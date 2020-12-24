use super::splice;
use aligned_bytes::AlignedBytes;
use memchr::memchr;
use nix::{self, fcntl, unistd};
use std::os::unix::io::RawFd;
use utilities::Cast;
use super::fuse_request::Request;

/// The max size of write requests from the kernel. The absolute minimum is 4k,
/// FUSE recommends at least 128k, max 16M. The FUSE default is  128k on Linux.
const MAX_WRITE_SIZE: u32 = 128 * 1024;

/// Size of the buffer for reading a request from the kernel. Since the kernel may send
/// up to `MAX_WRITE_SIZE` bytes in a write request, we use that value plus some extra space.
const BUFFER_SIZE: u32 = MAX_WRITE_SIZE + 512;

/// We use `PAGE_SIZE` (4 KiB) as the alignment of the buffer.
const PAGE_SIZE: usize = 4096;

/// This buffer is the combine of regular aligned buffer and pipes.
/// If we consume the pipes data (not writing), the data is copied to the
/// memory buffer too.
#[derive(Debug)]
pub struct UnionBuffer {
    /// The byte buffer to store regular read/write data
    bytes: AlignedBytes,

    /// The pipes for splice read/write
    pipe: splice::Pipe,

    /// The union buffer offset, marking start point of data,
    /// will increase after `consume`
    offset: usize,

    /// The bytes buffer offset, marking start point of data,
    /// will increase after inserting into byte buffer, may be caused by
    /// `read` and `consume`.
    bytes_end: usize,

    /// The total data size we've got from fd, which will increase after `read`.
    size: usize,

    /// flag to tell if it's using pipe or bytebuffer
    is_pipe: bool,
}

unsafe impl Send for UnionBuffer {}
unsafe impl Sync for UnionBuffer {}

/// The error returned by `UnionBuffer`
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum BufferError {
    /// Expect more data
    #[error("NotEnough")]
    NotEnough,

    /// Buffer is not large enough to hold the pipe read data
    #[error("BufferNotLargeEnough")]
    BufferNotLargeEnough,

    /// Nix error
    #[error("NixInternal")]
    NixInternal(nix::Error),
}

/// Get the buffer starting from `bytes_end`
macro_rules! get_local_buffer {
    ($x:expr) => {
        match $x.bytes.get_mut($x.bytes_end..) {
            Some(b) => b,
            None => return Err(BufferError::BufferNotLargeEnough),
        }
    };
}

impl UnionBuffer {
    /// Constructor to create a UnionBuffer instance
    pub fn new(is_pipe: bool) -> Self {
        Self {
            bytes: AlignedBytes::new_zeroed(BUFFER_SIZE.cast(), PAGE_SIZE),
            pipe: splice::Pipe::new()
                .unwrap_or_else(|err| panic!("failed to fetch u32, the error is: {}", err)),
            is_pipe,
            offset: 0,
            bytes_end: 0,
            size: 0,
        }
    }

    /// Read data from `fd` into this buffer, and set buffer size
    pub fn read(&mut self, fd: RawFd) -> Result<usize, BufferError> {
        let read_ret = if self.is_pipe {
            fcntl::splice(
                fd,
                None,
                self.pipe.1,
                None,
                BUFFER_SIZE.cast(),
                fcntl::SpliceFFlags::empty(),
            )
        } else {
            unistd::read(fd, get_local_buffer!(self))
        };

        // Fallback if splice failed
        let read_ret = if let Err(_) = read_ret {
            if self.is_pipe {
                let tmp = unistd::read(fd, get_local_buffer!(self));
                if let Ok(_) = tmp {
                    self.is_pipe = false;
                }
                tmp
            } else {
                read_ret
            }
        } else {
            read_ret
        };

        match read_ret {
            Ok(size) => {
                if !self.is_pipe {
                    self.bytes_end += size;
                }
                self.size += size;
                Ok(size)
            }
            Err(err) => Err(BufferError::NixInternal(err)),
        }
    }

    /// Read u8 vec from this buffer, usually it's zero-copied.
    /// It assumes `size` bytes should be read, if it's not enough, return BufferError::NotEnough error.
    pub fn consume(&mut self, wanted: usize) -> Result<&[u8], BufferError> {
        if self.is_pipe {
            let buffer = get_local_buffer!(self);
            let read_size = match unistd::read(self.pipe.0, buffer) {
                Ok(s) => s,
                Err(err) => return Err(BufferError::NixInternal(err)),
            };

            if read_size < wanted {
                Err(BufferError::NotEnough)
            } else {
                self.bytes_end += wanted;
                self.offset += wanted;
                Ok(buffer)
            }
        } else {
            match self.bytes.get(self.offset..(self.offset + wanted)) {
                Some(b) => {
                    self.offset += wanted;
                    Ok(b)
                }
                None => Err(BufferError::NotEnough),
            }
        }
    }

    /// Consume all data left in this buffer
    pub fn consume_all(&mut self) -> Result<&[u8], BufferError> {
        self.consume(self.len())
    }

    /// Find char in the buffer. If it's a pipe, read pipe content to internal buffer first.
    pub fn memchr(&mut self, needle: u8) -> Option<usize> {
        if self.is_pipe {
            let available = self.len();
            match self.consume(available) {
                Ok(_) => {
                    // It's a fake consume, move data from pipe to bytes buffer
                    self.offset -= available;
                }
                Err(err) => panic!("Read pipe content to internal buffer failed"),
            }
            self.is_pipe = false;
        }

        return memchr(
            needle,
            self.bytes.get(self.offset..).expect("No data to search"),
        );
    }

    /// Get the remaining byte count without reading
    pub const fn len(&self) -> usize {
        self.size - self.offset
    }

    /// Tell if the buffer is empty
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub const fn is_pipe(&self) -> bool {
        self.is_pipe
    }
}

pub enum WrapBufferError {
}

pub fn wrap_buffer_from_req<'a, T>(
    req: &'a mut Request<'a>,
    origin: nix::Result<T>,
) -> nix::Result<(UnionBuffer, T)> {
    wrap_buffer(req.pop_buffer(), origin)
}

pub fn wrap_buffer<'a, T>(
    buffer: UnionBuffer,
    origin: nix::Result<T>,
) -> nix::Result<(UnionBuffer, T)> {
    match origin {
        Ok(o) => Ok((buffer, o)),
        Err(err) => Err(err),
    }
}
