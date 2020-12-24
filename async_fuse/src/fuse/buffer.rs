use super::splice;
use aligned_bytes::AlignedBytes;
use libc;
use nix::{self, fcntl, unistd};
use std::os::unix::io::RawFd;
use utilities::Cast;

/// The max size of write requests from the kernel. The absolute minimum is 4k,
/// FUSE recommends at least 128k, max 16M. The FUSE default is  128k on Linux.
const MAX_WRITE_SIZE: u32 = 128 * 1024;

/// Size of the buffer for reading a request from the kernel. Since the kernel may send
/// up to `MAX_WRITE_SIZE` bytes in a write request, we use that value plus some extra space.
const BUFFER_SIZE: u32 = MAX_WRITE_SIZE + 512;

/// We use `PAGE_SIZE` (4 KiB) as the alignment of the buffer.
const PAGE_SIZE: usize = 4096;

/// This buffer is the combine of regular aligned buffers and pipes
#[derive(Debug)]
pub struct UnionBuffer {
    /// The buffer to store regular read/write data
    byte: AlignedBytes,

    /// The pipes for splice read/write
    pipe: splice::Pipe,

    /// flag to tell if it's using pipe or bytebuffer
    is_pipe: bool,
}

/// The error returned by `UnionBuffer`
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum BufferError {
    /// Expect more data
    #[error("NotEnough")]
    NotEnough,

    /// Nix error
    #[error("NixInternal")]
    NixInternal(nix::Error),
}

impl UnionBuffer {
    /// Constructor to create a UnionBuffer instance
    pub fn new(is_pipe: bool) -> Self {
        Self {
            byte: AlignedBytes::new_zeroed(BUFFER_SIZE.cast(), PAGE_SIZE),
            pipe: splice::Pipe::new()
                .unwrap_or_else(|err| panic!("failed to fetch u32, the error is: {}", err)),
            is_pipe,
        }
    }

    pub fn read(&mut self, fd: RawFd) -> Result<usize, BufferError> {
        let result = if self.is_pipe {
            fcntl::splice(
                fd,
                None,
                self.pipe.1,
                None,
                BUFFER_SIZE.cast(),
                fcntl::SpliceFFlags::empty(),
            )
        } else {
            unistd::read(fd, &mut *(self.byte))
        };

        match result {
            Ok(read_size) => Ok(read_size),
            Err(err) => Err(BufferError::NixInternal(err)),
        }
    }

    pub fn consume(&mut self, size: usize) -> Result<Vec<u8>, BufferError> {
        if self.is_pipe {
            let buffer = Vec::with_capacity(size);
            let read_size = match unistd::read(self.pipe.0, buffer.as_mut_slice()) {
                Ok(s) => s,
                Err(err) => return Err(BufferError::NixInternal(err)),
            };
            if read_size < size {
                Err(BufferError::NotEnough)
            } else {
                Ok(buffer)
            }
        } else {
            match self.byte.get(..size) {
                Some(b) => Ok(b.to_vec()),
                None => Err(BufferError::NotEnough),
            }
        }
    }

    pub fn len(&self) -> usize {
        if self.is_pipe {
            let mut pipe_left: usize = 0;
            unsafe {
                let ptr: *mut usize = &mut pipe_left;
                let ret = libc::ioctl(self.pipe.0, libc::FIONREAD, ptr);
                if ret < 0 {
                    panic!("iotcl FIONREAD on pipe failed, return fvalue is {}", ret)
                }
            }
            pipe_left
        } else {
            self.byte.len()
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
