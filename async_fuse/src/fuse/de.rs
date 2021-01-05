//! FUSE protocol deserializer

use super::abi_marker::FuseAbiData;

use std::ffi::OsStr;
use std::mem;
use std::os::unix::io::RawFd;
use std::slice;

use aligned_bytes::AlignedBytes;
use better_as::pointer;
use log::trace;
use memchr::memchr;
use nix::unistd;

/// FUSE protocol deserializer
#[derive(Debug)]
pub struct Deserializer {
    /// inner bytes
    bytes: AlignedBytes,
    /// offset to indicate the start point
    offset: usize,
    /// the number of bytes in the buffer
    size: usize,
}

/// The error returned by `Deserializer`
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub enum DeserializeError {
    /// Expected more data
    #[error("NotEnough")]
    NotEnough,

    /// The pointer's alignment mismatched with the type
    #[error("AlignMismatch")]
    AlignMismatch,

    /// Buffer is too small to hold all the data
    #[error("BufferTooSmall")]
    BufferTooSmall,

    /// Number overflow during decoding
    #[error("NumOverflow")]
    NumOverflow,

    /// The value of the target type is invalid
    #[allow(dead_code)]
    #[error("InvalidValue")]
    InvalidValue,

    #[error("InnerNixError")]
    InnerNixError(nix::Error),
}

/// checks pointer alignment, returns `AlignMismatch` if failed
#[inline]
fn check_align<T>(ptr: *const u8) -> Result<(), DeserializeError> {
    let addr = pointer::to_address(ptr);
    let align = mem::align_of::<T>();
    if addr.wrapping_rem(align) != 0 {
        trace!(
            "failed to convert bytes to type {}, \
                    pointer={:p} is not a multiple of alignment={}",
            std::any::type_name::<T>(),
            ptr,
            align,
        );
        return Err(DeserializeError::AlignMismatch);
    }
    Ok(())
}

/// checks whether there are enough bytes
#[inline]
fn check_size(len: usize, need: usize) -> Result<(), DeserializeError> {
    if len < need {
        trace!(
            "no enough bytes to fetch, remaining {} bytes but to fetch {} bytes",
            len,
            need,
        );
        return Err(DeserializeError::NotEnough);
    }
    Ok(())
}

macro_rules! get_buffer {
    ($name: ident, $get_fun: ident, $start: ident) => {
        /// Get the bytes slice starting from `$start`, containing all zero bytes
        macro_rules! $name {
            ($x:expr) => {
                match $x.bytes.$get_fun($x.$start..) {
                    Some(b) => b,
                    None => return Err(DeserializeError::BufferTooSmall),
                }
            };

            ($x:expr, $len:expr) => {
                match $x.bytes.$get_fun($x.$start..($x.$start + $len)) {
                    Some(b) => b,
                    None => return Err(DeserializeError::BufferTooSmall),
                }
            };
        }
    };
}

get_buffer!(get_buffer_from_end, get_mut, size);
get_buffer!(get_buffer_from_offset, get_mut, offset);

impl Deserializer {
    /// Create `Deserializer`
    pub const fn new(bytes: AlignedBytes) -> Deserializer {
        Self {
            bytes,
            offset: 0,
            size: 0,
        }
    }

    /// Only used in test
    pub const fn new_with_size(bytes: AlignedBytes, size: usize) -> Deserializer {
        Self {
            bytes,
            offset: 0,
            size,
        }
    }

    pub fn read(&mut self, fd: RawFd) -> Result<usize, DeserializeError> {
        unistd::read(fd, get_buffer_from_end!(self)).map(|size| {
            self.size += size;
            size
        }).map_err(|err| {
            DeserializeError::InnerNixError(err)
        })
    }

    /// pop some bytes without length check
    unsafe fn pop_bytes_unchecked(&mut self, len: usize) -> &[u8] {
        let bytes = self.bytes.get_unchecked(self.offset..(self.offset + len));
        self.offset += len;
        bytes
    }

    /// Get the length of the remaining bytes
    pub const fn remaining_len(&self) -> usize {
        self.size - self.offset
    }

    /// Fetch all remaining bytes
    pub fn fetch_all_bytes(&mut self) -> &[u8] {
        unsafe {
            let bytes = self.bytes.get_unchecked(self.offset..self.size);
            self.offset = self.size;
            bytes
        }
    }

    /// Fetch specified amount of bytes
    #[allow(dead_code)]
    pub fn fetch_bytes(&mut self, need: usize) -> Result<&[u8], DeserializeError> {
        check_size(self.remaining_len(), need)?;
        unsafe { Ok(self.pop_bytes_unchecked(need)) }
    }

    /// Fetch some bytes and transmute to `&T`
    pub fn fetch_ref<T: FuseAbiData + Sized>(&mut self) -> Result<&T, DeserializeError> {
        let ty_size: usize = mem::size_of::<T>();
        let ty_align: usize = mem::align_of::<T>();
        debug_assert!(ty_size > 0 && ty_size.wrapping_rem(ty_align) == 0);

        check_size(self.remaining_len(), ty_size)?;

        unsafe {
            check_align::<T>(self.bytes.as_ptr().add(self.offset))?;
            let bytes = self.pop_bytes_unchecked(ty_size);
            Ok(&*(bytes.as_ptr().cast()))
        }
    }

    /// Fetch a slice of target instances with the length `n`
    #[allow(dead_code)]
    pub fn fetch_slice<T: FuseAbiData + Sized>(
        &mut self,
        n: usize,
    ) -> Result<&[T], DeserializeError> {
        let ty_size: usize = mem::size_of::<T>();
        let ty_align: usize = mem::align_of::<T>();
        debug_assert!(ty_size > 0 && ty_size.wrapping_rem(ty_align) == 0);

        let (size, is_overflow) = ty_size.overflowing_mul(n);
        if is_overflow {
            trace!("number overflow: ty_size = {}, n = {}", ty_size, n);
            return Err(DeserializeError::NumOverflow);
        }

        check_size(self.remaining_len(), size)?;

        unsafe {
            let bytes = self.pop_bytes_unchecked(size);
            let base: *const T = bytes.as_ptr().cast();
            check_align::<T>(base.cast()).map_err(|err| {
                self.offset -= size;
                err
            })?;
            Ok(slice::from_raw_parts(base, n))
        }
    }

    /// Fetch remaining bytes and transmute to a slice of target instances
    pub fn fetch_all_as_slice<T: FuseAbiData + Sized>(&mut self) -> Result<&[T], DeserializeError> {
        let ty_size: usize = mem::size_of::<T>();
        let ty_align: usize = mem::align_of::<T>();
        debug_assert!(ty_size > 0 && ty_size.wrapping_rem(ty_align) == 0);

        let remaining_len = self.remaining_len();
        if remaining_len < ty_size || remaining_len.wrapping_rem(ty_size) != 0 {
            trace!(
                "no enough bytes to fetch, remaining {} bytes but to fetch (n * {}) bytes",
                self.bytes.len(),
                ty_size,
            );
            return Err(DeserializeError::NotEnough);
        }

        let bytes = self.fetch_all_bytes();
        check_align::<T>(bytes.as_ptr().cast())?;
        unsafe {
            let base: *const T = bytes.as_ptr().cast();
            let len = bytes.len().wrapping_div(ty_size);
            Ok(slice::from_raw_parts(base, len))
        }
    }

    /// Fetch some nul-terminated bytes.
    ///
    /// [`std::ffi::CStr::to_bytes`](https://doc.rust-lang.org/stable/std/ffi/struct.CStr.html#method.to_bytes)
    /// will take O(n) time in the future.
    ///
    /// `slice::len` is always O(1)
    pub fn fetch_c_str(&mut self) -> Result<&[u8], DeserializeError> {
        let remaining_len = self.remaining_len();
        let strlen: usize = memchr(0, get_buffer_from_offset!(self, remaining_len))
            .ok_or_else(|| {
                trace!("no trailing zero in bytes, cannot fetch c-string");
                DeserializeError::NotEnough
            })?
            .wrapping_add(1);
        debug_assert!(strlen <= remaining_len);
        unsafe { Ok(self.pop_bytes_unchecked(strlen)) }
    }

    /// Fetch some nul-terminated bytes and return an `OsStr` without the nul byte.
    pub fn fetch_os_str(&mut self) -> Result<&OsStr, DeserializeError> {
        use std::os::unix::ffi::OsStrExt;

        let bytes_with_nul = self.fetch_c_str()?;

        let bytes_without_nul: &[u8] = unsafe {
            let len = bytes_with_nul.len().wrapping_sub(1);
            bytes_with_nul.get_unchecked(..len)
        };

        Ok(OsStrExt::from_bytes(bytes_without_nul))
    }
}

#[cfg(test)]
mod tests {
    use super::DeserializeError;
    use super::super::util;

    #[test]
    fn fetch_all_bytes() {
        let mut de = util::init_de(8, 8);
        assert_eq!(de.fetch_all_bytes(), &[0; 8]);
        assert_eq!(de.remaining_len(), 0);
    }

    #[test]
    fn fetch_bytes() {
        let mut de = util::init_de(8,8);
        assert_eq!(
            de.fetch_bytes(5)
                .unwrap_or_else(|err| panic!("failed to fetch 5 bytes, the error is: {}", err,)),
            &[0; 5]
        );
        assert_eq!(de.remaining_len(), 3);

        assert!(de.fetch_bytes(5).is_err());
        assert_eq!(de.remaining_len(), 3);
    }

    #[test]
    fn fetch_ref() {
        // this buffer contains two `u32` or one `u64`
        // so it is aligned to 8 bytes
        let buf = [0, 1, 2, 3, 4, 5, 6, 7];

        {
            let mut de = util::init_de_with_value(&buf, 8);
            assert_eq!(
                de.fetch_ref::<u32>()
                    .unwrap_or_else(|err| panic!("failed to fetch u32, the error is: {}", err)),
                &u32::from_ne_bytes([0, 1, 2, 3])
            );
            assert_eq!(de.remaining_len(), 4);
        }

        {
            let mut de = util::init_de_with_value(&buf, 8);
            assert_eq!(
                de.fetch_ref::<u64>()
                    .unwrap_or_else(|err| panic!("failed to fetch u64, the error is: {}", err)),
                &u64::from_ne_bytes([0, 1, 2, 3, 4, 5, 6, 7])
            );
            assert_eq!(de.remaining_len(), 0);
        }
    }

    #[test]
    fn fetch_all_as_slice() {
        // this buffer contains two `u32`
        // so it can be aligned to 4 bytes
        // it is aligned to 8 bytes here
        let buf = [0, 1, 2, 3, 4, 5, 6, 7];

        {
            let mut de = util::init_de_with_value(&buf, 8);
            assert_eq!(
                de.fetch_all_as_slice::<u32>().unwrap_or_else(|err| panic!(
                    "failed to fetch all data and build slice of u32, the error is: {}",
                    err,
                )),
                &[
                    u32::from_ne_bytes([0, 1, 2, 3]),
                    u32::from_ne_bytes([4, 5, 6, 7]),
                ]
            );
            assert_eq!(de.remaining_len(), 0);
        }

        {
            let mut de = util::init_de_with_value(&buf, 8);
            assert!(de.fetch_bytes(3).is_ok());
            assert_eq!(
                de.fetch_all_as_slice::<u32>().unwrap_err(),
                DeserializeError::NotEnough
            );
            assert_eq!(de.remaining_len(), 5)
        }
    }

    #[test]
    fn fetch_c_str() {
        let buf: [u8; 12] = *b"hello\0world\0";

        let mut de = util::init_de_with_value(&buf, 8);
        assert_eq!(
            de.fetch_c_str()
                .unwrap_or_else(|err| panic!("failed to fetch C-String, the error is: {}", err)),
            b"hello\0".as_ref()
        );
        assert_eq!(
            de.fetch_c_str()
                .unwrap_or_else(|err| panic!("failed to fetch C-String, the error is: {}", err)),
            b"world\0".as_ref()
        );
        assert_eq!(de.remaining_len(), 0);
    }
}
