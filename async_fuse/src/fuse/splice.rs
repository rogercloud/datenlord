use anyhow;
use nix::{unistd, errno::Errno};
use std::os::unix::io::RawFd;

#[derive(Debug)]
pub struct Pipe(pub RawFd, pub RawFd);

impl Drop for Pipe {
    fn drop(&mut self) {
        if let Err(_) = unistd::close(self.0) {
            panic!("Error to close the pipe[0]: {}", self.0);
        }

        if let Err(_) = unistd::close(self.1) {
            panic!("Error to close the pipe[1]: {}", self.1);
        }
    }
}

impl Pipe {
    pub fn new() -> anyhow::Result<Self> {
        match unistd::pipe() {
            Ok((infd, outfd)) => Ok(Self(infd, outfd)),
            Err(_) => Err(anyhow::anyhow!(
                "create Pipe failed: {}",
                Errno::last().desc()
            )),
        }
    }
}
