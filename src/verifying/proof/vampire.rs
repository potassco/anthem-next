use {
    crate::verifying::problem::Problem,
    std::{
        io::Write as _,
        process::{Command, Output, Stdio},
    },
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum VampireError {
    #[error("unable to spawn vampire as a child process")]
    UnableToSpawn(#[source] std::io::Error),
    #[error("unable to write to vampire's stdin")]
    UnableToWrite(#[source] std::io::Error),
    #[error("unable to wait for vampire")]
    UnableToWait(#[source] std::io::Error),
}

pub struct VampireReport {
    pub output: Output,
}

pub struct Vampire;

impl Vampire {
    pub fn prove(&self, problem: Problem) -> Result<VampireReport, VampireError> {
        let mut child = Command::new("vampire")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(VampireError::UnableToSpawn)?;

        let mut stdin = child.stdin.take().unwrap();
        write!(stdin, "{problem}").map_err(VampireError::UnableToWrite)?;
        drop(stdin);

        let output = child
            .wait_with_output()
            .map_err(VampireError::UnableToWait)?;

        Ok(VampireReport { output })
    }
}
