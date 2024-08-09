use {
    crate::verifying::{
        problem::Problem,
        proof::{Outcome, Prover, Status},
    },
    std::{
        fmt::Display,
        io::Write as _,
        process::{Command, Stdio},
    },
};

#[derive(Debug, Clone)]
pub enum VampireOutcome {
    UnableToSpawn,
    UnableToOpenStdin,
    UnableToWriteToStdin,
    UnableToWait,
    SuccessfulExecution
}

impl Outcome for VampireOutcome {
    fn status(&self) -> Option<Status> {
        todo!()
    }
}

impl Display for VampireOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

pub struct Vampire;

impl Prover for Vampire {
    type Outcome = VampireOutcome;

    fn prove(&self, problem: &Problem) -> VampireOutcome {
        let mut child = Command::new("vampire")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(); // TODO: Proper error handling

        let stdin = child.stdin.as_mut().unwrap(); // TODO: Proper error handling
        write!(stdin, "{problem}").unwrap(); // TODO: Proper error handling

        let output = child.wait_with_output().unwrap(); // TODO: Proper error handling

        todo!()
    }
}
