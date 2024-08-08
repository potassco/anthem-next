use {crate::verifying::{
    problem::Problem,
    proof::{Prover, Report},
},
std::{
    io::Write,
    process::{Command, Stdio},
}
};

pub struct Vampire;

impl Prover for Vampire {
    fn prove(problem: &Problem) -> Report {
        let mut child = Command::new("vampire")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap(); // TODO: Proper error handling

        let stdin = child.stdin.as_mut().unwrap(); // TODO: Proper error handling
        write!(stdin, "{problem}").unwrap(); // TODO: Proper error handling

        let output = child.wait_with_output().unwrap(); // TODO: Proper error handling

        Report::from_output(output)
    }
}
