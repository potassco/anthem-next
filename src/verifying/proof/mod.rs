pub mod vampire;

use {crate::verifying::problem::Problem, indexmap::{map::MutableKeys, IndexMap}, std::process::Output};

#[derive(Debug)]
pub struct Proof {
    pub problems: IndexMap<Problem, Status>,
}

impl Proof {
    pub fn of(problems: impl IntoIterator<Item = Problem>) -> Self {
        Proof {
            problems: problems.into_iter().map(|p| (p, Status::Open)).collect(),
        }
    }

    pub fn prove_with(mut self, prover: impl Prover) -> Self {
        todo!()
    }
}

pub trait Prover {
    fn prove(&self, problem: &Problem) -> Report;
}

#[derive(Debug)]
pub enum Status {
    Open,
    Running, // TODO: Store the thread
    Finished(Report),
}

#[derive(Debug)]
pub struct Report {
    // szs_status: SzsStatus,
    // raw: String,
    output: Output,
}

impl Report {
    pub fn from_output(output: Output) -> Self {
        Report { output }
    }

    // pub fn from_raw(raw: String) -> Self {
    //     todo!()
    // }

    // pub fn szs_status(&self) -> SzsStatus {
    //     self.szs_status
    // }

    // pub fn raw(&self) -> &str {
    //     self.raw.as_str()
    // }
}

// #[derive(Debug, Clone, Copy)]
// pub enum SzsStatus {
//     Success(Success),
//     NoSuccess(NoSuccess),
// }

// #[derive(Debug, Clone, Copy)]
// pub enum Success {
//     Theorem,
//     CounterSatisfiable,
//     ContradictoryAxioms,
// }

// #[derive(Debug, Clone, Copy)]
// pub enum NoSuccess {
//     TimeOut,
//     MemoryOut,
//     GaveUp,
//     UserTerminated,
//     Error,
// }
