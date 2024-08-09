use crate::verifying::problem::Problem;

pub mod vampire;

pub trait Report {}

pub trait Prover {
    type Report: Report;
    type Error;

    fn prove(&self, problem: &Problem) -> Result<Self::Report, Self::Error>;
}
