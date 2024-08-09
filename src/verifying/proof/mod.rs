use crate::verifying::problem::Problem;

pub mod vampire;

pub trait Report {}

pub trait Prover {
    type Report: Report;
    type Error;

    fn prove(&self, problem: &Problem) -> Result<Self::Report, Self::Error>;

    fn prove_all<'a>(
        &self,
        problems: impl IntoIterator<Item = &'a Problem>,
    ) -> impl IntoIterator<Item = Result<Self::Report, Self::Error>> {
        problems.into_iter().map(|p| self.prove(p))
    }
}
