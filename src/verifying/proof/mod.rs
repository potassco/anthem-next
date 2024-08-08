use {crate::verifying::problem::Problem, indexmap::IndexMap};

pub mod vampire;

pub struct Outcome;

pub trait Prover {
    fn prove(&self, problem: &Problem) -> Outcome;
}

pub struct Report {
    pub problems: IndexMap<Problem, Outcome>,
}

impl Report {
    pub fn generate_from(
        problems: impl IntoIterator<Item = Problem>,
        prover: impl Prover,
        // threads: usize,
    ) -> Self {
        Report {
            problems: problems.into_iter().map(|problem| {
                let outcome = prover.prove(&problem);
                (problem, outcome)
            }).collect()
        }
    }
}
