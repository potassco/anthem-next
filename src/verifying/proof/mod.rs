use {
    crate::verifying::problem::Problem,
    indexmap::IndexMap,
    std::fmt::{Debug, Display},
};

pub mod vampire;

pub enum Status {
    // TODO: SZS status ontology
}

pub trait Outcome: Display + Debug + Clone {
    fn status(&self) -> Option<Status>;
}

pub trait Prover {
    type Outcome: Outcome;
    fn prove(&self, problem: &Problem) -> Self::Outcome;
}

pub struct Report<O: Outcome> {
    pub problems: IndexMap<Problem, O>,
}

impl<O: Outcome> Report<O> {
    pub fn generate_from(
        problems: impl IntoIterator<Item = Problem>,
        prover: impl Prover<Outcome = O>,
        // threads: usize,
    ) -> Self {
        Report {
            problems: problems
                .into_iter()
                .map(|problem| {
                    let outcome = prover.prove(&problem);
                    (problem, outcome)
                })
                .collect(),
        }
    }
}
