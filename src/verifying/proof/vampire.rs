use {crate::verifying::{problem::{Problem}, proof::{Prover, Outcome}}};

pub struct Vampire;

impl Prover for Vampire {
    fn prove(&self, problem: &Problem) -> Outcome {
        todo!()
    }
}
