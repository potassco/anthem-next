use {
    crate::{
        command_line::Decomposition,
        syntax_tree::{asp, fol},
        verifying::{
            problem::{self, Problem},
            task::Task,
        },
    },
    either::Either,
    thiserror::Error,
};

struct ProofOutline {
    pub forward_basic_lemmas: Vec<fol::AnnotatedFormula>,
    pub backward_basic_lemmas: Vec<fol::AnnotatedFormula>,
}

#[derive(Error, Debug)]
pub enum ExternalEquivalenceTaskError {}

#[derive(Debug)]
pub struct ExternalEquivalenceTask {
    pub specification: Either<asp::Program, fol::Specification>,
    pub program: asp::Program,
    pub user_guide: fol::UserGuide,
    pub proof_outline: fol::Specification,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl Task for ExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;

    fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
        // let task: ValidatedExternalEquivalenceTask = todo!();
        // task.decompose()
        todo!()
    }
}

// struct ValidatedExternalEquivalenceTask {
//     pub left: Vec<fol::AnnotatedFormula>,
//     pub right: Vec<fol::AnnotatedFormula>,
//     pub user_guide_assumptions: Vec<fol::AnnotatedFormula>,
//     pub proof_outline: ProofOutline,
//     pub decomposition: Decomposition,
//     pub direction: fol::Direction,
//     pub break_equivalences: bool,
// }

// impl Task for ValidatedExternalEquivalenceTask {
//     type Error = ExternalEquivalenceTaskError;

//     fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
//         // let task: AssembledExternalEquivalenceTask = todo!();
//         // task.decompose()
//         todo!()
//     }
// }

struct AssembledExternalEquivalenceTask {
    pub stable_premises: Vec<problem::AnnotatedFormula>,
    pub forward_premises: Vec<problem::AnnotatedFormula>,
    pub forward_conclusions: Vec<problem::AnnotatedFormula>,
    pub backward_premises: Vec<problem::AnnotatedFormula>,
    pub backward_conclusions: Vec<problem::AnnotatedFormula>,
    pub proof_outline: ProofOutline,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
}

impl Task for AssembledExternalEquivalenceTask {
    type Error = ExternalEquivalenceTask;

    fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            let mut forward_sequence = Problem::from_components(
                "forward".to_string(),
                self.stable_premises.clone(),
                self.forward_premises,
                self.forward_conclusions,
                self.proof_outline.forward_basic_lemmas,
            );
            problems.append(&mut forward_sequence);
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            let mut backward_sequence = Problem::from_components(
                "backward".to_string(),
                self.stable_premises,
                self.backward_premises,
                self.backward_conclusions,
                self.proof_outline.backward_basic_lemmas,
            );
            problems.append(&mut backward_sequence);
        }

        let result: Vec<Problem> = problems
            .into_iter()
            .flat_map(|p: Problem| match self.decomposition {
                Decomposition::Independent => p.decompose_independent(),
                Decomposition::Sequential => p.decompose_sequential(),
            })
            .collect();

        Ok(result)
    }
}
