use {
    crate::{
        command_line::Decomposition,
        syntax_tree::{asp, fol},
        verifying::{
            problem::Problem,
            task::{ProofOutline, Task},
        },
    },
    either::Either,
    indexmap::IndexSet,
    std::fmt::Display,
    thiserror::Error,
};

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

#[derive(Error, Debug)]
pub enum ExternalEquivalenceTaskError {
    InputOutputPredicatesOverlap(Vec<fol::Predicate>),
    InputPredicateInRuleHead(Vec<fol::Predicate>),
}

impl Display for ExternalEquivalenceTaskError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExternalEquivalenceTaskError::InputOutputPredicatesOverlap(predicates) => {
                write!(
                    f,
                    "the following predicates are declared as input and output predicates: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
            ExternalEquivalenceTaskError::InputPredicateInRuleHead(predicates) => {
                write!(
                    f,
                    "the following predicates are declared as input and output predicates: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
        }
    }
}

impl ExternalEquivalenceTask {
    fn ensure_input_and_output_predicates_are_disjoint(
        &self,
    ) -> Result<(), ExternalEquivalenceTaskError> {
        let input_predicates = self.user_guide.input_predicates();
        let output_predicates = self.user_guide.output_predicates();

        let intersection: Vec<_> = input_predicates
            .intersection(&output_predicates)
            .cloned()
            .collect();

        if intersection.is_empty() {
            Ok(())
        } else {
            Err(ExternalEquivalenceTaskError::InputOutputPredicatesOverlap(
                intersection,
            ))
        }
    }

    fn ensure_program_heads_do_not_contain_input_predicates(
        &self,
    ) -> Result<(), ExternalEquivalenceTaskError> {
        let input_predicates = self.user_guide.input_predicates();
        let head_predicates: IndexSet<_> = self
            .program
            .head_predicates()
            .into_iter()
            .map(fol::Predicate::from)
            .collect();

        let intersection: Vec<_> = input_predicates
            .intersection(&head_predicates)
            .cloned()
            .collect();

        if intersection.is_empty() {
            Ok(())
        } else {
            Err(ExternalEquivalenceTaskError::InputPredicateInRuleHead(
                intersection,
            ))
        }
    }
}

impl Task for ExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;

    fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
        self.ensure_input_and_output_predicates_are_disjoint()?;
        self.ensure_program_heads_do_not_contain_input_predicates()?;

        let taken_predicates = self.user_guide.input_predicates();
        let _proof_outline = ProofOutline::construct(self.proof_outline, taken_predicates);
        // TODO: Add more error handing

        todo!()
    }
}
