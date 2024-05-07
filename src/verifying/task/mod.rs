pub mod external_equivalence;
pub mod strong_equivalence;

use {
    crate::{
        convenience::unbox::{fol::UnboxedFormula, Unbox as _},
        syntax_tree::fol,
        verifying::problem::Problem,
    },
    indexmap::IndexSet,
    thiserror::Error,
};

pub trait Task {
    type Error;
    fn decompose(self) -> Result<Vec<Problem>, Self::Error>;
}

#[derive(Error, Debug, PartialEq)]
pub enum ProofOutlineError {
    #[error("the definition `{0}` contains duplicated variables in outermost quantification")]
    DuplicatedVariables(fol::Formula),
    #[error("predicate `{0}` is taken - definitions require fresh predicates")]
    TakenPredicate(fol::Predicate),
    #[error("the definition `{0}` contains free variables in the RHS")]
    FreeRhsVariables(fol::Formula),
    #[error("undefined predicate - {predicate:?} occurs for the first time in the RHS of definition {definition:?}")]
    UndefinedRhsPredicate {
        definition: fol::Formula,
        predicate: fol::Predicate,
    },
    #[error("there was an issue with formula `{0}` in the proof outline")]
    Basic(fol::Formula),
}

#[derive(Debug, PartialEq)]
pub struct ProofOutline {
    pub forward_definitions: Vec<fol::AnnotatedFormula>,
    pub forward_basic_lemmas: Vec<fol::AnnotatedFormula>,
    //pub forward_inductive_lemmas: <fol::AnnotatedFormula>,
    pub backward_definitions: Vec<fol::AnnotatedFormula>,
    pub backward_basic_lemmas: Vec<fol::AnnotatedFormula>,
    //pub backward_inductive_lemmas: Vec<fol::AnnotatedFormula>,
}

impl ProofOutline {
    fn construct(
        spec: fol::Specification,
        mut taken_predicates: IndexSet<fol::Predicate>,
    ) -> Result<Self, ProofOutlineError> {
        let mut forward_definitions: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut backward_definitions: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut forward_basic_lemmas: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut backward_basic_lemmas: Vec<fol::AnnotatedFormula> = Vec::new();
        // process a specification, line by line, adding each definition's predicate to the
        // list of taken predicates before the next iteration
        for anf in spec.formulas.iter() {
            match anf.role {
                fol::Role::Definition => {
                    let predicate = anf.formula.clone().definition(&taken_predicates)?;
                    taken_predicates.insert(predicate);
                    match anf.direction {
                        fol::Direction::Forward => {
                            forward_definitions.push(anf.clone());
                            //forward_definitions.push(AnnotatedFormula::from((anf.clone(), Role::Axiom)));
                        }
                        fol::Direction::Backward => {
                            backward_definitions.push(anf.clone());
                        }
                        fol::Direction::Universal => {
                            let f = anf.clone();
                            forward_definitions.push(f.clone());
                            backward_definitions.push(f);
                        }
                    }
                }
                fol::Role::Lemma => match anf.direction {
                    fol::Direction::Forward => {
                        forward_basic_lemmas.push(anf.clone());
                        //forward_definitions.push(AnnotatedFormula::from((anf.clone(), Role::Axiom)));
                    }
                    fol::Direction::Backward => {
                        backward_basic_lemmas.push(anf.clone());
                    }
                    fol::Direction::Universal => {
                        let f = anf.clone();
                        forward_basic_lemmas.push(f.clone());
                        backward_basic_lemmas.push(f);
                    }
                },
                fol::Role::Assumption | fol::Role::Spec => {
                    return Err(ProofOutlineError::Basic(anf.formula.clone()));
                }
            }
        }
        Ok(ProofOutline {
            forward_definitions,
            forward_basic_lemmas,
            backward_definitions,
            backward_basic_lemmas,
        })
    }
}

trait CheckDefinition {
    // Returns the predicate defined in the LHS of the formula if it is a valid definition, else returns an error
    fn definition(
        self,
        taken_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<fol::Predicate, ProofOutlineError>;
}

impl CheckDefinition for fol::Formula {
    fn definition(
        self,
        taken_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<fol::Predicate, ProofOutlineError> {
        let original = self.clone();
        match self.unbox() {
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    fol::Quantification {
                        quantifier: fol::Quantifier::Forall,
                        variables,
                    },
                formula:
                    fol::Formula::BinaryFormula {
                        connective: fol::BinaryConnective::Equivalence,
                        lhs,
                        rhs,
                    },
            } => {
                match lhs.unbox() {
                    UnboxedFormula::AtomicFormula(fol::AtomicFormula::Atom(a)) => {
                        // check variables has no duplicates
                        let uniques: IndexSet<fol::Variable> =
                            IndexSet::from_iter(variables.clone());
                        if uniques.len() < variables.len() {
                            return Err(ProofOutlineError::DuplicatedVariables(original));
                        }

                        // check predicate is totally fresh
                        let predicate = a.predicate();
                        if taken_predicates.contains(&predicate) {
                            return Err(ProofOutlineError::TakenPredicate(predicate));
                        }

                        // check RHS has no free variables other than those in uniques
                        if rhs.free_variables().difference(&uniques).count() > 0 {
                            return Err(ProofOutlineError::FreeRhsVariables(original));
                        }
                        if uniques.difference(&rhs.free_variables()).count() > 0 {
                            println!("Warning: The universally quantified list of vars contains members which do not occur in RHS.");
                        }

                        // check RHS has no predicates other than taken predicates
                        // this should ensure no recursion through definition sequence
                        if let Some(predicate) =
                            rhs.predicates().difference(taken_predicates).next()
                        {
                            return Err(ProofOutlineError::UndefinedRhsPredicate {
                                definition: original,
                                predicate: predicate.clone(),
                            });
                        }

                        Ok(predicate)
                    }
                    _ => Err(ProofOutlineError::Basic(original)),
                }
            }
            _ => Err(ProofOutlineError::Basic(original)),
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{ProofOutline, ProofOutlineError},
        crate::{syntax_tree::fol, verifying::task::CheckDefinition},
        frame_support::assert_err,
        indexmap::IndexSet,
    };

    #[test]
    fn check_correct_definition() {
        for (src, target) in [
            (
                "forall X ( p(X) <-> 1 < 2 )",
                fol::Predicate {
                    symbol: "p".to_string(),
                    arity: 1,
                },
            ),
            (
                "forall X Y$i ( pred(X, Y$i) <-> exists N$i (X = N$i and t(X) or t(Y$i)) )",
                fol::Predicate {
                    symbol: "pred".to_string(),
                    arity: 2,
                },
            ),
        ] {
            let taken_predicates: IndexSet<fol::Predicate> =
                IndexSet::from_iter(vec![fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }]);
            let formula: fol::Formula = src.parse().unwrap();
            assert_eq!(formula.definition(&taken_predicates).unwrap(), target)
        }
    }

    #[test]
    fn check_incorrect_definition() {
        for (src, target) in [
            (
                "forall X Y X ( p(X) <-> 1 < 2 )",
                ProofOutlineError::DuplicatedVariables(
                    "forall X Y X ( p(X) <-> 1 < 2 )".parse().unwrap(),
                ),
            ),
            (
                "forall X ( t(X) <-> 1 < 2 )",
                ProofOutlineError::TakenPredicate(fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }),
            ),
            (
                "forall Z1 Z2 ( ancestor(Z1, Z2) <-> t(X) and t(Z2) )",
                ProofOutlineError::FreeRhsVariables(
                    "forall Z1 Z2 ( ancestor(Z1, Z2) <-> t(X) and t(Z2) )"
                        .parse()
                        .unwrap(),
                ),
            ),
            (
                "forall Z1 Z2 ( ancestor(Z1, Z2) <-> ancestor(Z1, Z2) )",
                ProofOutlineError::UndefinedRhsPredicate {
                    definition: "forall Z1 Z2 ( ancestor(Z1, Z2) <-> ancestor(Z1, Z2) )"
                        .parse()
                        .unwrap(),
                    predicate: fol::Predicate {
                        symbol: "ancestor".to_string(),
                        arity: 2,
                    },
                },
            ),
        ] {
            let taken_predicates: IndexSet<fol::Predicate> =
                IndexSet::from_iter(vec![fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }]);
            let formula: fol::Formula = src.parse().unwrap();
            assert_err!(formula.definition(&taken_predicates), target)
        }
    }

    #[test]
    fn test_proof_outline_constructor() {
        let f1: fol::AnnotatedFormula =
            "definition[p]: forall X (p(X) <-> exists Y$i (X = Y$i and 0 <= Y$i <= 10))"
                .parse()
                .unwrap();
        let f2: fol::AnnotatedFormula = "lemma(backward)[l1]: exists X (X = n$i)".parse().unwrap();
        let f3: fol::AnnotatedFormula = "definition(forward)[q]: forall X (q(X) <-> p(X) or t(X))"
            .parse()
            .unwrap();
        let f4: fol::AnnotatedFormula = "lemma[l2]: n$i > 0".parse().unwrap();
        let spec = fol::Specification {
            formulas: vec![f1.clone(), f2.clone(), f3.clone(), f4.clone()],
        };
        let taken_predicates: IndexSet<fol::Predicate> =
            IndexSet::from_iter(vec![fol::Predicate {
                symbol: "t".to_string(),
                arity: 1,
            }]);
        let proof_outline = ProofOutline::construct(spec, taken_predicates).unwrap();
        let target = ProofOutline {
            forward_definitions: vec![f1.clone(), f3],
            forward_basic_lemmas: vec![f4.clone()],
            backward_definitions: vec![f1],
            backward_basic_lemmas: vec![f2, f4],
        };
        assert_eq!(proof_outline, target)
    }
}
