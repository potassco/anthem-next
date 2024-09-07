use crate::{
    convenience::{
        apply::Apply as _,
        unbox::{fol::UnboxedFormula, Unbox as _},
    },
    syntax_tree::fol::{AtomicFormula, BinaryConnective, Formula, Quantification, Theory},
};

pub fn simplify(theory: Theory) -> Theory {
    Theory {
        formulas: theory.formulas.into_iter().map(simplify_formula).collect(),
    }
}

pub fn simplify_formula(formula: Formula) -> Formula {
    formula.apply_all(&mut vec![
        Box::new(remove_identities),
        Box::new(remove_annihilations),
        Box::new(remove_idempotences),
        Box::new(join_nested_quantifiers),
        Box::new(extend_quantifier_scope),
    ])
}

pub fn remove_identities(formula: Formula) -> Formula {
    // Remove identities
    // e.g. F op E => F

    match formula.unbox() {
        // F and #true => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Truth),
        } => lhs,

        // #true and F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Truth),
            rhs,
        } => rhs,

        // F or #false => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Falsity),
        } => lhs,

        // #false or F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs,
        } => rhs,

        x => x.rebox(),
    }
}

pub fn remove_annihilations(formula: Formula) -> Formula {
    // Remove annihilations
    // e.g. F op E => E

    match formula.unbox() {
        // F or #true => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Truth),
        } => rhs,

        // #true or F => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Truth),
            rhs: _,
        } => lhs,

        // F and #false => false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
        } => rhs,

        // #false and F => #false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs: _,
        } => lhs,

        x => x.rebox(),
    }
}

pub fn remove_idempotences(formula: Formula) -> Formula {
    // Remove idempotences
    // e.g. F op F => F

    match formula.unbox() {
        // F and F => F
        // F or  F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction | BinaryConnective::Disjunction,
            lhs,
            rhs,
        } if lhs == rhs => lhs,

        x => x.rebox(),
    }
}

pub fn join_nested_quantifiers(formula: Formula) -> Formula {
    // Remove nested quantifiers
    // e.g. q X ( q Y F(X,Y) ) => q X Y F(X,Y)

    match formula.unbox() {
        // forall X ( forall Y F(X,Y) ) => forall X Y F(X,Y)
        // exists X ( exists Y F(X,Y) ) => exists X Y F(X,Y)
        UnboxedFormula::QuantifiedFormula {
            quantification: outer_quantification,
            formula:
                Formula::QuantifiedFormula {
                    quantification: mut inner_quantification,
                    formula: inner_formula,
                },
        } if outer_quantification.quantifier == inner_quantification.quantifier => {
            let mut variables = outer_quantification.variables;
            variables.append(&mut inner_quantification.variables);
            variables.sort();
            variables.dedup();

            inner_formula.quantify(outer_quantification.quantifier, variables)
        }
        x => x.rebox(),
    }
}

pub fn extend_quantifier_scope(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Bring a conjunctive or disjunctive term into the scope of a quantifer
        // e.g. exists X ( F(X) ) & G => exists X ( F(X) & G )
        // where X does not occur free in G
        UnboxedFormula::BinaryFormula {
            connective,
            lhs:
                Formula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier,
                            variables,
                        },
                    formula: f,
                },
            rhs,
        } => match connective {
            BinaryConnective::Conjunction | BinaryConnective::Disjunction => {
                let mut collision = false;
                for var in variables.iter() {
                    if rhs.free_variables().contains(var) {
                        collision = true;
                        break;
                    }
                }

                match collision {
                    true => formula,
                    false => Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier,
                            variables,
                        },
                        formula: Formula::BinaryFormula {
                            connective,
                            lhs: f,
                            rhs: rhs.into(),
                        }
                        .into(),
                    },
                }
            }
            _ => formula,
        },

        UnboxedFormula::BinaryFormula {
            connective,
            lhs,
            rhs:
                Formula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier,
                            variables,
                        },
                    formula: f,
                },
        } => match connective {
            BinaryConnective::Conjunction | BinaryConnective::Disjunction => {
                let mut collision = false;
                for var in variables.iter() {
                    if lhs.free_variables().contains(var) {
                        collision = true;
                        break;
                    }
                }

                match collision {
                    true => formula,
                    false => Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier,
                            variables,
                        },
                        formula: Formula::BinaryFormula {
                            connective,
                            lhs: lhs.into(),
                            rhs: f,
                        }
                        .into(),
                    },
                }
            }
            _ => formula,
        },

        x => x.rebox(),
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{
            extend_quantifier_scope, join_nested_quantifiers, remove_annihilations,
            remove_idempotences, remove_identities, simplify_formula,
        },
        crate::{convenience::apply::Apply as _, syntax_tree::fol::Formula},
    };

    #[test]
    fn test_simplify() {
        for (src, target) in [
            ("#true and #true and a", "a"),
            ("#true and (#true and a)", "a"),
        ] {
            assert_eq!(
                simplify_formula(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_remove_identities() {
        for (src, target) in [
            ("#true and a", "a"),
            ("a and #true", "a"),
            ("#false or a", "a"),
            ("a or #false", "a"),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut remove_identities),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_remove_annihilations() {
        for (src, target) in [
            ("#true or a", "#true"),
            ("a or #true", "#true"),
            ("#false and a", "#false"),
            ("a and #false", "#false"),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut remove_annihilations),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_remove_idempotences() {
        for (src, target) in [("a and a", "a"), ("a or a", "a")] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut remove_idempotences),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_join_nested_quantifiers() {
        for (src, target) in [
            ("exists X (exists Y (X = Y))", "exists X Y (X = Y)"),
            (
                "exists X Y ( exists Z ( X < Y and Y < Z ))",
                "exists X Y Z ( X < Y and Y < Z )",
            ),
            (
                "exists X (exists Y (X = Y and q(Y)))",
                "exists X Y (X = Y and q(Y))",
            ),
            (
                "exists X (exists X$i (p(X) -> X$i < 1))",
                "exists X X$i (p(X) -> X$i < 1)",
            ),
            (
                "forall X Y (forall Y Z (p(X,Y) and q(Y,Z)))",
                "forall X Y Z (p(X,Y) and q(Y,Z))",
            ),
            (
                "forall X (forall Y (forall Z (X = Y = Z)))",
                "forall X Y Z (X = Y = Z)",
            ),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .apply(&mut join_nested_quantifiers),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_extend_quantification_scope() {
        for (src, target) in [
            (
                "exists X (q(X) and 1 < 3) and p(Z)",
                "exists X (q(X) and 1 < 3 and p(Z))",
            ),
            (
                "exists X (q(X) and 1 < 3) and p(X)",
                "exists X (q(X) and 1 < 3) and p(X)",
            ),
            (
                "forall Z X (q(X) and 1 < Z) or p(Y,Z$)",
                "forall Z X (q(X) and 1 < Z or p(Y,Z$))",
            ),
            (
                "p(Z) and exists X (q(X) and 1 < 3)",
                "exists X (p(Z) and (q(X) and 1 < 3))",
            ),
        ] {
            let result = extend_quantifier_scope(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(result, target, "{result} != {target}")
        }
    }
}
