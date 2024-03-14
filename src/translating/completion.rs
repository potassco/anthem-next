use {
    crate::{
        convenience::unbox::{fol::UnboxedFormula, Unbox as _},
        simplifying::fol::ht,
        syntax_tree::fol,
    },
    indexmap::{map::Entry, IndexMap},
};

/// A sentence is completable if it has the form "forall (F -> G)",
/// where G contains no intensional symbols OR has the form "p(V)"".
/// If a sentence is completable, this function returns "G"
fn completable_beheader(sentence: fol::Formula) -> Option<fol::AtomicFormula> {
    match sentence.clone().unbox() {
        UnboxedFormula::QuantifiedFormula {
            quantification:
                fol::Quantification {
                    quantifier: fol::Quantifier::Forall,
                    ..
                },
            formula:
                fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::Implication,
                    rhs,
                    ..
                },
        } => match rhs.unbox() {
            UnboxedFormula::AtomicFormula(a) => match a {
                fol::AtomicFormula::Truth | fol::AtomicFormula::Falsity => Some(a),
                fol::AtomicFormula::Atom(_) => Some(a),
                fol::AtomicFormula::Comparison(_) => None,
            },

            _ => None,
        },

        UnboxedFormula::QuantifiedFormula {
            quantification:
                fol::Quantification {
                    quantifier: fol::Quantifier::Forall,
                    ..
                },
            formula:
                fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::ReverseImplication,
                    lhs,
                    ..
                },
        } => match lhs.unbox() {
            UnboxedFormula::AtomicFormula(a) => match a {
                fol::AtomicFormula::Truth | fol::AtomicFormula::Falsity => Some(a),
                fol::AtomicFormula::Atom(_) => Some(a),
                fol::AtomicFormula::Comparison(_) => None,
            },

            _ => None,
        },

        UnboxedFormula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            rhs: fol::Formula::AtomicFormula(a),
            ..
        } => match a {
            fol::AtomicFormula::Truth | fol::AtomicFormula::Falsity => Some(a),
            fol::AtomicFormula::Atom(_) => Some(a),
            fol::AtomicFormula::Comparison(_) => None,
        },

        UnboxedFormula::BinaryFormula {
            connective: fol::BinaryConnective::ReverseImplication,
            lhs: fol::Formula::AtomicFormula(a),
            ..
        } => match a {
            fol::AtomicFormula::Truth | fol::AtomicFormula::Falsity => Some(a),
            fol::AtomicFormula::Atom(_) => Some(a),
            fol::AtomicFormula::Comparison(_) => None,
        },

        _ => None,
    }
}

/// Returns true if s1 and s2 have the same predicate symbol p/n in the head
/// but head(s1) != head(s2)
fn head_mismatch(s1: &fol::AtomicFormula, s2: &fol::AtomicFormula) -> bool {
    match s1 {
        fol::AtomicFormula::Atom(a1) => {
            let p1 = &a1.predicate();
            let n1 = a1.terms.len();
            match s2 {
                fol::AtomicFormula::Atom(a2) => {
                    let p2 = &a2.predicate();
                    let n2 = a2.terms.len();
                    if p1 == p2 && n1 == n2 {
                        s1 != s2
                    } else {
                        false
                    }
                }
                _ => false,
            }
        }
        _ => false,
    }
}

/// Returns a mapping from <theory> formulas to their heads if <theory> is completable
/// Otherwise returns None
fn completable_theory(theory: &fol::Theory) -> Option<IndexMap<fol::Formula, fol::AtomicFormula>> {
    if !theory.formulas.is_empty() {
        let mut formulas = Vec::<fol::Formula>::new();
        let mut rule_heads = Vec::<fol::AtomicFormula>::new();
        for sentence in theory.formulas.iter() {
            formulas.push(sentence.clone());
            match completable_beheader(sentence.clone()) {
                Some(f) => {
                    rule_heads.push(f.clone());
                }
                None => {
                    return None;
                }
            }
        }
        let mut formula_heads = IndexMap::<fol::Formula, fol::AtomicFormula>::new();
        for (i, s) in formulas.iter().enumerate() {
            formula_heads.insert(s.clone(), rule_heads[i].clone());
        }
        for s1 in formulas.iter() {
            let head1 = &formula_heads[s1];
            for (s2, head2) in formula_heads.iter() {
                if s1 != s2 && head_mismatch(head1, head2) {
                    return None;
                }
            }
        }
        Some(formula_heads)
    } else {
        None
    }
}

/// Create a map from each unique head to a vector of F_i formula bodies (definitions)
fn definitions(theory: &fol::Theory) -> IndexMap<fol::AtomicFormula, Vec<fol::Formula>> {
    let mut definitions = IndexMap::<fol::AtomicFormula, Vec<fol::Formula>>::new();
    for sentence in theory.formulas.iter() {
        match sentence.clone().unbox() {
            UnboxedFormula::QuantifiedFormula { formula, .. } => match formula.clone().unbox() {
                UnboxedFormula::BinaryFormula {
                    connective: fol::BinaryConnective::Implication,
                    lhs,
                    rhs: fol::Formula::AtomicFormula(head),
                } => match definitions.entry(head) {
                    Entry::Occupied(mut entry) => {
                        entry.get_mut().push(lhs);
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(vec![lhs]);
                    }
                },

                UnboxedFormula::BinaryFormula {
                    connective: fol::BinaryConnective::ReverseImplication,
                    lhs: fol::Formula::AtomicFormula(head),
                    rhs,
                } => match definitions.entry(head) {
                    Entry::Occupied(mut entry) => {
                        entry.get_mut().push(rhs);
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(vec![rhs]);
                    }
                },

                _ => {}
            },

            UnboxedFormula::BinaryFormula {
                connective: fol::BinaryConnective::Implication,
                lhs,
                rhs: fol::Formula::AtomicFormula(head),
            } => match definitions.entry(head) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().push(lhs);
                }
                Entry::Vacant(entry) => {
                    entry.insert(vec![lhs]);
                }
            },

            UnboxedFormula::BinaryFormula {
                connective: fol::BinaryConnective::ReverseImplication,
                lhs: fol::Formula::AtomicFormula(head),
                rhs,
            } => match definitions.entry(head) {
                Entry::Occupied(mut entry) => {
                    entry.get_mut().push(rhs);
                }
                Entry::Vacant(entry) => {
                    entry.insert(vec![rhs]);
                }
            },

            _ => {}
        }
    }
    definitions
}

/// <theory> must be a completable theory, so we know it has the form forall V (body -> head) OR body -> head
/// <formula_heads[formula] = head(formula)>
// TODO: Accept owned fol:Theory
pub fn completion(theory: &fol::Theory) -> Option<fol::Theory> {
    match completable_theory(theory) {
        Some(formula_heads) => {
            let definitions = definitions(theory);
            let mut completions = Vec::<fol::Formula>::new(); // Now we need the completed definitions of each unique head
            for (formula, head) in formula_heads.iter() {
                if head == &fol::AtomicFormula::Falsity {
                    // Every constraint gets its own "completed definition"
                    completions.push(formula.clone());
                }
            }
            for (head, body_vec) in definitions.iter() {
                // p(V), { Fi }
                match head {
                    fol::AtomicFormula::Falsity => {}
                    _ => {
                        // TODO distinguish between intensional and extensional predicate symbols
                        let head_vars = head.variables();
                        let mut bodies = Vec::<fol::Formula>::new();
                        for body in body_vec.iter() {
                            let mut free_vars = Vec::<fol::Variable>::new();
                            for var in body.free_variables().iter() {
                                // Ui (Ui are free variables in Fi that do not belong to V)
                                if !head_vars.contains(var) {
                                    free_vars.push(var.clone());
                                }
                            }
                            if !free_vars.is_empty() {
                                free_vars.sort();
                                let qbod = fol::Formula::QuantifiedFormula {
                                    quantification: fol::Quantification {
                                        quantifier: fol::Quantifier::Exists,
                                        variables: free_vars,
                                    },
                                    formula: body.clone().into(),
                                };
                                bodies.push(qbod);
                            } else {
                                bodies.push(body.clone());
                            }
                        }
                        let full_body = ht::basic_simplify(fol::Formula::disjoin(bodies));
                        let comp = match head_vars.len() {
                            0 => fol::Formula::BinaryFormula {
                                connective: fol::BinaryConnective::Equivalence,
                                lhs: fol::Formula::AtomicFormula(head.clone()).into(),
                                rhs: full_body.into(),
                            },
                            _ => {
                                let mut sorted_head_vars = Vec::from_iter(head_vars);
                                sorted_head_vars.sort();
                                fol::Formula::QuantifiedFormula {
                                    quantification: fol::Quantification {
                                        quantifier: fol::Quantifier::Forall,
                                        variables: sorted_head_vars,
                                    },
                                    formula: fol::Formula::BinaryFormula {
                                        connective: fol::BinaryConnective::Equivalence,
                                        lhs: Box::new(fol::Formula::AtomicFormula(head.clone())),
                                        rhs: full_body.into(),
                                    }
                                    .into(),
                                }
                            }
                        };
                        completions.push(comp);
                    }
                }
            }
            Some(fol::Theory {
                formulas: completions,
            })
        }
        None => {
            println!("Not a completable theory!");
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::translating::{completion::completion, tau_star::tau_star};

    #[test]
    fn test_completion() {
        for (src, target) in [
            ("p(X) :- q(X).", "forall V1 (p(V1) <-> exists X (V1 = X and exists Z (Z = X and q(Z))))."),
            ("p(a). p(b). q(X,Y) :- p(X), p(Y).", "forall V1 (p(V1) <-> V1 = a or V1 = b). forall V1 V2 (q(V1, V2) <-> exists X Y (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z)))))."),
            ("{p(X+1)} :- q(X).", "forall V1 (p(V1) <-> exists X (exists I$i J$i (V1 = I$i + J$i and I$i = X and J$i = 1) and exists Z (Z = X and q(Z)) and not not p(V1)))."),
            ("r(X) :- q(X). r(G,Y) :- G < Y. r(a).", "forall V1 (r(V1) <-> exists X (V1 = X and exists Z (Z = X and q(Z))) or V1 = a). forall V1 V2 (r(V1,V2) <-> exists G Y (V1 = G and V2 = Y and exists Z Z1 (Z = G and Z1 = Y and Z < Z1) ) )."),
            ("composite(I*J) :- I>1, J>1. prime(I) :- I = 2..n, not composite(I).", "forall V1 (composite(V1) <-> exists I J (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (exists Z Z1 (Z = I and Z1 = 1 and Z > Z1) and exists Z Z1 (Z = J and Z1 = 1 and Z > Z1)))). forall V1 (prime(V1) <-> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z)))))."),
            ("p :- q, not t. p :- r. r :- t.", "p <-> (q and not t) or (r). r <-> t."),
            ("p. p(a). :- q.", "q -> #false. p <-> #true. forall V1 (p(V1) <-> V1 = a)."),
        ] {
            let result = completion(&tau_star(src.parse().unwrap())).unwrap();
            assert_eq!(result, target.parse().unwrap(), "\n\n{result}!=\n {target}")
        }
    }
}
