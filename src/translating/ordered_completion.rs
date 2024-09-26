use crate::{
    syntax_tree::fol::{
        Atom, AtomicFormula, BinaryConnective, Formula, Quantifier, Theory, UnaryConnective,
    },
    translating::completion::{components, no_head_mismatches},
};

pub fn ordered_completion(theory: Theory) -> Option<Theory> {
    let (definitions, constraints) = components(theory)?;

    if !no_head_mismatches(&definitions) {
        return None;
    }

    let comp_rules = definitions.clone().into_iter().map(|(g, a)| {
        let v = g.variables();
        Formula::BinaryFormula {
            connective: BinaryConnective::ReverseImplication,
            lhs: Formula::AtomicFormula(g).into(),
            rhs: Formula::disjoin(a.into_iter().map(|f_i| {
                let u_i = f_i.free_variables().difference(&v).cloned().collect();
                f_i.quantify(Quantifier::Exists, u_i)
            }))
            .into(),
        }
        .quantify(Quantifier::Forall, v.into_iter().collect())
    });

    let ocomp_def = definitions.into_iter().map(|(g, a)| {
        let v = g.variables();
        match g.clone() {
            AtomicFormula::Atom(head_atom) => Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::AtomicFormula(g).into(),
                rhs: Formula::disjoin(a.into_iter().map(|f_i| {
                    let u_i = f_i.free_variables().difference(&v).cloned().collect();
                    let f_i_order = conjoin_order_atom(f_i, head_atom.clone());
                    f_i_order.quantify(Quantifier::Exists, u_i)
                }))
                .into(),
            }
            .quantify(Quantifier::Forall, v.into_iter().collect()),
            _ => unreachable!(),
        }
    });

    let mut formulas: Vec<_> = constraints
        .into_iter()
        .map(Formula::universal_closure)
        .collect();
    formulas.extend(comp_rules);
    formulas.extend(ocomp_def);

    Some(Theory { formulas })
}

fn conjoin_order_atom(formula: Formula, head_atom: Atom) -> Formula {
    match formula {
        Formula::AtomicFormula(AtomicFormula::Atom(a)) => {
            let p = head_atom.predicate_symbol;
            let mut xs = head_atom.terms;
            let q = a.predicate_symbol.clone();
            let mut zs = a.terms.clone();

            let order_predicate = format!("less_{q}_{p}");
            let mut order_terms = Vec::new();
            order_terms.append(&mut zs);
            order_terms.append(&mut xs);

            let order_atom = Atom {
                predicate_symbol: order_predicate,
                terms: order_terms,
            };

            Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(a)).into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(order_atom)).into(),
            }
        }
        Formula::AtomicFormula(f) => Formula::AtomicFormula(f),
        Formula::UnaryFormula {
            connective: connective @ UnaryConnective::Negation,
            formula,
        } => Formula::UnaryFormula {
            connective,
            formula,
        },
        Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => Formula::BinaryFormula {
            connective,
            lhs: conjoin_order_atom(*lhs, head_atom.clone()).into(),
            rhs: conjoin_order_atom(*rhs, head_atom).into(),
        },
        Formula::QuantifiedFormula {
            quantification,
            formula,
        } => Formula::QuantifiedFormula {
            quantification,
            formula: conjoin_order_atom(*formula, head_atom).into(),
        },
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        syntax_tree::fol,
        translating::{ordered_completion::ordered_completion, tau_star::tau_star},
    };

    #[test]
    fn test_ordered_completion() {
        for (src, target) in [
            ("p :- q.", "p <- q. p -> q and less_q_p."),
            ("p(X) :- q.", "forall V1 (p(V1) <- exists X (V1 = X and q)). forall V1 (p(V1) -> exists X (V1 = X and (q and less_q_p(V1))))."),
            ("p(X) :- q(X).", "forall V1 (p(V1) <- exists X (V1 = X and exists Z (Z = X and q(Z)))). forall V1 (p(V1) -> exists X (V1 = X and exists Z (Z = X and (q(Z) and less_q_p(Z, V1)))))."),
            ("p(X) :- q(X). p(X) :- not r(X).", "forall V1 (p(V1) <- exists X (V1 = X and exists Z (Z = X and q(Z))) or exists X (V1 = X and exists Z (Z = X and not r(Z)))). forall V1 (p(V1) -> exists X (V1 = X and exists Z (Z = X and (q(Z) and less_q_p(Z, V1)))) or exists X (V1 = X and exists Z (Z = X and not r(Z))))."),
            ("p(X) :- q(X-1). {p(X)} :- r(X,Y).", "forall V1 (p(V1) <- exists X (V1 = X and exists Z (exists I$i J$i (Z = I$i - J$i and I$i = X and J$i = 1) and q(Z))) or exists X Y (V1 = X and exists Z Z1 (Z = X and Z1 = Y and r(Z, Z1)) and not not p(V1))). forall V1 (p(V1) -> exists X (V1 = X and exists Z (exists I$i J$i (Z = I$i - J$i and I$i = X and J$i = 1) and (q(Z) and less_q_p(Z, V1)))) or exists X Y (V1 = X and exists Z Z1 (Z = X and Z1 = Y and (r(Z, Z1) and less_r_p(Z, Z1, V1))) and not not p(V1)))."),
            ("t(X,Y) :- e(X,Y). t(X,Z) :- e(X,Y), t(Y,Z).", "forall V1 V2 (t(V1, V2) <- exists X Y (V1 = X and V2 = Y and exists Z Z1 (Z = X and Z1 = Y and e(Z, Z1))) or exists X Z Y (V1 = X and V2 = Z and (exists Z Z1 (Z = X and Z1 = Y and e(Z, Z1)) and exists Z1 Z2 (Z1 = Y and Z2 = Z and t(Z1, Z2))))). forall V1 V2 (t(V1, V2) -> exists X Y (V1 = X and V2 = Y and exists Z Z1 (Z = X and Z1 = Y and (e(Z, Z1) and less_e_t(Z, Z1, V1, V2)))) or exists X Z Y (V1 = X and V2 = Z and (exists Z Z1 (Z = X and Z1 = Y and (e(Z, Z1) and less_e_t(Z, Z1, V1, V2))) and exists Z1 Z2 (Z1 = Y and Z2 = Z and (t(Z1, Z2) and less_t_t(Z1, Z2, V1, V2))))))."),
        ] {
            let left = ordered_completion(tau_star(src.parse().unwrap())).unwrap();
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_oc_incompletable() {
        for theory in [
            "forall X (p(X, a) <- q(X)).",
            "forall X (p(X, X) <- q(X)).",
            "forall X (p(X) <- q(X,Y)).",
            "forall V1 V2 (p(V1, V2) <- t). forall V1 X (p(V1,X) <- q).",
        ] {
            let theory: fol::Theory = theory.parse().unwrap();
            assert!(
                ordered_completion(theory.clone()).is_none(),
                "`{theory}` should not be completable"
            );
        }
    }
}
