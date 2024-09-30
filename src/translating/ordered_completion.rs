use crate::{
    syntax_tree::fol::{
        Atom, AtomicFormula, BinaryConnective, Formula, GeneralTerm, Predicate, Quantifier, Theory,
        UnaryConnective,
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

fn order_predicate_symbol(p: String, q: String) -> String {
    format!("less_{p}_{q}")
}

fn conjoin_order_atom(formula: Formula, head_atom: Atom) -> Formula {
    // replace positive atoms (i.e. not in scope of any negation) q(zs) by the formula
    // q(zs) and less_q_p(zs,xs)
    // where p(xs) is the head_atom
    match formula {
        Formula::AtomicFormula(AtomicFormula::Atom(a)) => {
            let p = head_atom.predicate_symbol;
            let mut xs = head_atom.terms;
            let q = a.predicate_symbol.clone();
            let mut zs = a.terms.clone();

            let order_predicate = order_predicate_symbol(q, p);
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

fn transitivity_axiom(p: Predicate, q: Predicate, r: Predicate) -> Formula {
    // generate all variables
    let vars: Vec<GeneralTerm> = (1..=p.arity + q.arity + r.arity)
        .map(|i| GeneralTerm::Variable(format!("X{i}")))
        .collect();
    // split up into variables for p, q, r
    let (p_vars, vars) = vars.split_at(p.arity);
    let (q_vars, r_vars) = vars.split_at(q.arity);

    // collect variables for less_p_q, less_q_r, less_p_r
    let mut pq_vars = p_vars.to_vec().clone();
    pq_vars.extend(q_vars.to_vec().clone());
    let mut qr_vars = q_vars.to_vec();
    qr_vars.extend(r_vars.to_vec().clone());
    let mut pr_vars = p_vars.to_vec();
    pr_vars.extend(r_vars.to_vec());

    let less_pq = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
        predicate_symbol: order_predicate_symbol(p.symbol.clone(), q.symbol.clone()),
        terms: pq_vars,
    }));
    let less_qr = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
        predicate_symbol: order_predicate_symbol(q.symbol, r.symbol.clone()),
        terms: qr_vars,
    }));
    let less_pr = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
        predicate_symbol: order_predicate_symbol(p.symbol, r.symbol),
        terms: pr_vars,
    }));

    let mut variables = less_pq.free_variables();
    variables.extend(less_qr.free_variables());

    Formula::BinaryFormula {
        connective: BinaryConnective::Implication,
        lhs: Box::new(Formula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: less_pq.into(),
            rhs: less_qr.into(),
        }),
        rhs: less_pr.into(),
    }
    .quantify(Quantifier::Forall, variables.into_iter().collect())
}

fn irreflexivity_axiom(p: Predicate) -> Formula {
    let mut terms: Vec<GeneralTerm> = (1..=p.arity)
        .map(|i| GeneralTerm::Variable(format!("X{i}")))
        .collect();
    terms.extend(terms.clone());
    let less_pp = Formula::AtomicFormula(AtomicFormula::Atom(Atom {
        predicate_symbol: order_predicate_symbol(p.symbol.clone(), p.symbol),
        terms,
    }));

    let variables = less_pp.free_variables();

    Formula::UnaryFormula {
        connective: UnaryConnective::Negation,
        formula: less_pp.into(),
    }
    .quantify(Quantifier::Forall, variables.into_iter().collect())
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
