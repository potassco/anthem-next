use {
    crate::{
        syntax_tree::fol,
        translating::completion::{components, heads},
    },
    itertools::Itertools,
};

pub fn ordered_completion(theory: fol::Theory) -> Option<fol::Theory> {
    let (definitions, constraints) = components(theory)?;

    for (_, heads) in heads(&definitions) {
        if !heads.iter().all_equal() {
            return None;
        }
    }

    let comp_rules = definitions.clone().into_iter().map(|(g, a)| {
        let v = g.variables();
        fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::ReverseImplication,
            lhs: fol::Formula::AtomicFormula(g).into(),
            rhs: fol::Formula::disjoin(a.into_iter().map(|f_i| {
                let u_i = f_i.free_variables().difference(&v).cloned().collect();
                f_i.quantify(fol::Quantifier::Exists, u_i)
            }))
            .into(),
        }
        .quantify(fol::Quantifier::Forall, v.into_iter().collect())
    });

    let ocomp_def = definitions.into_iter().map(|(g, a)| {
        let v = g.variables();
        fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: fol::Formula::AtomicFormula(g).into(),
            rhs: fol::Formula::disjoin(a.into_iter().map(|f_i| {
                let u_i = f_i.free_variables().difference(&v).cloned().collect();
                f_i.quantify(fol::Quantifier::Exists, u_i)
            }))
            .into(),
        }
        .quantify(fol::Quantifier::Forall, v.into_iter().collect())
    });

    let mut formulas: Vec<_> = constraints
        .into_iter()
        .map(fol::Formula::universal_closure)
        .collect();
    formulas.extend(comp_rules);
    formulas.extend(ocomp_def);

    Some(fol::Theory { formulas })
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
