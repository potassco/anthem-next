use {
    crate::syntax_tree::fol::{Formula, Predicate, Theory},
    itertools::Itertools,
    std::{collections::HashSet, fmt, iter::repeat},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Role {
    Axiom,
    Lemma,
    Conjecture,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Role::Axiom => write!(f, "axiom"),
            Role::Lemma => write!(f, "lemma"),
            Role::Conjecture => write!(f, "conjecture"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedFormula {
    pub name: String,
    pub role: Role,
    pub formula: Formula,
}

impl AnnotatedFormula {
    fn symbols(&self) -> HashSet<String> {
        self.formula.symbols()
    }

    fn predicates(&self) -> HashSet<Predicate> {
        self.formula.predicates()
    }
}

impl fmt::Display for AnnotatedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = &self.name;
        let role = &self.role;
        let formula = crate::formatting::fol::tptp::Format(&self.formula);
        writeln!(f, "tff({name}, {role}, {formula}).")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Problem {
    pub formulas: Vec<AnnotatedFormula>,
}

impl Problem {
    pub fn from_parts(axioms: Theory, lemmas: Theory, conjectures: Theory) -> Self {
        let mut formulas = Vec::new();

        for (i, formula) in axioms.formulas.into_iter().enumerate() {
            formulas.push(AnnotatedFormula {
                name: format!("axiom_{i}"),
                role: Role::Axiom,
                formula,
            })
        }

        for (i, formula) in lemmas.formulas.into_iter().enumerate() {
            formulas.push(AnnotatedFormula {
                name: format!("lemma_{i}"),
                role: Role::Lemma,
                formula,
            })
        }

        for (i, formula) in conjectures.formulas.into_iter().enumerate() {
            formulas.push(AnnotatedFormula {
                name: format!("conjecture_{i}"),
                role: Role::Conjecture,
                formula,
            })
        }

        Problem { formulas }
    }

    pub fn symbols(&self) -> HashSet<String> {
        let mut result = HashSet::new();
        for formula in &self.formulas {
            result.extend(formula.symbols());
        }
        result
    }

    pub fn predicates(&self) -> HashSet<Predicate> {
        let mut result = HashSet::new();
        for formula in &self.formulas {
            result.extend(formula.predicates())
        }
        result
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, include_str!("preample.p"))?;

        for (i, symbol) in self.symbols().into_iter().enumerate() {
            writeln!(f, "tff(symbol{i}, type, {symbol}: object).")?
        }

        // TODO: Have a specific type for predicates?
        for (i, predicate) in self.predicates().into_iter().enumerate() {
            let symbol = predicate.symbol;
            let input: String = repeat("object")
                .take(predicate.arity)
                .intersperse(", ")
                .collect();
            writeln!(f, "tff(predicate_{i}, type, {symbol}: ({input}) > $o).")?
        }

        for formula in &self.formulas {
            formula.fmt(f)?;
        }

        Ok(())
    }
}
