use {
    crate::{
        formatting::fol::default::Format,
        parsing::fol::pest::{
            AtomParser, AtomicFormulaParser, BinaryConnectiveParser, BinaryOperatorParser,
            ComparisonParser, FormulaParser, FunctionConstantParser, GeneralTermParser,
            GuardParser, IntegerTermParser, PredicateParser, QuantificationParser,
            QuantifierParser, RelationParser, SymbolicTermParser, TheoryParser,
            UnaryConnectiveParser, UnaryOperatorParser, VariableParser,
        },
        syntax_tree::{impl_node, Node},
    },
    std::{collections::HashSet, hash::Hash},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
}

impl_node!(BinaryOperator, Format, BinaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum IntegerTerm {
    Numeral(isize),
    FunctionConstant(String),
    Variable(String),
    UnaryOperation {
        op: UnaryOperator,
        arg: Box<IntegerTerm>,
    },
    BinaryOperation {
        op: BinaryOperator,
        lhs: Box<IntegerTerm>,
        rhs: Box<IntegerTerm>,
    },
}

impl_node!(IntegerTerm, Format, IntegerTermParser);

impl IntegerTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            IntegerTerm::Numeral(_) | IntegerTerm::FunctionConstant(_) => HashSet::new(),
            IntegerTerm::Variable(v) => HashSet::from([Variable {
                name: v.to_string(),
                sort: Sort::Integer,
            }]),
            IntegerTerm::UnaryOperation { arg: t, .. } => t.variables(),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        match &self {
            IntegerTerm::FunctionConstant(c) => HashSet::from([FunctionConstant {
                name: c.clone(),
                sort: Sort::Integer,
            }]),
            IntegerTerm::Numeral(_) | IntegerTerm::Variable(_) => HashSet::new(),
            IntegerTerm::UnaryOperation { arg: t, .. } => t.function_constants(),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                let mut constants = lhs.function_constants();
                constants.extend(rhs.function_constants());
                constants
            }
        }
    }

    pub fn substitute(self, var: Variable, term: IntegerTerm) -> Self {
        match self {
            IntegerTerm::Variable(s) if var.name == s && var.sort == Sort::Integer => term,
            IntegerTerm::Numeral(_)
            | IntegerTerm::FunctionConstant(_)
            | IntegerTerm::Variable(_) => self,
            IntegerTerm::UnaryOperation { op, arg } => IntegerTerm::UnaryOperation {
                op,
                arg: arg.substitute(var, term).into(),
            },
            IntegerTerm::BinaryOperation { op, lhs, rhs } => IntegerTerm::BinaryOperation {
                op,
                lhs: lhs.substitute(var.clone(), term.clone()).into(),
                rhs: rhs.substitute(var, term).into(),
            },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum SymbolicTerm {
    Symbol(String),
    FunctionConstant(String),
    Variable(String),
}

impl_node!(SymbolicTerm, Format, SymbolicTermParser);

impl SymbolicTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            SymbolicTerm::Symbol(_) | SymbolicTerm::FunctionConstant(_) => HashSet::new(),
            SymbolicTerm::Variable(v) => HashSet::from([Variable {
                name: v.to_string(),
                sort: Sort::Symbol,
            }]),
        }
    }

    pub fn symbols(&self) -> HashSet<String> {
        match &self {
            SymbolicTerm::Symbol(s) => HashSet::from([s.clone()]),
            SymbolicTerm::FunctionConstant(_) | SymbolicTerm::Variable(_) => HashSet::new(),
        }
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        match &self {
            SymbolicTerm::FunctionConstant(c) => HashSet::from([FunctionConstant {
                name: c.clone(),
                sort: Sort::Symbol,
            }]),
            SymbolicTerm::Symbol(_) | SymbolicTerm::Variable(_) => HashSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum GeneralTerm {
    Infimum,
    Supremum,
    FunctionConstant(String),
    Variable(String),
    IntegerTerm(IntegerTerm),
    SymbolicTerm(SymbolicTerm),
}

impl_node!(GeneralTerm, Format, GeneralTermParser);

impl GeneralTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            GeneralTerm::Infimum | GeneralTerm::Supremum | GeneralTerm::FunctionConstant(_) => {
                HashSet::new()
            }
            GeneralTerm::Variable(v) => HashSet::from([Variable {
                name: v.to_string(),
                sort: Sort::General,
            }]),
            GeneralTerm::IntegerTerm(t) => t.variables(),
            GeneralTerm::SymbolicTerm(t) => t.variables(),
        }
    }

    pub fn symbols(&self) -> HashSet<String> {
        match &self {
            GeneralTerm::SymbolicTerm(t) => t.symbols(),
            _ => HashSet::new(),
        }
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        match &self {
            GeneralTerm::FunctionConstant(c) => HashSet::from([FunctionConstant {
                name: c.clone(),
                sort: Sort::General,
            }]),
            GeneralTerm::IntegerTerm(t) => t.function_constants(),
            GeneralTerm::SymbolicTerm(t) => t.function_constants(),
            GeneralTerm::Infimum | GeneralTerm::Supremum | GeneralTerm::Variable(_) => {
                HashSet::new()
            }
        }
    }

    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            GeneralTerm::Variable(s) if var.name == s && var.sort == Sort::General => term,
            GeneralTerm::IntegerTerm(t) if var.sort == Sort::Integer => match term {
                GeneralTerm::IntegerTerm(term) => GeneralTerm::IntegerTerm(t.substitute(var, term)),
                _ => panic!(
                    "cannot substitute general term `{term}` for the integer variable `{var}`"
                ),
            },
            t => t,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Predicate {
    pub symbol: String,
    pub arity: usize,
}

impl_node!(Predicate, Format, PredicateParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom {
    pub predicate_symbol: String,
    pub terms: Vec<GeneralTerm>,
}

impl Atom {
    pub fn predicate(&self) -> Predicate {
        Predicate {
            symbol: self.predicate_symbol.clone(),
            arity: self.terms.len(),
        }
    }
}

impl_node!(Atom, Format, AtomParser);

impl Atom {
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        let predicate_symbol = self.predicate_symbol;

        let mut terms = Vec::new();
        for t in self.terms {
            terms.push(t.substitute(var.clone(), term.clone()))
        }

        Atom {
            predicate_symbol,
            terms,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Relation {
    Equal,
    NotEqual,
    Greater,
    Less,
    GreaterEqual,
    LessEqual,
}

impl_node!(Relation, Format, RelationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Guard {
    pub relation: Relation,
    pub term: GeneralTerm,
}

impl_node!(Guard, Format, GuardParser);

impl Guard {
    pub fn variables(&self) -> HashSet<Variable> {
        self.term.variables()
    }

    pub fn symbols(&self) -> HashSet<String> {
        self.term.symbols()
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        self.term.function_constants()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Comparison {
    pub term: GeneralTerm,
    pub guards: Vec<Guard>,
}

impl_node!(Comparison, Format, ComparisonParser);

impl Comparison {
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        let lhs = self.term.substitute(var.clone(), term.clone());

        let mut guards = Vec::new();
        for old_guard in self.guards {
            let new_guard = Guard {
                relation: old_guard.relation,
                term: old_guard.term.substitute(var.clone(), term.clone()),
            };
            guards.push(new_guard);
        }

        Comparison { term: lhs, guards }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AtomicFormula {
    Truth,
    Falsity,
    Atom(Atom),
    Comparison(Comparison),
}

impl_node!(AtomicFormula, Format, AtomicFormulaParser);

impl AtomicFormula {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => HashSet::new(),
            AtomicFormula::Atom(a) => {
                let mut vars = HashSet::new();
                for t in a.terms.iter() {
                    vars.extend(t.variables());
                }
                vars
            }
            AtomicFormula::Comparison(c) => {
                let mut vars = c.term.variables();
                for guard in c.guards.iter() {
                    vars.extend(guard.variables())
                }
                vars
            }
        }
    }

    pub fn predicates(&self) -> HashSet<Predicate> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth | AtomicFormula::Comparison(_) => {
                HashSet::new()
            }
            AtomicFormula::Atom(a) => HashSet::from([a.predicate()]),
        }
    }

    pub fn symbols(&self) -> HashSet<String> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => HashSet::new(),
            AtomicFormula::Atom(a) => {
                let mut symbols = HashSet::new();
                for t in a.terms.iter() {
                    symbols.extend(t.symbols());
                }
                symbols
            }
            AtomicFormula::Comparison(c) => {
                let mut symbols = c.term.symbols();
                for guard in c.guards.iter() {
                    symbols.extend(guard.symbols())
                }
                symbols
            }
        }
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => HashSet::new(),
            AtomicFormula::Atom(a) => {
                let mut function_constants = HashSet::new();
                for t in a.terms.iter() {
                    function_constants.extend(t.function_constants());
                }
                function_constants
            }
            AtomicFormula::Comparison(c) => {
                let mut function_constants = c.term.function_constants();
                for guard in c.guards.iter() {
                    function_constants.extend(guard.function_constants())
                }
                function_constants
            }
        }
    }

    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            AtomicFormula::Atom(a) => AtomicFormula::Atom(a.substitute(var, term)),
            AtomicFormula::Comparison(c) => AtomicFormula::Comparison(c.substitute(var, term)),
            f => f,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryConnective {
    Negation,
}

impl_node!(UnaryConnective, Format, UnaryConnectiveParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

impl_node!(Quantifier, Format, QuantifierParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Quantification {
    pub quantifier: Quantifier,
    pub variables: Vec<Variable>,
}

impl_node!(Quantification, Format, QuantificationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    General,
    Integer,
    Symbol,
}

// TODO: Should Sort be a Node?

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct FunctionConstant {
    pub name: String,
    pub sort: Sort,
}

impl_node!(FunctionConstant, Format, FunctionConstantParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Variable {
    pub name: String,
    pub sort: Sort,
}

impl_node!(Variable, Format, VariableParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryConnective {
    Conjunction,
    Disjunction,
    Implication,
    ReverseImplication,
    Equivalence,
}

impl_node!(BinaryConnective, Format, BinaryConnectiveParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Formula {
    AtomicFormula(AtomicFormula),
    UnaryFormula {
        connective: UnaryConnective,
        formula: Box<Formula>,
    },
    BinaryFormula {
        connective: BinaryConnective,
        lhs: Box<Formula>,
        rhs: Box<Formula>,
    },
    QuantifiedFormula {
        quantification: Quantification,
        formula: Box<Formula>,
    },
}

impl_node!(Formula, Format, FormulaParser);

impl Formula {
    /// Recursively turn a list of formulas into a conjunction tree
    pub fn conjoin(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        /*
         * One could also implement this recursively:
         *
         * Case 1: List of formulas is empty
         * -> Return #true
         *
         * Case 2: List of formulas contains a single formula
         * -> Return that formula
         *
         * Case 3: List of formulas contains more than a single formula
         * -> Return conjoin(formula[0..n-2]) and formula[n-1]
         */

        formulas
            .into_iter()
            .reduce(|acc, e| Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: acc.into(),
                rhs: e.into(),
            })
            .unwrap_or_else(|| Formula::AtomicFormula(AtomicFormula::Truth))
    }

    /// Recursively turn a list of formulas into a tree of disjunctions
    pub fn disjoin(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        /*
         * One could also implement this recursively:
         *
         * Case 1: List of formulas is empty
         * -> Return #false
         *
         * Case 2: List of formulas contains a single formula
         * -> Return that formula
         *
         * Case 3: List of formulas contains more than a single formula
         * -> Return conjoin(formula[0..n-2]) or formula[n-1]
         */

        formulas
            .into_iter()
            .reduce(|acc, e| Formula::BinaryFormula {
                connective: BinaryConnective::Disjunction,
                lhs: acc.into(),
                rhs: e.into(),
            })
            .unwrap_or_else(|| Formula::AtomicFormula(AtomicFormula::Falsity))
    }

    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            Formula::AtomicFormula(f) => f.variables(),
            Formula::UnaryFormula { formula, .. } => formula.variables(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.variables(),
        }
    }

    pub fn free_variables(&self) -> HashSet<Variable> {
        match &self {
            Formula::AtomicFormula(f) => f.variables(),
            Formula::UnaryFormula { formula, .. } => formula.free_variables(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.free_variables();
                vars.extend(rhs.free_variables());
                vars
            }
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => {
                let mut vars = formula.free_variables();
                for var in &quantification.variables {
                    vars.remove(var);
                }
                vars
            }
        }
    }

    pub fn predicates(&self) -> HashSet<Predicate> {
        match &self {
            Formula::AtomicFormula(f) => f.predicates(),
            Formula::UnaryFormula { formula, .. } => formula.predicates(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.predicates();
                vars.extend(rhs.predicates());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.predicates(),
        }
    }

    pub fn symbols(&self) -> HashSet<String> {
        match &self {
            Formula::AtomicFormula(f) => f.symbols(),
            Formula::UnaryFormula { formula, .. } => formula.symbols(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.symbols();
                vars.extend(rhs.symbols());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.symbols(),
        }
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        match &self {
            Formula::AtomicFormula(f) => f.function_constants(),
            Formula::UnaryFormula { formula, .. } => formula.function_constants(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.function_constants();
                vars.extend(rhs.function_constants());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.function_constants(),
        }
    }

    // Replace all free occurences of var with term within the formula
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            Formula::AtomicFormula(f) => Formula::AtomicFormula(f.substitute(var, term)),
            Formula::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula.substitute(var, term).into(),
            },
            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.substitute(var.clone(), term.clone()).into(),
                rhs: rhs.substitute(var, term).into(),
            },
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } if !quantification.variables.contains(&var) => Formula::QuantifiedFormula {
                quantification,
                formula: formula.substitute(var, term).into(),
            },
            f @ Formula::QuantifiedFormula {
                quantification: _,
                formula: _,
            } => f,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Theory {
    pub formulas: Vec<Formula>,
}

impl_node!(Theory, Format, TheoryParser);

///////// End of FOL Language /////////






///////// Start of Control Language /////////

/// A Role dictates how a formula is used within a verification task
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Role {
    Assumption,
    Conjecture,
    Definition,
    Lemma,
    InductiveLemma,
}

impl_node!(Role, Format, RoleParser);

/// The Direction dictates which direction of an equivalence verification
/// task a formula should be used within
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Direction {
    Forward,
    Backward,
    Universal,
}

impl_node!(Direction, Format, DirectionParser);

/// An AnnotatedFormula can be optionally named
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FormulaName(pub Option<String>);

impl_node!(FormulaName, Format, FormulaNameParser);

/// A Claim is composed of AnnotatedFormulas
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedFormula {
    pub role: Role,
    pub direction: Direction,
    pub name: FormulaName,
    pub formula: Formula,
}

impl_node!(AnnotatedFormula, Format, AnnotatedFormulaParser);

/// A User Guide contains Placeholder Declarations, input/output Predicates, and
/// certain universal assumptions of a verification task
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct UserGuide {
    pub input_predicates: Vec<Predicate>,
    pub output_predicates: Vec<Predicate>,
    pub placeholders: Vec<FunctionConstant>,
    pub assumptions: Vec<AnnotatedFormula>,
}

impl_node!(UserGuide, Format, UserGuideParser);

/// User Guides are lists of Specs.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Spec {
    Input { predicates: Vec<Predicate> },
    Output { predicates: Vec<Predicate> },
    PlaceholderDeclaration { placeholders: Vec<FunctionConstant> },
    AnnotatedFormula(AnnotatedFormula),
}

impl_node!(Spec, Format, SpecParser);

/// A Specification defines additional assumptions and
/// the conjectures against which a program is compared.
/// It can also contain proof outline instructions (such as Definitions and Inductions),
/// thus all helper files are Specifications.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Specification {
    pub formulas: Vec<AnnotatedFormula>,
}

impl_node!(Specification, Format, SpecificationParser);





#[cfg(test)]
mod tests {
    use super::Formula;

    #[test]
    fn test_formula_conjoin() {
        for (src, target) in [
            (vec![], "#true"),
            (vec!["X = Y"], "X = Y"),
            (vec!["X = Y", "p(a)", "q(X)"], "(X = Y and p(a)) and q(X)"),
        ] {
            assert_eq!(
                Formula::conjoin(src.iter().map(|x| x.parse().unwrap())),
                target.parse().unwrap(),
            )
        }
    }

    #[test]
    fn test_formula_disjoin() {
        for (src, target) in [
            (vec![], "#false"),
            (vec!["X = Y"], "X = Y"),
            (vec!["X = Y", "p(a)", "q(X)"], "(X = Y or p(a)) or q(X)"),
        ] {
            assert_eq!(
                Formula::disjoin(src.iter().map(|x| x.parse().unwrap())),
                target.parse().unwrap(),
            )
        }
    }

    #[test]
    fn test_formula_free_variables() {
        for (src, target) in [
            ("forall X (X = Y)", vec!["Y"]),
            ("forall X (X = Y) and Y = Z", vec!["Y", "Z"]),
            ("forall X exists Y (X = Y)", vec![]),
        ] {
            assert_eq!(
                src.parse::<Formula>().unwrap().free_variables(),
                target.iter().map(|x| x.parse().unwrap()).collect(),
            )
        }
    }

    #[test]
    fn test_formula_substitute() {
        for (src, var, term, target) in [
            ("p(X)", "X", "s", "p(s)"),
            ("p(X)", "X", "5", "p(5)"),
            ("prime(-X$i + 13)", "X$i", "3*Y$i", "prime(-(3*Y$i) + 13)"),
            ("prime(X$i, X)", "X$i", "Y$i", "prime(Y$i, X)"),
            ("exists X (X = Y)", "Y", "3", "exists X (X = 3)"),
            ("forall X p(X)", "X", "1", "forall X p(X)"),
            (
                "exists X (X = Y)",
                "Y",
                "X$i + 3",
                "exists X (X = (X$i + 3))",
            ),
            (
                "forall X (q(Y) or exists Y (p(1,Y) and X > Y))",
                "Y",
                "a",
                "forall X (q(a) or exists Y (p(1,Y) and X > Y))",
            ),
            (
                "forall X (q(Y$i) or exists Z (p(1,Z) and X > Y$i > Z))",
                "Y$i",
                "4",
                "forall X (q(4) or exists Z (p(1,Z) and X > 4 > Z))",
            ),
            (
                "exists J$i (J$i = N$i and Z = Z1)",
                "Z",
                "I",
                "exists J$i (J$i = N$i and I = Z1)",
            ),
        ] {
            assert_eq!(
                src.parse::<Formula>()
                    .unwrap()
                    .substitute(var.parse().unwrap(), term.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }
}
