use {
    crate::{
        formatting::{Associativity, Precedence},
        syntax_tree::{
            fol::{
                Atom, AtomicFormula, BasicIntegerTerm, BinaryConnective, BinaryOperator,
                Comparison, Formula, Function, FunctionSymbol, GeneralTerm, Guard, IntegerTerm,
                Predicate, Quantification, Quantifier, Relation, Sort, Theory, UnaryConnective,
                UnaryOperator, Variable,
            },
            Node,
        },
    },
    std::fmt::{self, Display, Formatter},
};

pub struct Format<'a, N: Node>(pub &'a N);

impl Display for Format<'_, BasicIntegerTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BasicIntegerTerm::Infimum => write!(f, "#inf"),
            BasicIntegerTerm::Supremum => write!(f, "#sup"),
            BasicIntegerTerm::Numeral(n) => write!(f, "{n}"),
            BasicIntegerTerm::IntegerVariable(s) => write!(f, "{s}$i"),
        }
    }
}

impl Display for Format<'_, UnaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryOperator::Negative => write!(f, "-"),
        }
    }
}

impl Display for Format<'_, FunctionSymbol> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            FunctionSymbol::AbsoluteValue => write!(f, "abs"),
        }
    }
}

impl Display for Format<'_, BinaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryOperator::Add => write!(f, "+"),
            BinaryOperator::Subtract => write!(f, "-"),
            BinaryOperator::Multiply => write!(f, "*"),
        }
    }
}

impl Format<'_, IntegerTerm> {}

impl Precedence for Format<'_, IntegerTerm> {
    fn precedence(&self) -> usize {
        match self.0 {
            IntegerTerm::Function(_) => 0,
            IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1..)) => 2,
            IntegerTerm::UnaryOperation {
                op: UnaryOperator::Negative,
                ..
            }
            | IntegerTerm::BasicIntegerTerm(_) => 1,
            IntegerTerm::BinaryOperation {
                op: BinaryOperator::Multiply,
                ..
            } => 3,
            IntegerTerm::BinaryOperation {
                op: BinaryOperator::Add | BinaryOperator::Subtract,
                ..
            } => 4,
        }
    }

    fn associativity(&self) -> Associativity {
        Associativity::Left
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            IntegerTerm::Function(Function { symbol, .. }) => write!(f, "{}", Format(symbol)),
            IntegerTerm::UnaryOperation { op, .. } => write!(f, "{}", Format(op)),
            IntegerTerm::BinaryOperation { op, .. } => write!(f, " {} ", Format(op)),
            IntegerTerm::BasicIntegerTerm(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, IntegerTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            IntegerTerm::BasicIntegerTerm(t) => Format(t).fmt(f),
            IntegerTerm::Function(fun) => match fun.symbol {
                FunctionSymbol::AbsoluteValue => self.fmt_unary(Format(&fun.terms[0]), f),
            },
            IntegerTerm::UnaryOperation { arg, .. } => self.fmt_unary(Format(arg.as_ref()), f),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

impl Display for Format<'_, GeneralTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            GeneralTerm::Symbol(s) => write!(f, "{s}"),
            GeneralTerm::GeneralVariable(v) => write!(f, "{v}"),
            GeneralTerm::IntegerTerm(t) => Format(t).fmt(f),
        }
    }
}

impl Display for Format<'_, Predicate> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let symbol = &self.0.symbol;
        let arity = &self.0.arity;
        write!(f, "{symbol}/{arity}")
    }
}

impl Display for Format<'_, Atom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let predicate = &self.0.predicate_symbol;
        let terms = &self.0.terms;

        write!(f, "{predicate}")?;

        if !terms.is_empty() {
            let mut iter = terms.iter().map(Format);
            write!(f, "({}", iter.next().unwrap())?;
            for term in iter {
                write!(f, ", {term}")?;
            }
            write!(f, ")")?;
        }

        Ok(())
    }
}

// TODO - zero-arity function constants shouldn't be supported
impl Display for Format<'_, Function> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let function = &self.0.symbol;
        let terms = &self.0.terms;

        write!(f, "{function}")?;

        if !terms.is_empty() {
            let mut iter = terms.iter().map(Format);
            write!(f, "({}", iter.next().unwrap())?;
            for term in iter {
                write!(f, ", {term}")?;
            }
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, Relation> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Relation::Equal => write!(f, "="),
            Relation::NotEqual => write!(f, "!="),
            Relation::GreaterEqual => write!(f, ">="),
            Relation::LessEqual => write!(f, "<="),
            Relation::Greater => write!(f, ">"),
            Relation::Less => write!(f, "<"),
        }
    }
}

impl Display for Format<'_, Guard> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", Format(&self.0.relation), Format(&self.0.term))
    }
}

impl Display for Format<'_, Comparison> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let guards = &self.0.guards;

        write!(f, "{}", Format(&self.0.term))?;

        let iter = guards.iter().map(Format);
        for guard in iter {
            write!(f, " {guard}")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, AtomicFormula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            AtomicFormula::Truth => write!(f, "#true"),
            AtomicFormula::Falsity => write!(f, "#false"),
            AtomicFormula::Atom(a) => Format(a).fmt(f),
            AtomicFormula::Comparison(c) => Format(c).fmt(f),
        }
    }
}

impl Display for Format<'_, Quantifier> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Quantifier::Forall => write!(f, "forall"),
            Quantifier::Exists => write!(f, "exists"),
        }
    }
}

impl Display for Format<'_, Variable> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let sort = &self.0.sort;

        match sort {
            Sort::General => write!(f, "{name}"),
            Sort::Integer => write!(f, "{name}$i"),
        }
    }
}

impl Display for Format<'_, Quantification> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let quantifier = &self.0.quantifier;
        let variables = &self.0.variables;

        match quantifier {
            Quantifier::Forall => write!(f, "forall"),
            Quantifier::Exists => write!(f, "exists"),
        }?;

        let iter = variables.iter().map(Format);
        for var in iter {
            write!(f, " {var}")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, UnaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryConnective::Negation => write!(f, "not"),
        }
    }
}

impl Display for Format<'_, BinaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryConnective::Equivalence => write!(f, "<->"),
            BinaryConnective::Implication => write!(f, "->"),
            BinaryConnective::ReverseImplication => write!(f, "<-"),
            BinaryConnective::Conjunction => write!(f, "and"),
            BinaryConnective::Disjunction => write!(f, "or"),
        }
    }
}

impl Precedence for Format<'_, Formula> {
    fn precedence(&self) -> usize {
        match self.0 {
            Formula::AtomicFormula(_) => 0,
            Formula::UnaryFormula { .. } | Formula::QuantifiedFormula { .. } => 1,
            Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                ..
            } => 2,
            Formula::BinaryFormula {
                connective: BinaryConnective::Disjunction,
                ..
            } => 3,
            Formula::BinaryFormula {
                connective:
                    BinaryConnective::Equivalence
                    | BinaryConnective::Implication
                    | BinaryConnective::ReverseImplication,
                ..
            } => 4,
        }
    }

    fn associativity(&self) -> Associativity {
        match self.0 {
            Formula::UnaryFormula { .. }
            | Formula::QuantifiedFormula { .. }
            | Formula::BinaryFormula {
                connective:
                    BinaryConnective::Conjunction
                    | BinaryConnective::Disjunction
                    | BinaryConnective::ReverseImplication,
                ..
            } => Associativity::Left,
            Formula::BinaryFormula {
                connective: BinaryConnective::Equivalence | BinaryConnective::Implication,
                ..
            } => Associativity::Right,
            Formula::AtomicFormula(_) => unreachable!(),
        }
    }

    fn mandatory_parentheses(&self) -> bool {
        matches!(
            self.0,
            Formula::BinaryFormula {
                connective: BinaryConnective::Equivalence
                    | BinaryConnective::Implication
                    | BinaryConnective::ReverseImplication,
                ..
            }
        )
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::UnaryFormula { connective, .. } => write!(f, "{} ", Format(connective)),
            Formula::QuantifiedFormula { quantification, .. } => {
                write!(f, "{} ", Format(quantification))
            }
            Formula::BinaryFormula { connective, .. } => write!(f, " {} ", Format(connective)),
            Formula::AtomicFormula(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, Formula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::AtomicFormula(a) => Format(a).fmt(f),
            Formula::UnaryFormula { formula, .. } => self.fmt_unary(Format(formula.as_ref()), f),
            Formula::QuantifiedFormula { formula, .. } => {
                self.fmt_unary(Format(formula.as_ref()), f)
            }
            Formula::BinaryFormula { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

impl Display for Format<'_, Theory> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let formulas = &self.0.formulas;
        let iter = formulas.iter().map(Format);
        for form in iter {
            writeln!(f, "{form}.")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        formatting::fol::default::Format,
        syntax_tree::fol::{
            Atom, AtomicFormula, BasicIntegerTerm, BinaryConnective, BinaryOperator, Comparison,
            Formula, Function, FunctionSymbol, GeneralTerm, Guard, IntegerTerm, Quantification,
            Quantifier, Relation, Sort, UnaryConnective, Variable,
        },
    };

    #[test]
    fn format_basic_integer_term() {
        assert_eq!(Format(&BasicIntegerTerm::Infimum).to_string(), "#inf");
        assert_eq!(Format(&BasicIntegerTerm::Numeral(-1)).to_string(), "-1");
        assert_eq!(Format(&BasicIntegerTerm::Numeral(0)).to_string(), "0");
        assert_eq!(Format(&BasicIntegerTerm::Numeral(42)).to_string(), "42");
        assert_eq!(
            Format(&BasicIntegerTerm::IntegerVariable("A".into())).to_string(),
            "A$i"
        );
        assert_eq!(Format(&BasicIntegerTerm::Supremum).to_string(), "#sup");
    }

    #[test]
    fn format_general_term() {
        assert_eq!(
            Format(&GeneralTerm::IntegerTerm(
                IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable("N".into())).into()
            ))
            .to_string(),
            "N$i"
        );
        assert_eq!(
            Format(&GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Subtract,
                lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(3)).into(),
                rhs: IntegerTerm::Function(Function {
                    symbol: FunctionSymbol::AbsoluteValue,
                    terms: vec![IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(-1))],
                })
                .into()
            }))
            .to_string(),
            "3 - abs(-1)"
        );
        assert_eq!(
            Format(&GeneralTerm::Symbol("abc".into())).to_string(),
            "abc"
        );
        assert_eq!(
            Format(&GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: BinaryOperator::Multiply,
                lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(5)).into(),
            }))
            .to_string(),
            "1 * 5"
        );
    }

    #[test]
    fn format_comparison() {
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                    BasicIntegerTerm::Numeral(1)
                )),
                guards: vec![Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                        BasicIntegerTerm::Numeral(5)
                    )),
                }]
            })
            .to_string(),
            "1 < 5"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                    BasicIntegerTerm::IntegerVariable("N".into())
                )),
                guards: vec![
                    Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::Numeral(5)
                        )),
                    },
                    Guard {
                        relation: Relation::NotEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(7)).into(),
                            rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(2)).into(),
                        }),
                    },
                    Guard {
                        relation: Relation::GreaterEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::IntegerVariable("Xa".into())
                        )),
                    },
                ]
            })
            .to_string(),
            "N$i < 5 != 7 * 2 >= Xa$i"
        );
    }

    #[test]
    fn format_quantification() {
        assert_eq!(
            Format(&Quantification {
                quantifier: Quantifier::Forall,
                variables: vec![
                    Variable {
                        name: "X".into(),
                        sort: Sort::General,
                    },
                    Variable {
                        name: "Y".into(),
                        sort: Sort::Integer,
                    },
                    Variable {
                        name: "N".into(),
                        sort: Sort::General,
                    },
                ]
            })
            .to_string(),
            "forall X Y$i N"
        );
    }

    #[test]
    fn format_atomic_formula() {
        assert_eq!(
            Format(&AtomicFormula::Atom(Atom {
                predicate_symbol: "p".into(),
                terms: vec![
                    GeneralTerm::Symbol("a".into()),
                    GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                        BasicIntegerTerm::IntegerVariable("X".into())
                    )),
                ]
            }))
            .to_string(),
            "p(a, X$i)"
        );
        assert_eq!(
            Format(&AtomicFormula::Comparison(Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                    BasicIntegerTerm::Numeral(5)
                )),
                guards: vec![Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::GeneralVariable("I".into()),
                }]
            }))
            .to_string(),
            "5 < I"
        );
        assert_eq!(Format(&AtomicFormula::Falsity).to_string(), "#false");
    }

    #[test]
    fn format_formula() {
        assert_eq!(
            Format(&Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                predicate_symbol: "p".into(),
                terms: vec![]
            })))
            .to_string(),
            "p"
        );

        assert_eq!(
            Format(&Formula::UnaryFormula {
                connective: UnaryConnective::Negation,
                formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into()
            })
            .to_string(),
            "not p"
        );

        assert_eq!(
            Format(&Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: vec![Variable {
                        name: "X".into(),
                        sort: Sort::General
                    }]
                },
                formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![GeneralTerm::GeneralVariable("X".into())]
                }))
                .into()
            })
            .to_string(),
            "forall X p(X)"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "r".into(),
                    terms: vec![]
                }))
                .into(),
            })
            .to_string(),
            "(p <- q) <- r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p <- (q <- r)"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "r".into(),
                    terms: vec![]
                }))
                .into(),
            })
            .to_string(),
            "(p -> q) -> r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p -> (q -> r)"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "r".into(),
                    terms: vec![]
                }))
                .into(),
            })
            .to_string(),
            "(p -> q) <- r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p -> (q <- r)"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::ReverseImplication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "r".into(),
                    terms: vec![]
                }))
                .into(),
            })
            .to_string(),
            "(p <- q) -> r"
        );

        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::ReverseImplication,
                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![]
                }))
                .into(),
                rhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "r".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into()
            })
            .to_string(),
            "p <- (q -> r)"
        );
    }
}
