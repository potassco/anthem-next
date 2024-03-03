use {
    crate::syntax_tree::{asp, fol},
    lazy_static::lazy_static,
    regex::Regex,
    std::collections::HashSet,
};

lazy_static! {
    static ref RE: Regex = Regex::new(r"^V(?<number>[0-9]*)$").unwrap();
}

/// Choose fresh variants of `Vn` by incrementing `n`
fn choose_fresh_global_variables(program: &asp::Program) -> Vec<String> {
    let mut max_arity = 0;
    let mut head_arity;
    for rule in program.rules.iter() {
        head_arity = rule.head.arity();
        if head_arity > max_arity {
            max_arity = head_arity;
        }
    }
    let mut max_taken_var = 0;
    let taken_vars = program.variables();
    for var in taken_vars {
        if let Some(caps) = RE.captures(&var.0) {
            let taken: usize = (caps["number"]).parse().unwrap_or(0);
            if taken > max_taken_var {
                max_taken_var = taken;
            }
        }
    }
    let mut globals = Vec::<String>::new();
    for i in 1..max_arity + 1 {
        let mut v: String = "V".to_owned();
        let counter: &str = &(max_taken_var + i).to_string();
        v.push_str(counter);
        globals.push(v);
    }
    globals
}

/// Choose `arity` variable names by incrementing `variant`, disjoint from `variables`
fn choose_fresh_variable_names(
    variables: &HashSet<fol::Variable>,
    variant: &str,
    arity: usize,
) -> Vec<String> {
    let mut taken_vars = Vec::<String>::new();
    for var in variables.iter() {
        taken_vars.push(var.name.to_string());
    }
    let mut fresh_vars = Vec::<String>::new();
    let arity_bound = match taken_vars.contains(&variant.to_string()) {
        true => arity + 1,
        false => {
            fresh_vars.push(variant.to_string());
            arity
        }
    };
    for n in 1..arity_bound {
        let mut candidate: String = variant.to_owned();
        let number: &str = &n.to_string();
        candidate.push_str(number);
        let mut m = n;
        while taken_vars.contains(&candidate) || fresh_vars.contains(&candidate) {
            candidate = variant.to_owned();
            m += 1;
            let number = &m.to_string();
            candidate.push_str(number);
        }
        fresh_vars.push(candidate.to_string());
    }
    fresh_vars
}

// Z = t
fn construct_equality_formula(term: asp::Term, z: fol::Variable) -> fol::Formula {
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name),
        )),
    };

    let rhs = match term {
        asp::Term::PrecomputedTerm(t) => match t {
            asp::PrecomputedTerm::Infimum => fol::GeneralTerm::IntegerTerm(
                fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::Infimum),
            ),
            asp::PrecomputedTerm::Supremum => fol::GeneralTerm::IntegerTerm(
                fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::Supremum),
            ),
            asp::PrecomputedTerm::Numeral(i) => fol::GeneralTerm::IntegerTerm(
                fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::Numeral(i)),
            ),
            asp::PrecomputedTerm::Symbol(s) => fol::GeneralTerm::Symbol(s),
        },
        asp::Term::Variable(v) => fol::GeneralTerm::GeneralVariable(v.0),
        _ => panic!(), // Error
    };

    fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_var_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: rhs,
        }],
    }))
}

// +,-,*
// exists I J (Z = I op J & val_t1(I) & val_t2(J))
fn construct_total_function_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    binop: asp::BinaryOperator,
    i_var: fol::Variable,
    j_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    let i = i_var.name;
    let j = j_var.name;
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name),
        )),
    };
    let zequals = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        // Z = I binop J
        term: z_var_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                op: match binop {
                    asp::BinaryOperator::Add => fol::BinaryOperator::Add,
                    asp::BinaryOperator::Subtract => fol::BinaryOperator::Subtract,
                    asp::BinaryOperator::Multiply => fol::BinaryOperator::Multiply,
                    _ => panic!(), // More error handling
                },
                lhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
                    i.clone(),
                ))
                .into(),
                rhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
                    j.clone(),
                ))
                .into(),
            }),
        }],
    }));
    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![
                fol::Variable {
                    name: i,
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: j,
                    sort: fol::Sort::Integer,
                },
            ],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: zequals.into(),
                rhs: valti.into(),
            }
            .into(),
            rhs: valtj.into(),
        }
        .into(),
    }
}

// Assumes I,J,K are integer variables
// K * |J| <= |I| < (K+1) * |J|
// e.g. I is evenly divisible by J: K times
fn evenly_divisible(i: &fol::Variable, j: &fol::Variable, k: &fol::Variable) -> fol::Formula {
    let i_term =
        fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(i.name.clone()));
    let j_term =
        fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(j.name.clone()));
    let k_term =
        fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(k.name.clone()));

    let absi = fol::IntegerTerm::Function(fol::Function {
        symbol: fol::FunctionSymbol::AbsoluteValue,
        terms: vec![i_term],
    });
    let absj = fol::IntegerTerm::Function(fol::Function {
        symbol: fol::FunctionSymbol::AbsoluteValue,
        terms: vec![j_term],
    });

    let t1 = fol::IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: k_term.clone().into(),
        rhs: absj.clone().into(),
    };
    let t2 = fol::IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: fol::IntegerTerm::BinaryOperation {
            op: fol::BinaryOperator::Add,
            lhs: k_term.into(),
            rhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::Numeral(1)).into(),
        }
        .into(),
        rhs: absj.clone().into(),
    };

    fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(t1),
        guards: vec![
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: fol::GeneralTerm::IntegerTerm(absi),
            },
            fol::Guard {
                relation: fol::Relation::Less,
                term: fol::GeneralTerm::IntegerTerm(t2),
            },
        ],
    }))
}

// Assumes I, J, K are integer variables
// (I * J >= 0 & Z = K) | (I * J < 0 & Z = -K)
fn rounded_quotient(
    i: &fol::Variable,
    j: &fol::Variable,
    k: &fol::Variable,
    z: &fol::Variable,
) -> fol::Formula {
    let k_term =
        fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(k.name.clone()));
    let z_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name.clone()),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name.clone()),
        )),
    };

    // I * J
    let t1 = fol::IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
            i.name.clone(),
        ))
        .into(),
        rhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
            j.name.clone(),
        ))
        .into(),
    };

    // I * J >= 0
    let comp1 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(t1.clone()),
        guards: vec![fol::Guard {
            relation: fol::Relation::GreaterEqual,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                fol::BasicIntegerTerm::Numeral(0),
            )),
        }],
    }));

    // Z = K
    let comp2 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_term.clone(),
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(k_term.clone()),
        }],
    }));

    // I * J < 0
    let comp3 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(t1),
        guards: vec![fol::Guard {
            relation: fol::Relation::Less,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                fol::BasicIntegerTerm::Numeral(0),
            )),
        }],
    }));

    // Z = -K
    let comp4 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::UnaryOperation {
                op: fol::UnaryOperator::Negative,
                arg: k_term.into(),
            }),
        }],
    }));

    fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Disjunction,
        lhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: comp1.into(),
            rhs: comp2.into(),
        }
        .into(),
        rhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: comp3.into(),
            rhs: comp4.into(),
        }
        .into(),
    }
}

// (I * J >= 0 & Z = I - K * J) | (I * J < 0 & Z = I + K * J)
fn rounded_remainder(
    i: &fol::Variable,
    j: &fol::Variable,
    k: &fol::Variable,
    z: &fol::Variable,
) -> fol::Formula {
    let z_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name.clone()),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name.clone()),
        )),
    };

    // I * J
    let t1 = fol::IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
            i.name.clone(),
        ))
        .into(),
        rhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
            j.name.clone(),
        ))
        .into(),
    };

    // K * J
    let t2 = fol::IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
            k.name.clone(),
        ))
        .into(),
        rhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
            j.name.clone(),
        ))
        .into(),
    };

    // I * J >= 0
    let comp1 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(t1.clone()),
        guards: vec![fol::Guard {
            relation: fol::Relation::GreaterEqual,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                fol::BasicIntegerTerm::Numeral(0),
            )),
        }],
    }));

    // Z = I - K * J
    let comp2 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_term.clone(),
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                op: fol::BinaryOperator::Subtract,
                lhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
                    i.name.clone(),
                ))
                .into(),
                rhs: t2.clone().into(),
            }),
        }],
    }));

    // I * J < 0
    let comp3 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(t1),
        guards: vec![fol::Guard {
            relation: fol::Relation::Less,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                fol::BasicIntegerTerm::Numeral(0),
            )),
        }],
    }));

    // Z = I + K * J
    let comp4 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_term.clone(),
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                op: fol::BinaryOperator::Add,
                lhs: fol::IntegerTerm::BasicIntegerTerm(fol::BasicIntegerTerm::IntegerVariable(
                    i.name.clone(),
                ))
                .into(),
                rhs: t2.into(),
            }),
        }],
    }));

    fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Disjunction,
        lhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: comp1.into(),
            rhs: comp2.into(),
        }
        .into(),
        rhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: comp3.into(),
            rhs: comp4.into(),
        }
        .into(),
    }
}

// Division: exists I J K (val_t1(I) & val_t2(J) & evenly_divisible(I,J,K) & rounded_quotient(I,J,K,Z))
// Modulo:   exists I J K (val_t1(I) & val_t2(J) & evenly_divisible(I,J,K) & rounded_remainder(I,J,K,Z))
fn construct_partial_function_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    binop: asp::BinaryOperator,
    i_var: fol::Variable,
    j_var: fol::Variable,
    k_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    // val_t1(I) & val_t2(J)
    let inner_vals = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: valti.into(),
        rhs: valtj.into(),
    };

    // evenly_divisible(I,J,K) & rounded_quotient(I,J,K,Z)
    // OR
    // evenly_divisible(I,J,K) & rounded_remainder(I,J,K,Z)
    let subformula = match binop {
        asp::BinaryOperator::Divide => fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: evenly_divisible(&i_var, &j_var, &k_var).into(),
            rhs: rounded_quotient(&i_var, &j_var, &k_var, &z).into(),
        },
        asp::BinaryOperator::Modulo => fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: evenly_divisible(&i_var, &j_var, &k_var).into(),
            rhs: rounded_remainder(&i_var, &j_var, &k_var, &z).into(),
        },
        _ => panic!(),
    };

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![i_var, j_var, k_var],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: inner_vals.into(),
            rhs: subformula.into(),
        }
        .into(),
    }
}

// t1..t2
// exists I J K (val_t1(I) & val_t2(J) & I <= K <= J & Z = K)
fn construct_interval_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    i_var: fol::Variable,
    j_var: fol::Variable,
    k_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::GeneralVariable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(z.name),
        )),
    };

    // I <= K <= J
    let range = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
            fol::BasicIntegerTerm::IntegerVariable(i_var.name.clone()),
        )),
        guards: vec![
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(k_var.name.clone()),
                )),
            },
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(j_var.name.clone()),
                )),
            },
        ],
    }));

    // val_t1(I) & val_t2(J) & Z = k
    let subformula = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: valti.into(),
            rhs: valtj.into(),
        }
        .into(),
        rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: z_var_term,
            guards: vec![fol::Guard {
                relation: fol::Relation::Equal,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
                    fol::BasicIntegerTerm::IntegerVariable(k_var.name.clone()),
                )),
            }],
        }))
        .into(),
    };

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![i_var, j_var, k_var],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: subformula.into(),
            rhs: range.into(),
        }
        .into(),
    }
}

// val_t(Z)
fn val(t: asp::Term, z: fol::Variable) -> fol::Formula {
    let mut taken_vars = HashSet::<fol::Variable>::new();
    for var in t.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    taken_vars.insert(z.clone());

    let mut fresh_ivar = choose_fresh_variable_names(&taken_vars, "I", 1);
    let mut fresh_jvar = choose_fresh_variable_names(&taken_vars, "J", 1);
    let mut fresh_kvar = choose_fresh_variable_names(&taken_vars, "K", 1);

    // Fresh integer variables
    let var1 = fol::Variable {
        name: fresh_ivar.pop().unwrap(),
        sort: fol::Sort::Integer,
    };
    let var2 = fol::Variable {
        name: fresh_jvar.pop().unwrap(),
        sort: fol::Sort::Integer,
    };
    let var3 = fol::Variable {
        name: fresh_kvar.pop().unwrap(),
        sort: fol::Sort::Integer,
    };
    match t {
        asp::Term::PrecomputedTerm(_) | asp::Term::Variable(_) => construct_equality_formula(t, z),
        asp::Term::UnaryOperation { op, arg } => {
            match op {
                asp::UnaryOperator::Negative => {
                    let lhs = asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Numeral(0)); // Shorthand for 0 - t
                    let valti = val(lhs, var1.clone()); // val_t1(I)
                    let valtj = val(*arg, var2.clone()); // val_t2(J)
                    construct_total_function_formula(
                        valti,
                        valtj,
                        asp::BinaryOperator::Subtract,
                        var1,
                        var2,
                        z,
                    )
                }
            }
        }
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let valti = val(*lhs, var1.clone()); // val_t1(I)
            let valtj = val(*rhs, var2.clone()); // val_t2(J)
            match op {
                asp::BinaryOperator::Add => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Add,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Subtract => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Subtract,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Multiply => construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Multiply,
                    var1,
                    var2,
                    z,
                ),
                asp::BinaryOperator::Divide => construct_partial_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Divide,
                    var1,
                    var2,
                    var3,
                    z,
                ),
                asp::BinaryOperator::Modulo => construct_partial_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Modulo,
                    var1,
                    var2,
                    var3,
                    z,
                ),
                asp::BinaryOperator::Interval => {
                    construct_interval_formula(valti, valtj, var1, var2, var3, z)
                }
            }
        }
    }
}

// val_t1(Z1) & val_t2(Z2) & ... & val_tn(Zn)
fn valtz(mut terms: Vec<asp::Term>, mut variables: Vec<fol::Variable>) -> fol::Formula {
    fol::Formula::conjoin(
        terms
            .drain(..)
            .zip(variables.drain(..))
            .map(|(t, v)| val(t, v)),
    )
}

// Translate a first-order body literal
fn tau_b_first_order_literal(l: asp::Literal, taken_vars: HashSet<fol::Variable>) -> fol::Formula {
    let atom = l.atom;
    let terms = atom.terms;
    let arity = terms.len();
    let varnames = choose_fresh_variable_names(&taken_vars, "Z", arity);

    // Compute val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
    let mut var_terms: Vec<fol::GeneralTerm> = Vec::with_capacity(arity);
    let mut var_vars: Vec<fol::Variable> = Vec::with_capacity(arity);
    let mut valtz_vec: Vec<fol::Formula> = Vec::with_capacity(arity);
    for (i, t) in terms.iter().enumerate() {
        let var = fol::Variable {
            sort: fol::Sort::General,
            name: varnames[i].clone(),
        };
        valtz_vec.push(val(t.clone(), var.clone()));
        var_terms.push(fol::GeneralTerm::GeneralVariable(varnames[i].clone()));
        var_vars.push(var);
    }
    let valtz = fol::Formula::conjoin(valtz_vec);

    // Compute p(Z1, Z2, ..., Zk)
    let p_zk = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: atom.predicate_symbol,
        terms: var_terms,
    }));

    // Compute tau^b(B)
    match l.sign {
        asp::Sign::NoSign => fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Exists,
                variables: var_vars,
            },
            formula: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: valtz.into(),
                rhs: p_zk.into(),
            }
            .into(),
        },
        asp::Sign::Negation => fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Exists,
                variables: var_vars,
            },
            formula: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: valtz.into(),
                rhs: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: p_zk.into(),
                }
                .into(),
            }
            .into(),
        },
        asp::Sign::DoubleNegation => fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Exists,
                variables: var_vars,
            },
            formula: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: valtz.into(),
                rhs: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: fol::Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: p_zk.into(),
                    }
                    .into(),
                }
                .into(),
            }
            .into(),
        },
    }
}

// Translate a propositional body literal
fn tau_b_propositional_literal(l: asp::Literal) -> fol::Formula {
    let atom = l.atom;
    match l.sign {
        asp::Sign::NoSign => fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
            predicate_symbol: atom.predicate_symbol,

            terms: vec![],
        })),
        asp::Sign::Negation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol: atom.predicate_symbol,
                terms: vec![],
            }))
            .into(),
        },
        asp::Sign::DoubleNegation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                    predicate_symbol: atom.predicate_symbol,
                    terms: vec![],
                }))
                .into(),
            }
            .into(),
        },
    }
}

// Translate a body comparison
fn tau_b_comparison(c: asp::Comparison, taken_vars: HashSet<fol::Variable>) -> fol::Formula {
    let varnames = choose_fresh_variable_names(&taken_vars, "Z", 2);

    // Compute val_t1(Z1) & val_t2(Z2)
    let term_z1 = fol::GeneralTerm::GeneralVariable(varnames[0].clone());
    let term_z2 = fol::GeneralTerm::GeneralVariable(varnames[1].clone());
    let var_z1 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[0].clone(),
    };
    let var_z2 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[1].clone(),
    };
    let valtz = fol::Formula::conjoin(vec![val(c.lhs, var_z1.clone()), val(c.rhs, var_z2.clone())]);

    // Compute Z1 rel Z2
    let z1_rel_z2 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: term_z1,
        guards: vec![fol::Guard {
            relation: match c.relation {
                asp::Relation::Equal => fol::Relation::Equal,
                asp::Relation::NotEqual => fol::Relation::NotEqual,
                asp::Relation::Greater => fol::Relation::Greater,
                asp::Relation::Less => fol::Relation::Less,
                asp::Relation::GreaterEqual => fol::Relation::GreaterEqual,
                asp::Relation::LessEqual => fol::Relation::LessEqual,
            },
            term: term_z2,
        }],
    }));

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![var_z1, var_z2],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: valtz.into(),
            rhs: z1_rel_z2.into(),
        }
        .into(),
    }
}

// Translate a body literal or comparison
fn tau_b(f: asp::AtomicFormula) -> fol::Formula {
    let mut taken_vars = HashSet::<fol::Variable>::new();
    for var in f.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    match f {
        asp::AtomicFormula::Literal(l) => {
            let arity = l.atom.terms.len();
            if arity > 0 {
                tau_b_first_order_literal(l, taken_vars)
            } else {
                tau_b_propositional_literal(l)
            }
        }
        asp::AtomicFormula::Comparison(c) => tau_b_comparison(c, taken_vars),
    }
}

// Translate a rule body
fn tau_body(b: asp::Body) -> fol::Formula {
    let mut formulas = Vec::<fol::Formula>::new();
    for f in b.formulas.iter() {
        formulas.push(tau_b(f.clone()));
    }
    fol::Formula::conjoin(formulas)
}

// Handles the case when we have a rule with a first-order atom or choice atom in the head
fn tau_star_fo_head_rule(r: &asp::Rule, globals: &[String]) -> fol::Formula {
    let head_symbol = r.head.predicate().unwrap();
    let fol_head_predicate = fol::Predicate {
        symbol: head_symbol.symbol,
        arity: head_symbol.arity,
    };
    let head_arity = r.head.arity(); // n
    let fvars = &globals[0..head_arity]; // V, |V| = n
    let mut gvars = Vec::<fol::Variable>::new(); // G
    for var in r.variables().iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }

    let head_terms = r.head.terms().unwrap(); // Transform p(t) into p(V)
    let mut new_terms = Vec::<fol::GeneralTerm>::new();
    let mut fo_vars = Vec::<fol::Variable>::new();
    for (i, _) in head_terms.iter().enumerate() {
        let fol_var = fol::Variable {
            name: fvars[i].to_string(),
            sort: fol::Sort::General,
        };
        let fol_term = fol::GeneralTerm::GeneralVariable(fvars[i].to_string());
        fo_vars.push(fol_var);
        new_terms.push(fol_term);
    }
    let valtz = valtz(head_terms.to_vec(), fo_vars); // val_t(V)
    let new_head = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: fol_head_predicate.symbol,
        terms: new_terms,
    })); // p(V)
    let core_lhs = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: valtz.into(),
        rhs: tau_body(r.body.clone()).into(),
    };

    let new_body = match r.head {
        asp::Head::Basic(_) => core_lhs, // val_t(V) & tau^B(Body)
        asp::Head::Choice(_) => fol::Formula::BinaryFormula {
            // val_t(V) & tau^B(Body) & ~~p(V)
            connective: fol::BinaryConnective::Conjunction,
            lhs: core_lhs.into(),
            rhs: fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: new_head.clone().into(),
                }
                .into(),
            }
            .into(),
        },
        _ => panic!(),
    };
    let imp = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    }; // val_t(V) & tau^B(Body) -> p(V) OR val_t(V) & tau^B(Body) & ~~p(V) -> p(V)
    for var in fvars.iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }
    gvars.sort(); // TODO
    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Forall,
            variables: gvars,
        },
        formula: imp.into(),
    } // forall G V ( val_t(V) & tau^B(Body) -> p(V) ) OR forall G V ( val_t(V) & tau^B(Body) -> p(V) )
}

// Handles the case when we have a rule with a propositional atom or choice atom in the head
fn tau_star_prop_head_rule(r: &asp::Rule) -> fol::Formula {
    let head_symbol = r.head.predicate().unwrap();
    let fol_head_predicate = fol::Predicate {
        symbol: head_symbol.symbol,
        arity: head_symbol.arity,
    };
    let mut gvars = Vec::<fol::Variable>::new(); // G
    for var in r.variables().iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }
    let new_head = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: fol_head_predicate.symbol,
        terms: vec![],
    }));
    let core_lhs = tau_body(r.body.clone());
    let new_body = match &r.head {
        asp::Head::Basic(_) => {
            // tau^B(Body)
            core_lhs
        }
        asp::Head::Choice(_) => {
            // tau^B(Body) & ~~p
            fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: core_lhs.into(),
                rhs: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: fol::Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: new_head.clone().into(),
                    }
                    .into(),
                }
                .into(),
            }
        }
        asp::Head::Falsity => {
            panic!()
        }
    };

    let imp = fol::Formula::BinaryFormula {
        // tau^B(Body) -> p OR tau^B(Body) & ~~p -> p
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    };
    gvars.sort(); // TODO
    if !gvars.is_empty() {
        // forall G ( tau^B(Body) -> p ) OR forall G ( tau^B(Body) & ~~p -> p )
        fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Forall,
                variables: gvars,
            },
            formula: imp.into(),
        }
    } else {
        imp // tau^B(Body) -> p  OR tau^B(Body) & ~~p -> p
    }
}

// Handles the case when we have a rule with an empty head
fn tau_star_constraint_rule(r: &asp::Rule) -> fol::Formula {
    let mut gvars = Vec::<fol::Variable>::new();
    for var in r.variables().iter() {
        gvars.push(fol::Variable {
            sort: fol::Sort::General,
            name: var.to_string(),
        });
    }
    let imp = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: tau_body(r.body.clone()).into(),
        rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity).into(),
    }; // tau^B(Body) -> \bot
    gvars.sort(); // TODO
    if !gvars.is_empty() {
        fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Forall,
                variables: gvars,
            },
            formula: imp.into(),
        } // forall G ( tau^B(Body) -> \bot )
    } else {
        imp
    } // tau^B(Body) -> \bot
}

// Translate a rule using a pre-defined list of global variables
fn tau_star_rule(r: &asp::Rule, globals: &[String]) -> fol::Formula {
    match r.head.predicate() {
        Some(_) => {
            if r.head.arity() > 0 {
                // First-order head
                tau_star_fo_head_rule(r, globals)
            } else {
                // Propositional head
                tau_star_prop_head_rule(r)
            }
        }
        None => tau_star_constraint_rule(r),
    }
}

// For each rule, produce a formula: forall G V ( val_t(V) & tau_body(Body) -> p(V) )
// Where G is all variables from the original rule
// and V is the set of fresh variables replacing t within p
pub fn tau_star(p: asp::Program) -> fol::Theory {
    let globals = choose_fresh_global_variables(&p);
    let mut formulas: Vec<fol::Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
    for r in p.rules.iter() {
        formulas.push(tau_star_rule(r, &globals));
    }
    fol::Theory { formulas }
}

#[cfg(test)]
mod tests {
    use super::{tau_b, val};

    #[test]
    fn test_val() {
        for (term, var, target) in [
            ("X + 1", "Z1", "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)"),
            ("3 - 5", "Z1", "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and J$i = 5)"),
            ("3/15", "Z1", "exists I$ J$ K$ (I$ = 3 and J$ = 15 and (( K$ * abs(J$) <= abs(I$) < (K$ +1) * abs(J$) ) and ((I$ * J$ >= 0 and Z1 = K$) or (I$ * J$ < 0 and Z1 = -K$))))"),
            ("3\\15", "Z1", "exists I$ J$ K$ (I$ = 3 and J$ = 15 and (( K$ * abs(J$) <= abs(I$) < (K$ +1) * abs(J$) ) and ((I$ * J$ >= 0 and Z1 = I$ - K$ * J$) or (I$ * J$ < 0 and Z1 = I$ + K$ * J$))))"),
            ("X..Y", "Z", "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)"),
            ("X+1..Y", "Z1", "exists I$i J$i K$i ((exists I1$i J$i (I$i = I1$i + J$i and I1$i = X and J$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i)"),
        ] {
            let left = val(term.parse().unwrap(), var.parse().unwrap());
            let right = target.parse().unwrap();
            assert_eq!(
                left,
                right,
                "{left} \n != \n {right}"
            )
        }
    }

    #[test]
    fn test_tau_b() {
        for (src, target) in [
            ("p(t)", "exists Z (Z = t and p(Z))"),
            ("not p(t)", "exists Z (Z = t and not p(Z))"),
            ("X < 1..5", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and Z < Z1)"),
            ("not not p(t)", "exists Z (Z = t and not not p(Z))"),
            ("not not x", "not not x"),
            ("not p(X,5)", "exists Z Z1 (Z = X and Z1 = 5 and not p(Z,Z1))"),
            ("not p(X,0-5)", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and J$i = 5) and not p(Z,Z1))"),
            ("p(X,-1..5)", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = -1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and p(Z,Z1))"),
            ("p(X,-(1..5))", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and exists I$i J1$i K$i (I$i = 1 and J1$i = 5  and J$i = K$i and I$i <= K$i <= J1$i)) and p(Z,Z1))")
        ] {
            assert_eq!(
                tau_b(src.parse().unwrap()),
                target.parse().unwrap(),
            )
        }
    }
}
