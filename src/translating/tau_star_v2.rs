use indexmap::IndexSet;

use crate::{
    syntax_tree::{
        asp::{self, ConditionalHead, PrecomputedTerm, Term},
        fol::{self, Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier, Sort},
    },
    translating::tau_star_basics::{
        choose_fresh_global_variables, choose_fresh_ijk, choose_fresh_variable_names,
        construct_equality_formula, construct_interval_formula, construct_total_function_formula,
        variable_to_general_term,
    },
};

// |t|
// exists I$ (Z = I$ & val_t(I$))
fn construct_absolute_value_formula(
    valti: Formula,
    i_var: fol::Variable,
    z: fol::Variable,
) -> Formula {
    let z_var_term = variable_to_general_term(z);

    // Z = |I|
    let zequals = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_var_term,
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: fol::UnaryOperator::AbsoluteValue,
                arg: IntegerTerm::Variable(i_var.name.clone()).into(),
            }),
        }],
    }));

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var],
        },
        formula: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: zequals.into(),
            rhs: valti.into(),
        }
        .into(),
    }
}

// I,J,K must be integer variables
// K * |J| <= |I| < (K+1) * |J|
fn division_helper_f1(i: fol::Variable, j: fol::Variable, k: fol::Variable) -> Formula {
    // K * |J|
    let term1 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::UnaryOperation {
            op: fol::UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    // |I|
    let term2 = GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
        op: fol::UnaryOperator::AbsoluteValue,
        arg: IntegerTerm::Variable(i.name.clone()).into(),
    });

    // (K+1) * |J|
    let term3 = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::BinaryOperation {
            op: fol::BinaryOperator::Add,
            lhs: IntegerTerm::Variable(k.name.clone()).into(),
            rhs: IntegerTerm::Numeral(1).into(),
        }
        .into(),
        rhs: IntegerTerm::UnaryOperation {
            op: fol::UnaryOperator::AbsoluteValue,
            arg: IntegerTerm::Variable(j.name.clone()).into(),
        }
        .into(),
    });

    Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: term1,
        guards: vec![
            Guard {
                relation: fol::Relation::LessEqual,
                term: term2,
            },
            Guard {
                relation: fol::Relation::Less,
                term: term3,
            },
        ],
    }))
}

// (I * J >= 0 & Z = K) v (I * J < 0 & Z = -K)
fn division_helper_f2(
    i: fol::Variable, // Must be an integer variable
    j: fol::Variable, // Must be an integer variable
    k: fol::Variable, // Must be an integer variable
    z: fol::Variable, // Must be a general variable
) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j.clone().into(),
        guards: vec![Guard {
            relation: fol::Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)).into(),
        }],
    }));

    // Z = K
    let z_equals_k = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: variable_to_general_term(z.clone()),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k.name.clone())),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j.into(),
        guards: vec![Guard {
            relation: fol::Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)).into(),
        }],
    }));

    // Z = -K
    let z_equals_neg_k = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: variable_to_general_term(z),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: fol::UnaryOperator::Negative,
                arg: IntegerTerm::Variable(k.name.into()).into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: fol::BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_k.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_neg_k.into(),
        }
        .into(),
    }
}

// (I * J >= 0 & Z = I - K * J) v (I * J < 0 & Z = I + K * J)
fn division_helper_f3(
    i: fol::Variable,
    j: fol::Variable,
    k: fol::Variable,
    z: fol::Variable,
) -> Formula {
    // I * J
    let i_times_j = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(i.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    });

    // I * J >= 0
    let ij_geq_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j.clone().into(),
        guards: vec![Guard {
            relation: fol::Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)).into(),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j.into(),
        guards: vec![Guard {
            relation: fol::Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)).into(),
        }],
    }));

    // K * J
    let k_times_j = IntegerTerm::BinaryOperation {
        op: fol::BinaryOperator::Multiply,
        lhs: IntegerTerm::Variable(k.name.clone()).into(),
        rhs: IntegerTerm::Variable(j.name.clone()).into(),
    };

    // Z = I - K * J
    let z_equals_i_minus =
        Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: variable_to_general_term(z.clone()),
            guards: vec![Guard {
                relation: fol::Relation::Equal,
                term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Subtract,
                    lhs: IntegerTerm::Variable(i.name.clone()).into(),
                    rhs: k_times_j.clone().into(),
                }),
            }],
        }));

    // Z = I + K * J
    let z_equals_i_plus = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: variable_to_general_term(z.clone()),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: fol::BinaryOperator::Add,
                lhs: IntegerTerm::Variable(i.name.clone()).into(),
                rhs: k_times_j.into(),
            }),
        }],
    }));

    Formula::BinaryFormula {
        connective: fol::BinaryConnective::Disjunction,
        lhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_geq_zero.into(),
            rhs: z_equals_i_minus.into(),
        }
        .into(),
        rhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: ij_less_zero.into(),
            rhs: z_equals_i_plus.into(),
        }
        .into(),
    }
}

// Abstract Gringo compliant integer division and modulo.
// Follows Locally Tight Programs (2023), Conditional literals drafts (2024)
// Division: exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F2(IJKZ))
// Modulo:   exists I J K (val_t1(I) & val_t2(J) & F1(IJK) & F3(IJKZ))
fn construct_partial_function_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    binop: asp::BinaryOperator,
    i: fol::Variable,
    j: fol::Variable,
    k: fol::Variable,
    z: fol::Variable,
) -> Formula {
    assert_eq!(i.sort, Sort::Integer);
    assert_eq!(j.sort, Sort::Integer);
    assert_eq!(k.sort, Sort::Integer);
    assert_eq!(z.sort, Sort::General);

    let f1 = division_helper_f1(i.clone(), j.clone(), k.clone());

    let f = match binop {
        asp::BinaryOperator::Divide => division_helper_f2(i.clone(), j.clone(), k.clone(), z),
        asp::BinaryOperator::Modulo => division_helper_f3(i.clone(), j.clone(), k.clone(), z),
        _ => unreachable!("division and modulo are the only supported partial functions"),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i, j, k],
        },
        formula: Formula::conjoin([valti, valtj, f1, f]).into(),
    }
}

// val_t(Z)
fn val(t: asp::Term, z: fol::Variable, taken_variables: IndexSet<fol::Variable>) -> Formula {
    let mut taken_variables: IndexSet<fol::Variable> =
        IndexSet::from_iter(taken_variables.into_iter());
    taken_variables.insert(z.clone());
    for var in t.variables().iter() {
        taken_variables.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }

    let taken_var_copy = taken_variables.clone();
    let fresh_int_vars = choose_fresh_ijk(&taken_var_copy);

    for (_, value) in fresh_int_vars.iter() {
        taken_variables.insert(value.clone());
    }

    match t {
        Term::PrecomputedTerm(_) | Term::Variable(_) => construct_equality_formula(t, z),
        Term::UnaryOperation { op, arg } => match op {
            asp::UnaryOperator::Negative => {
                let lhs = Term::PrecomputedTerm(PrecomputedTerm::Numeral(0)); // Shorthand for 0 - t
                let valti = val(lhs, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
                let valtj = val(*arg, fresh_int_vars["J"].clone(), taken_variables); // val_t2(J)
                construct_total_function_formula(
                    valti,
                    valtj,
                    asp::BinaryOperator::Subtract,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    z,
                )
            }
        },
        Term::BinaryOperation { op, lhs, rhs } => {
            let i = fresh_int_vars["I"].clone();
            let j = fresh_int_vars["J"].clone();

            let valti = val(*lhs, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
            let valtj = val(*rhs, fresh_int_vars["J"].clone(), taken_variables); // val_t2(J)
            match op {
                asp::BinaryOperator::Add
                | asp::BinaryOperator::Subtract
                | asp::BinaryOperator::Multiply => construct_total_function_formula(
                    valti,
                    valtj,
                    op,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    z,
                ),
                asp::BinaryOperator::Divide | asp::BinaryOperator::Modulo => {
                    construct_partial_function_formula(
                        valti,
                        valtj,
                        op,
                        fresh_int_vars["I"].clone(),
                        fresh_int_vars["J"].clone(),
                        fresh_int_vars["K"].clone(),
                        z,
                    )
                }
                asp::BinaryOperator::Interval => construct_interval_formula(
                    valti,
                    valtj,
                    fresh_int_vars["I"].clone(),
                    fresh_int_vars["J"].clone(),
                    fresh_int_vars["K"].clone(),
                    z,
                ),
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
            .map(|(t, v)| val(t, v, IndexSet::new())),
    )
}

// Translate a first-order body literal
pub(crate) fn tau_b_first_order_literal(
    l: asp::Literal,
    taken_vars: IndexSet<fol::Variable>,
) -> fol::Formula {
    let terms = l.atom.terms;
    let arity = terms.len();
    let varnames = choose_fresh_variable_names(&taken_vars, "Z", arity);

    // val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
    let mut var_terms: Vec<fol::GeneralTerm> = Vec::with_capacity(arity);
    let mut var_vars: Vec<fol::Variable> = Vec::with_capacity(arity);
    let mut valtz_vec: Vec<fol::Formula> = Vec::with_capacity(arity);
    for (i, t) in terms.iter().enumerate() {
        let var = fol::Variable {
            sort: fol::Sort::General,
            name: varnames[i].clone(),
        };
        valtz_vec.push(val(t.clone(), var.clone(), taken_vars.clone()));
        var_terms.push(fol::GeneralTerm::Variable(varnames[i].clone()));
        var_vars.push(var);
    }
    let valtz = fol::Formula::conjoin(valtz_vec);

    // p(Z1, Z2, ..., Zk)
    let p_zk = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: l.atom.predicate_symbol,
        terms: var_terms,
    }));

    // tau^b(B)
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
    match l.sign {
        asp::Sign::NoSign => fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
            predicate_symbol: l.atom.predicate_symbol,

            terms: vec![],
        })),
        asp::Sign::Negation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol: l.atom.predicate_symbol,
                terms: vec![],
            }))
            .into(),
        },
        asp::Sign::DoubleNegation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                    predicate_symbol: l.atom.predicate_symbol,
                    terms: vec![],
                }))
                .into(),
            }
            .into(),
        },
    }
}

// Translate a body comparison
fn tau_b_comparison(c: asp::Comparison, taken_vars: IndexSet<fol::Variable>) -> fol::Formula {
    let varnames = choose_fresh_variable_names(&taken_vars, "Z", 2);

    // Compute val_t1(Z1) & val_t2(Z2)
    let term_z1 = GeneralTerm::Variable(varnames[0].clone());
    let term_z2 = GeneralTerm::Variable(varnames[1].clone());
    let var_z1 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[0].clone(),
    };
    let var_z2 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[1].clone(),
    };
    let valtz = Formula::conjoin(vec![
        val(c.lhs, var_z1.clone(), taken_vars.clone()),
        val(c.rhs, var_z2.clone(), taken_vars),
    ]);

    // Compute Z1 rel Z2
    let z1_rel_z2 = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: term_z1,
        guards: vec![fol::Guard {
            relation: fol::Relation::from(c.relation),
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

#[cfg(test)]
mod tests {
    //use indexmap::IndexSet;
    use super::valtz;

    #[test]
    fn test_valtz() {
        for (term, var, target) in [
            (
                "X + 1",
                "Z1",
                "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)",
            ),
            ("3 - (1..5)", "Z1", "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and exists I1$i J1$i K1$i (I1$i = 1 and J1$i = 5 and J$i = K1$i and I1$i <= K1$i <= J1$i))"),
            //("1/0", "Z", "exists I$i J$i K$i (I$i = 1 and J$i = 0 and (K$i * #abs()) and ())"),
            // ("X \\ 3", "Z1", "exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = X and J$i = 3) and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z1$g = R$i)"),
            // ("X..Y", "Z", "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)"),
            // ("X+1..Y", "Z1", "exists I$i J$i K$i ((exists I1$i J$i (I$i = I1$i + J$i and I1$i = X and J$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i)"),
        ] {
            let left = valtz(vec![term.parse().unwrap()], vec![var.parse().unwrap()]);
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
