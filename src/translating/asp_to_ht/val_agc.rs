use indexmap::IndexSet;

use crate::{
    syntax_tree::{
        asp::{self, PrecomputedTerm, Term},
        fol::{self, Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier, Sort},
    },
    translating::asp_to_ht::basics::{
        choose_fresh_ijk, construct_equality_formula, construct_interval_formula,
        construct_total_function_formula, variable_to_general_term,
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
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: fol::Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
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
        term: i_times_j,
        guards: vec![Guard {
            relation: fol::Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // Z = -K
    let z_equals_neg_k = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: variable_to_general_term(z),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                op: fol::UnaryOperator::Negative,
                arg: IntegerTerm::Variable(k.name).into(),
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
        term: i_times_j.clone(),
        guards: vec![Guard {
            relation: fol::Relation::GreaterEqual,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
        }],
    }));

    // I * J < 0
    let ij_less_zero = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: i_times_j,
        guards: vec![Guard {
            relation: fol::Relation::Less,
            term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(0)),
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
pub(crate) fn val(
    t: asp::Term,
    z: fol::Variable,
    taken_variables: IndexSet<fol::Variable>,
) -> Formula {
    let mut taken_variables: IndexSet<fol::Variable> = IndexSet::from_iter(taken_variables);
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
            asp::UnaryOperator::AbsoluteValue => {
                let valti = val(*arg, fresh_int_vars["I"].clone(), taken_variables.clone()); // val_t1(I)
                construct_absolute_value_formula(valti, fresh_int_vars["I"].clone(), z)
            }
        },
        Term::BinaryOperation { op, lhs, rhs } => {
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
pub(crate) fn valtz(mut terms: Vec<asp::Term>, mut variables: Vec<fol::Variable>) -> fol::Formula {
    fol::Formula::conjoin(
        terms
            .drain(..)
            .zip(variables.drain(..))
            .map(|(t, z)| val(t, z, IndexSet::new())),
    )
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
