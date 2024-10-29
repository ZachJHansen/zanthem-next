use crate::{
    syntax_tree::{
        asp::{self, ConditionalHead, Term},
        fol::{self, Formula, GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier, Sort},
    },
    translating::tau_star_basics::{
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

#[cfg(test)]
mod tests {
    //use indexmap::IndexSet;

    // #[test]
    // fn test_val() {}
}
