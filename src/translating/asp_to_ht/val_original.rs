use indexmap::IndexSet;

use crate::{
    syntax_tree::{
        asp,
        fol::{self, Guard},
    },
    translating::asp_to_ht::basics::{
        choose_fresh_ijk, choose_fresh_variable_names, construct_equality_formula,
        construct_interval_formula, construct_total_function_formula,
    },
};

// Integer division. Not Abstract Gringo compliant in negative divisor edge cases.
// Follows the corrected arXiv paper (https://arxiv.org/abs/2008.02025), not the TPLP paper
// Division: exists I J Q R (I = J * Q + R & val_t1(I) & val_t2(J) & J != 0 & R >= 0 & R < J & Z = Q)
// Modulo:   exists I J Q R (I = J * Q + R & val_t1(I) & val_t2(J) & J != 0 & R >= 0 & R < J & Z = R)
fn construct_partial_function_formula(
    valti: fol::Formula,
    valtj: fol::Formula,
    binop: asp::BinaryOperator,
    i_var: fol::Variable,
    j_var: fol::Variable,
    z: fol::Variable,
) -> fol::Formula {
    let i = i_var.name;
    let j = j_var.name;

    let mut taken_vars = IndexSet::<fol::Variable>::new();
    for var in valti.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    for var in valtj.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }

    let z_var_term = match z.sort {
        fol::Sort::General => fol::GeneralTerm::Variable(z.name),
        fol::Sort::Integer => fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(z.name)),
        fol::Sort::Symbol => unreachable!("tau* should not produce variables of the Symbol sort"),
    };

    // I = J * Q + R
    let qvar = choose_fresh_variable_names(&taken_vars, "Q", 1)
        .pop()
        .unwrap();
    let rvar = choose_fresh_variable_names(&taken_vars, "R", 1)
        .pop()
        .unwrap();
    let iequals = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(i.clone())),
        guards: vec![Guard {
            relation: fol::Relation::Equal,
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BinaryOperation {
                op: fol::BinaryOperator::Add,
                lhs: fol::IntegerTerm::BinaryOperation {
                    op: fol::BinaryOperator::Multiply,
                    lhs: fol::IntegerTerm::Variable(j.clone()).into(),
                    rhs: fol::IntegerTerm::Variable(qvar.clone()).into(),
                }
                .into(),
                rhs: fol::IntegerTerm::Variable(rvar.clone()).into(),
            }),
        }],
    }));

    // J != 0 & R >= 0 & R < Q
    let conditions = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(j.clone())),
                guards: vec![Guard {
                    relation: fol::Relation::NotEqual,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(0)),
                }],
            }))
            .into(),
            rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(rvar.clone())),
                guards: vec![Guard {
                    relation: fol::Relation::GreaterEqual,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(0)),
                }],
            }))
            .into(),
        }
        .into(),
        rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(rvar.clone())),
            guards: vec![Guard {
                relation: fol::Relation::Less,
                term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(j.clone())),
            }],
        }))
        .into(),
    };

    // val_t1(I) & val_t2(J)
    let inner_vals = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: valti.into(),
        rhs: valtj.into(),
    };

    // (( I = J * Q + R ) & ( val_t1(I) & val_t2(J) )) & ( J != 0 & R >= 0 & R < Q )
    let subformula = {
        fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: iequals.into(),
                rhs: inner_vals.into(),
            }
            .into(),
            rhs: conditions.into(),
        }
    };

    // Z = Q or Z = R
    let zequals = match binop {
        asp::BinaryOperator::Divide => {
            fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: z_var_term,
                guards: vec![Guard {
                    relation: fol::Relation::Equal,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(qvar.clone())),
                }],
            }))
        }
        asp::BinaryOperator::Modulo => {
            fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                term: z_var_term,
                guards: vec![Guard {
                    relation: fol::Relation::Equal,
                    term: fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(rvar.clone())),
                }],
            }))
        }
        _ => unreachable!("division and modulo are the only supported partial functions"),
    };

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
                fol::Variable {
                    name: qvar,
                    sort: fol::Sort::Integer,
                },
                fol::Variable {
                    name: rvar,
                    sort: fol::Sort::Integer,
                },
            ],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: subformula.into(),
            rhs: zequals.into(),
        }
        .into(),
    }
}

// val_t(Z)
pub(crate) fn val(t: asp::Term, z: fol::Variable) -> fol::Formula {
    let mut taken_vars = IndexSet::<fol::Variable>::new();
    for var in t.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    taken_vars.insert(z.clone());

    let fresh_int_vars = choose_fresh_ijk(&taken_vars);

    match t {
        asp::Term::PrecomputedTerm(_) | asp::Term::Variable(_) => construct_equality_formula(t, z),
        asp::Term::UnaryOperation { op, arg } => {
            match op {
                asp::UnaryOperator::Negative => {
                    let lhs = asp::Term::PrecomputedTerm(asp::PrecomputedTerm::Numeral(0)); // Shorthand for 0 - t
                    let valti = val(lhs, fresh_int_vars["I"].clone()); // val_t1(I)
                    let valtj = val(*arg, fresh_int_vars["J"].clone()); // val_t2(J)
                    construct_total_function_formula(
                        valti,
                        valtj,
                        asp::BinaryOperator::Subtract,
                        fresh_int_vars["I"].clone(),
                        fresh_int_vars["J"].clone(),
                        z,
                    )
                }

                asp::UnaryOperator::AbsoluteValue => todo!(),
            }
        }
        asp::Term::BinaryOperation { op, lhs, rhs } => {
            let valti = val(*lhs, fresh_int_vars["I"].clone()); // val_t1(I)
            let valtj = val(*rhs, fresh_int_vars["J"].clone()); // val_t2(J)
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
            .map(|(t, v)| val(t, v)),
    )
}

#[cfg(test)]
mod tests {
    use super::val;

    #[test]
    fn test_val() {
        for (term, var, target) in [
            ("X + 1", "Z1", "exists I$i J$i (Z1$g = I$i + J$i and I$i = X and J$i = 1)"),
            ("3 - 5", "Z1", "exists I$i J$i (Z1$g = I$i - J$i and I$i = 3 and J$i = 5)"),
            ("Xanadu/Yak", "Z1", "exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = Xanadu and J$i = Yak) and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z1$g = Q$i)"),
            ("X \\ 3", "Z1", "exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = X and J$i = 3) and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z1$g = R$i)"),
            ("X..Y", "Z", "exists I$i J$i K$i (I$i = X and J$i = Y and Z$g = K$i and I$i <= K$i <= J$i)"),
            ("X+1..Y", "Z1", "exists I$i J$i K$i ((exists I1$i J$i (I$i = I1$i + J$i and I1$i = X and J$i = 1)) and J$i = Y and Z1 = K$i and I$i <= K$i <= J$i)"),
        ] {
            let left = val(term.parse().unwrap(), var.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
