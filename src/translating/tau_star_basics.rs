use crate::syntax_tree::{
    asp::{self, PrecomputedTerm, Term},
    fol::{
        self, Formula, GeneralTerm, IntegerTerm, Quantification, Quantifier, Sort, SymbolicTerm,
    },
};

pub(crate) fn variable_to_general_term(variable: fol::Variable) -> GeneralTerm {
    match variable.sort {
        Sort::General => GeneralTerm::Variable(variable.name),
        Sort::Integer => GeneralTerm::IntegerTerm(IntegerTerm::Variable(variable.name)),
        Sort::Symbol => unreachable!("tau* should not produce variables of the Symbol sort"),
    }
}

// Z = t
pub(crate) fn construct_equality_formula(term: Term, z: fol::Variable) -> Formula {
    let z_var_term = variable_to_general_term(z);

    let rhs = match term {
        Term::PrecomputedTerm(t) => match t {
            PrecomputedTerm::Infimum => GeneralTerm::Infimum,
            PrecomputedTerm::Supremum => GeneralTerm::Supremum,
            PrecomputedTerm::Numeral(i) => GeneralTerm::IntegerTerm(IntegerTerm::Numeral(i)),
            PrecomputedTerm::Symbol(s) => GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol(s)),
        },
        Term::Variable(v) => GeneralTerm::Variable(v.0),
        _ => unreachable!(
            "equality should be between two variables or a variable and a precomputed term"
        ),
    };

    Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: z_var_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: rhs,
        }],
    }))
}

// +,-,*
// exists I J (Z = I op J & val_t1(I) & val_t2(J))
pub(crate) fn construct_total_function_formula(
    valti: Formula,
    valtj: Formula,
    binop: asp::BinaryOperator,
    i_var: fol::Variable,
    j_var: fol::Variable,
    z: fol::Variable,
) -> Formula {
    let i = i_var.name;
    let j = j_var.name;
    let z_var_term = variable_to_general_term(z);
    let zequals = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        // Z = I binop J
        term: z_var_term,
        guards: vec![fol::Guard {
            relation: fol::Relation::Equal,
            term: GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                op: match binop {
                    asp::BinaryOperator::Add => fol::BinaryOperator::Add,
                    asp::BinaryOperator::Subtract => fol::BinaryOperator::Subtract,
                    asp::BinaryOperator::Multiply => fol::BinaryOperator::Multiply,
                    _ => unreachable!("addition, subtraction and multiplication are the only supported total functions"),
                },
                lhs: fol::IntegerTerm::Variable(i.clone()).into(),
                rhs: fol::IntegerTerm::Variable(j.clone()).into(),
            }),
        }],
    }));
    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![
                fol::Variable {
                    name: i,
                    sort: Sort::Integer,
                },
                fol::Variable {
                    name: j,
                    sort: Sort::Integer,
                },
            ],
        },
        formula: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: Formula::BinaryFormula {
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

// t1..t2
// exists I J K (val_t1(I) & val_t2(J) & I <= K <= J & Z = K)
pub(crate) fn construct_interval_formula(
    valti: Formula,
    valtj: Formula,
    i_var: fol::Variable,
    j_var: fol::Variable,
    k_var: fol::Variable,
    z: fol::Variable,
) -> Formula {
    let z_var_term = variable_to_general_term(z);

    // I <= K <= J
    let range = Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(i_var.name.clone())),
        guards: vec![
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: GeneralTerm::IntegerTerm(fol::IntegerTerm::Variable(k_var.name.clone())),
            },
            fol::Guard {
                relation: fol::Relation::LessEqual,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(j_var.name.clone())),
            },
        ],
    }));

    // val_t1(I) & val_t2(J) & Z = k
    let subformula = Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: valti.into(),
            rhs: valtj.into(),
        }
        .into(),
        rhs: Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
            term: z_var_term,
            guards: vec![fol::Guard {
                relation: fol::Relation::Equal,
                term: GeneralTerm::IntegerTerm(IntegerTerm::Variable(k_var.name.clone())),
            }],
        }))
        .into(),
    };

    Formula::QuantifiedFormula {
        quantification: Quantification {
            quantifier: Quantifier::Exists,
            variables: vec![i_var, j_var, k_var],
        },
        formula: Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: subformula.into(),
            rhs: range.into(),
        }
        .into(),
    }
}
