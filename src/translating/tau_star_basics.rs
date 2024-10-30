/*
* Helper functions for the tau-star family of translations
*/

use {
    crate::syntax_tree::{
        asp::{self, PrecomputedTerm, Program, Term},
        fol::{
            self, Formula, GeneralTerm, IntegerTerm, Quantification, Quantifier, Sort, SymbolicTerm,
        },
    },
    indexmap::{IndexMap, IndexSet},
    lazy_static::lazy_static,
    regex::Regex,
};

lazy_static! {
    static ref RE: Regex = Regex::new(r"^V(?<number>[0-9]*)$").unwrap();
}

/// Choose fresh variants of `Vn` by incrementing `n`
pub(crate) fn choose_fresh_global_variables(program: &Program) -> Vec<String> {
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
pub(crate) fn choose_fresh_variable_names(
    variables: &IndexSet<fol::Variable>,
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
            variant.clone_into(&mut candidate);
            m += 1;
            let number = &m.to_string();
            candidate.push_str(number);
        }
        fresh_vars.push(candidate.to_string());
    }
    fresh_vars
}

pub(crate) fn choose_fresh_ijk(
    taken_variables: &IndexSet<fol::Variable>,
) -> IndexMap<&str, fol::Variable> {
    let mut fresh_ivar = choose_fresh_variable_names(taken_variables, "I", 1);
    let mut fresh_jvar = choose_fresh_variable_names(taken_variables, "J", 1);
    let mut fresh_kvar = choose_fresh_variable_names(taken_variables, "K", 1);

    let mut fresh_int_vars = IndexMap::new();

    fresh_int_vars.insert(
        "I",
        fol::Variable {
            name: fresh_ivar.pop().unwrap(),
            sort: Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "J",
        fol::Variable {
            name: fresh_jvar.pop().unwrap(),
            sort: Sort::Integer,
        },
    );
    fresh_int_vars.insert(
        "K",
        fol::Variable {
            name: fresh_kvar.pop().unwrap(),
            sort: Sort::Integer,
        },
    );

    fresh_int_vars
}

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
