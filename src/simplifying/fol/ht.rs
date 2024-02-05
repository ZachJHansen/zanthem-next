use crate::{
    convenience::{
        apply::Apply as _,
        unbox::{fol::UnboxedFormula, Unbox as _},
    },
    syntax_tree::fol::{
        AtomicFormula, BasicIntegerTerm, BinaryConnective, Comparison, Formula, GeneralTerm,
        IntegerTerm, Quantification, Quantifier, Relation, Sort, Theory, Variable,
    },
};

pub fn simplify_theory(theory: Theory) -> Theory {
    //todo
    let mut formulas = theory.formulas;
    for i in 0..formulas.len() {
        formulas[i] = simplify(formulas[i].clone());
    }
    Theory { formulas }
}

pub fn simplify(formula: Formula) -> Formula {
    let mut f1 = formula;
    let mut f2;
    loop {
        f2 = simplify_redundant_quantifiers(simplify_empty_quantifiers(simplify_variable_lists(
            simplify_nested_quantifiers(basic_simplify(f1.clone())),
        )));
        if f1 == f2 {
            break;
        }
        f1 = f2;
    }
    f1
}

pub fn basic_simplify(formula: Formula) -> Formula {
    formula.apply(&mut basic_simplify_outer)
}

pub fn basic_simplify_outer(formula: Formula) -> Formula {
    // TODO: Split simplifications into multiple functions?

    match formula.unbox() {
        // Remove identities
        // e.g. F op E => F

        // F and #true => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Truth),
        } => lhs,

        // #true and F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Truth),
            rhs,
        } => rhs,

        // F or #false => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs,
            rhs: Formula::AtomicFormula(AtomicFormula::Falsity),
        } => lhs,

        // #false or F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs,
        } => rhs,

        // Remove annihilations
        // e.g. F op E => E

        // F or #true => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Truth),
        } => rhs,

        // #true or F => #true
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Disjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Truth),
            rhs: _,
        } => lhs,

        // F and #false => false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: _,
            rhs: rhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
        } => rhs,

        // #false and F => #false
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Falsity),
            rhs: _,
        } => lhs,

        // Remove idempotences
        // e.g. F op F => F

        // F and F => F
        // F or  F => F
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction | BinaryConnective::Disjunction,
            lhs,
            rhs,
        } if lhs == rhs => lhs,

        x => x.rebox(),
    }
}

pub fn simplify_nested_quantifiers(formula: Formula) -> Formula {
    formula.apply(&mut simplify_nested_quantifiers_outer)
}

pub fn simplify_nested_quantifiers_outer(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Join nested quantified formulas
        // e.g. exists X ( exists Y F(X,Y) ) => exists X Y F(X,Y)
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier,
                    mut variables,
                },
            formula:
                Formula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier: inner_quantifier,
                            variables: mut inner_vars,
                        },
                    formula: f,
                },
        } => {
            if quantifier == inner_quantifier {
                variables.append(&mut inner_vars);
                variables.sort();
                variables.dedup();
                Formula::QuantifiedFormula {
                    quantification: Quantification {
                        quantifier,
                        variables,
                    },
                    formula: f,
                }
            } else {
                formula
            }
        }

        x => x.rebox(),
    }
}

// ASSUMES formula has the form:
// exists X ( var = term & F(var) ) OR
// exists X ( term = var & F(var) )
// WHERE var occurs in variable list X
// If var is a variable of sort S and term is a domain element of S universe, return `exists X \ {var} F(term)`
// Otherwise, return the original formula
fn subsort_equality(var: Variable, term: GeneralTerm, formula: Formula, left: bool) -> Formula {
    match formula.clone().unbox() {
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    variables: mut vars,
                    ..
                },
            formula: Formula::BinaryFormula { rhs, lhs, .. },
        } => {
            let f;
            if left {
                f = lhs;
            } else {
                f = rhs;
            }
            match var.sort {
                Sort::General => {
                    vars.retain(|x| x != &var);
                    if vars.is_empty() {
                        f.substitute(var, term)
                    } else {
                        Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Exists,
                                variables: vars,
                            },
                            formula: f.substitute(var, term).into(),
                        }
                    }
                }
                Sort::Integer => match term.clone() {
                    GeneralTerm::IntegerTerm(_) => {
                        vars.retain(|x| x != &var);
                        if vars.is_empty() {
                            f.substitute(var, term)
                        } else {
                            Formula::QuantifiedFormula {
                                quantification: Quantification {
                                    quantifier: Quantifier::Exists,
                                    variables: vars,
                                },
                                formula: f.substitute(var, term).into(),
                            }
                        }
                    }
                    _ => formula,
                },
            }
        }
        _ => panic!("you're using the subsort equality fn wrong"),
    }
}

pub fn simplify_redundant_quantifiers(formula: Formula) -> Formula {
    formula.apply(&mut simplify_redundant_quantifiers_outer)
}

pub fn simplify_redundant_quantifiers_outer(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Remove redundant existentials
        // e.g. exists Z$g (Z$g = X$g and F(Z$g)) => F(X$g)
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: Quantifier::Exists,
                    variables,
                },
            formula: f,
        } => match f.clone().unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison { term, guards })),
                ..
            } => {
                let g = guards[0].clone();
                match g.relation {
                    Relation::Equal => {
                        let lhs_is_var = match term.clone() {
                            GeneralTerm::GeneralVariable(v) => Some(Variable {
                                sort: Sort::General,
                                name: v,
                            }),
                            GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::IntegerVariable(v),
                            )) => Some(Variable {
                                sort: Sort::Integer,
                                name: v,
                            }),
                            _ => None,
                        };
                        let rhs_is_var = match g.term.clone() {
                            GeneralTerm::GeneralVariable(v) => Some(Variable {
                                sort: Sort::General,
                                name: v,
                            }),
                            GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::IntegerVariable(v),
                            )) => Some(Variable {
                                sort: Sort::Integer,
                                name: v,
                            }),
                            _ => None,
                        };

                        let mut simplified = formula.clone();
                        if let Some(v1) = lhs_is_var {
                            if variables.contains(&v1) {
                                simplified =
                                    subsort_equality(v1.clone(), g.term, formula.clone(), false);
                            }
                        }
                        if let Some(v2) = rhs_is_var {
                            if variables.contains(&v2) {
                                simplified = subsort_equality(v2.clone(), term, simplified, false);
                            }
                        }
                        simplified
                    }
                    _ => formula,
                }
            }
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison { term, guards })),
                ..
            } => {
                let g = guards[0].clone();
                match g.relation {
                    Relation::Equal => {
                        let lhs_is_var = match term.clone() {
                            GeneralTerm::GeneralVariable(v) => Some(Variable {
                                sort: Sort::General,
                                name: v,
                            }),
                            GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::IntegerVariable(v),
                            )) => Some(Variable {
                                sort: Sort::Integer,
                                name: v,
                            }),
                            _ => None,
                        };
                        let rhs_is_var = match g.term.clone() {
                            GeneralTerm::GeneralVariable(v) => Some(Variable {
                                sort: Sort::General,
                                name: v,
                            }),
                            GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::IntegerVariable(v),
                            )) => Some(Variable {
                                sort: Sort::Integer,
                                name: v,
                            }),
                            _ => None,
                        };

                        let mut safety = true;
                        let mut simplified = formula.clone();
                        if let Some(v1) = lhs_is_var {
                            if variables.contains(&v1) {
                                simplified =
                                    subsort_equality(v1.clone(), g.term, formula.clone(), true);
                                safety = false;
                            }
                        }
                        if let Some(v2) = rhs_is_var {
                            if variables.contains(&v2) && safety {
                                simplified = subsort_equality(v2.clone(), term, simplified, true);
                            }
                        }
                        simplified
                    }
                    _ => formula,
                }
            }
            _ => formula,
        },
        x => x.rebox(),
    }
}

pub fn simplify_empty_quantifiers(formula: Formula) -> Formula {
    formula.apply(&mut simplify_empty_quantifiers_outer)
}

pub fn simplify_empty_quantifiers_outer(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Remove quantifiers with no variables
        // e.g. exists ( F ) => F
        UnboxedFormula::QuantifiedFormula {
            quantification: Quantification { variables, .. },
            formula: f,
        } => {
            if variables.is_empty() {
                f
            } else {
                formula
            }
        }

        x => x.rebox(),
    }
}

// TODO - make most functions private
// These aren't true simplifications, since some only make sense in the context of others being performed as well
pub fn simplify_variable_lists(formula: Formula) -> Formula {
    formula.apply(&mut simplify_variable_lists_outer)
}

pub fn simplify_variable_lists_outer(formula: Formula) -> Formula {
    match formula.clone().unbox() {
        // Removes variables from quantifiers when they do not occur in the quantified formula
        // e.g. exists X Y ( q(Y) ) => exists Y ( q(Y) )
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    mut variables,
                    quantifier,
                },
            formula,
        } => {
            let fvars = formula.variables();
            variables.retain(|x| fvars.contains(&x));
            Formula::QuantifiedFormula {
                quantification: Quantification {
                    variables,
                    quantifier,
                },
                formula: formula.into(),
            }
        }

        x => x.rebox(),
    }
}

#[cfg(test)]
mod tests {
    use super::{
        basic_simplify, basic_simplify_outer, simplify, simplify_empty_quantifiers,
        simplify_nested_quantifiers, simplify_redundant_quantifiers, simplify_theory,
        simplify_variable_lists,
    };

    #[test]
    fn test_basic_simplify() {
        for (src, target) in [
            ("#true and a", "a"),
            ("a and #true", "a"),
            ("#false or a", "a"),
            ("a or #false", "a"),
            ("#true or a", "#true"),
            ("a or #true", "#true"),
            ("#false and a", "#false"),
            ("a and #false", "#false"),
            ("a and a", "a"),
            ("a or a", "a"),
            ("#true and #true and a", "a"),
            ("#true and (#true and a)", "a"),
            (
                "forall X ((#true and p and q(X)) or (p or #true))",
                "forall X #true",
            ),
            ("forall X (q(X) or (p or #true))", "forall X #true"),
        ] {
            assert_eq!(
                basic_simplify(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_basic_simplify_outer() {
        for (src, target) in [
            ("#true and a", "a"),
            ("a and #true", "a"),
            ("#false or a", "a"),
            ("a or #false", "a"),
            ("#true or a", "#true"),
            ("a or #true", "#true"),
            ("#false and a", "#false"),
            ("a and #false", "#false"),
            ("a and a", "a"),
            ("a or a", "a"),
            ("#true and (#true and a)", "#true and a"),
            ("(#true and #true) and a", "(#true and #true) and a"),
        ] {
            assert_eq!(
                basic_simplify_outer(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_simplify_nested_quantifiers() {
        for (src, target) in [
            ("exists X (exists Y (X = Y))", "exists X Y (X = Y)"),
            (
                "exists X Y ( exists Z ( X < Y and Y < Z ))",
                "exists X Y Z ( X < Y and Y < Z )",
            ),
            (
                "exists X (exists Y (X = Y and q(Y)))",
                "exists X Y (X = Y and q(Y))",
            ),
            (
                "exists X (exists X$i (p(X) -> X$i < 1))",
                "exists X$i X (p(X) -> X$i < 1)",
            ),
            (
                "forall X Y (forall Y Z (p(X,Y) and q(Y,Z)))",
                "forall X Y Z (p(X,Y) and q(Y,Z))",
            ),
            (
                "forall X (forall Y (forall Z (X = Y = Z)))",
                "forall X Y Z (X = Y = Z)",
            ),
        ] {
            assert_eq!(
                simplify_nested_quantifiers(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_simplify_empty_quantifiers() {
        for (src, target) in [
            ("exists X (exists Y (1 < 2))", "1 < 2"),
            ("forall Z #true", "#true"),
        ] {
            assert_eq!(
                simplify_empty_quantifiers(simplify_variable_lists(src.parse().unwrap())),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_simplify_variable_lists() {
        for (src, target) in [
            (
                "exists X Y ( q or (t and q(Y)))",
                "exists Y ( q or (t and q(Y)))",
            ),
            (
                "exists Y V ( q or forall X Z (t(Y) and q(X)))",
                "exists Y ( q or forall X (t(Y) and q(X)))",
            ),
        ] {
            assert_eq!(
                simplify_variable_lists(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_simplify_redundant_quantifiers() {
        for (src, target) in [
            ("exists X ( X = Z and not q(X) )", "not q(Z)"),
            (
                "exists Y ( Y = X and forall V (p(Y,V) -> q(X)) )",
                "forall V (p(X,V) -> q(X))",
            ),
            (
                "exists Z Z1 ( Z = I and (exists K$i (K$i = I) and Z = Z1) )",
                "exists Z1 ( exists K$i (K$i = I) and I = Z1)",
            ),
        ] {
            let src =
                simplify_empty_quantifiers(simplify_redundant_quantifiers(src.parse().unwrap()));
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
        }
    }

    #[test]
    fn test_full_simplify() {
        for (src, target) in [
            (
                "exists X Y ( exists W Y Z (p(Y,Z) and #true) )",
                "exists Y Z ( p(Y,Z) )",
            ),
            (
                "forall X (forall Y (forall Z (X < Y)))",
                "forall X Y ( X < Y )",
            ),
            (
                "forall V1 (prime(V1) <-> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z)))))",
                "forall V1 (prime(V1) <-> exists I$i J$i K$i (I$i = 2 and J$i = n and V1 = K$i and I$i <= K$i <= J$i) and not composite(V1))",
            ),
            (
                "exists Z Z1 ( Z = I and (exists K$i (K$i = 2) and Z = Z1) )",
                "exists K$i(K$i = 2)",
            ),
            (
                "forall I (exists Z Z1 ( Z = I and ((q(Z)) and Z = Z1) ))",
                "forall I ( q(I) )",
            ),
        ] {
            let src = simplify(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
        }
    }

    #[test]
    fn test_simplify_theory() {
        for (src, target) in [(
            "exists X Y ( exists W Y Z (p(Y,Z) and #true) ). exists X Y ( q or (t and q(Y))).",
            "exists Y Z ( p(Y,Z) ). exists Y ( q or (t and q(Y))).",
        )] {
            assert_eq!(
                simplify_theory(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }
}
