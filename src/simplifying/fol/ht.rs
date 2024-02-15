use crate::{
    convenience::{
        apply::Apply as _,
        apply::ApplyCount as _,
        choose_fresh_variable_names,
        unbox::{fol::UnboxedFormula, Unbox as _},
    },
    syntax_tree::fol::{
        AtomicFormula, BasicIntegerTerm, BinaryConnective, Comparison, Formula, GeneralTerm, Guard,
        IntegerTerm, Quantification, Quantifier, Relation, Sort, Theory, Variable,
    },
};

use {
    evalexpr::*,
    log::debug,
};

pub fn simplify_theory(theory: Theory) -> Theory {
    //todo
    let mut formulas = theory.formulas;
    for i in 0..formulas.len() {
        formulas[i] = simplify(formulas[i].clone(), false);
    }
    Theory { formulas }
}

pub fn simplify(formula: Formula, prettify: bool) -> Formula {
    let mut f1 = formula;
    let mut f2;
    debug!("Formula prior to simplification: \n{f1}\n");
    loop {
        f2 = basic_simplify(f1.clone());
        f2 = relation_simplify(f2);
        f2 = simplify_empty_quantifiers(simplify_variable_lists(f2));
        debug!("Formula after basic simplification: \n{f2}\n");

        f2 = simplify_redundant_quantifiers(f2);
        f2 = simplify_empty_quantifiers(simplify_variable_lists(f2));
        debug!("Formula after redundant quantifier elimination: \n{f2}\n");

        f2 = simplify_nested_quantifiers(f2);
        f2 = simplify_empty_quantifiers(simplify_variable_lists(f2));
        debug!("Formula after nested quantifier joining: \n{f2}\n");

        f2 = restrict_quantifiers(f2);
        f2 = simplify_empty_quantifiers(simplify_variable_lists(f2));
        debug!("Formula after quantifier scope restriction: \n{f2}\n");

        if f1 == f2 {
            break;
        }
        f1 = f2;
    }
    if prettify {
        println!("Formula before variable renaming: \n{f1}");
        return pretty(f1);
    } else {
        return f1;
    }
}

pub fn pretty(formula: Formula) -> Formula {
    let result = formula.apply_count(&mut pretty_outer);
    result.0
}

pub fn pretty_outer(formula: Formula, mut count: usize) -> (Formula, usize) {
    match formula {
        Formula::UnaryFormula {
            connective,
            formula,
        } => {
            let f = *formula;
            let result = f.rename_variables(count);
            count = count + result.1;
            (
                Formula::UnaryFormula {
                    connective,
                    formula: result.0.into(),
                },
                count,
            )
        }
        Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => {
            let f1 = *lhs;
            let f2 = *rhs;
            let result1 = f1.rename_variables(count);
            count = count + result1.1;
            let result2 = f2.rename_variables(count);
            count = count + result2.1;
            (
                Formula::BinaryFormula {
                    connective,
                    lhs: result1.0.into(),
                    rhs: result2.0.into(),
                },
                count,
            )
        }
        Formula::QuantifiedFormula { .. } => formula.rename_variables(count),
        x => (x, count),
    }
}

// TODO: Extend to evaluating relations other than equality
pub fn relation_simplify(formula: Formula) -> Formula {
    formula.apply(&mut relation_simplify_outer)
}

pub fn relation_simplify_outer(formula: Formula) -> Formula {
    match formula.unbox() {
        // Simplify equality relations

        // s = s => #true
        // X = X => #true
        // 5 = 5 => #true || 3 + 2 = 5 => #true || ...
        UnboxedFormula::AtomicFormula(AtomicFormula::Comparison(c)) => {
            let mut f = Formula::AtomicFormula(AtomicFormula::Comparison(c.clone()));
            if c.equality_comparison() {
                let rhs = c.guards[0].term.clone();
                match c.term {
                    GeneralTerm::Symbol(lhs) => match rhs {
                        GeneralTerm::Symbol(s) => {
                            if lhs == s {
                                f = Formula::AtomicFormula(AtomicFormula::Truth);
                            }
                        }
                        GeneralTerm::GeneralVariable(_) => (),
                        GeneralTerm::IntegerTerm(_) => (),  // LHS could be an integer-valued placeholder, so no simplifications are possible
                    },
                    GeneralTerm::GeneralVariable(lhs) => match rhs {
                        GeneralTerm::GeneralVariable(v) => {
                            if lhs == v {
                                f = Formula::AtomicFormula(AtomicFormula::Truth);
                            }
                        }
                        _ => (),
                    },
                    GeneralTerm::IntegerTerm(lhs) => match rhs {
                        GeneralTerm::Symbol(_) => (), // RHS could be an integer-valued placeholder, so no simplifications are possible
                        GeneralTerm::GeneralVariable(_) => (),
                        GeneralTerm::IntegerTerm(i) => {
                            let equality = format!("({lhs}) == ({i})");
                            let eval_result = eval(&equality);
                            match eval_result {
                                Ok(bool) => match bool {
                                    Value::Boolean(b) => {
                                        if b {
                                            f = Formula::AtomicFormula(AtomicFormula::Truth);
                                        } else {
                                            f = Formula::AtomicFormula(AtomicFormula::Falsity);
                                        }
                                    }
                                    _ => (),
                                },
                                Err(_) => (),
                            }
                        }
                    },
                }
            }
            f
        }

        x => x.rebox(),
    }
}

pub fn basic_simplify(formula: Formula) -> Formula {
    formula.apply(&mut basic_simplify_outer)
}

pub fn basic_simplify_outer(formula: Formula) -> Formula {
    // TODO: Split simplifications into multiple functions?
    // tdo
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
// F(var) & var = term  OR
// F(var) & term = var
// If var is a variable of sort S and term is a term of a subsort of S, 
// and term doesn't contain variables quantified within F, return `F(term)`
// Otherwise, return the original formula
fn subsort_equality(var: Variable, term: GeneralTerm, formula: Formula) -> (Formula, bool) {
    let mut modified = false;
    let mut simplified_formula = formula.clone();
    match formula.clone().unbox() {
        UnboxedFormula::BinaryFormula {
            connective: BinaryConnective::Conjunction,
            lhs,
            ..
        } => {
            let term_vars = term.variables();   // term must not contain var
            match var.sort {
                Sort::General => {
                    if !term_vars.contains(&var) && !lhs.clone().unsafe_substitution(&var, &term) {               
                        modified = true;
                        simplified_formula = lhs.substitute(var, term);
                    }
                },
                Sort::Integer => match term.clone() {
                    GeneralTerm::IntegerTerm(_) => {
                        if !term_vars.contains(&var) && !lhs.clone().unsafe_substitution(&var, &term) {
                            modified = true;
                            simplified_formula = lhs.substitute(var, term);
                        }
                    },
                    _ => {
                        simplified_formula = formula;
                    }
                },
            }
        },

        _ => panic!("you're using the subsort equality fn wrong"),
    }
    (simplified_formula, modified)
}

// Given a tree of conjunctions, F1, .. Fi, .. Fn, identify an equality formula Fi: X = t or t = X
// If possible, substitute t for X within the tree and drop Fi
// Return the original formula and None if not possible
// Otherwise, return the simplified formula and the variable that was replaced 
fn simplify_conjunction_tree_with_equality(formula: Formula, enclosing_variables: Vec<Variable>) -> (Formula, Option<Variable>) {
    let mut result = (formula.clone(), None);
    let conjunctive_terms = Formula::conjoin_invert(formula.clone());
    for ct in conjunctive_terms.iter() {
        // Search for an equality formula
        if let Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
            term,
            guards,
        })) = ct
        {
            if guards.len() == 1 {
                let g = guards[0].clone();
                match g.relation {
                    Relation::Equal => {
                        let lhs_is_var = match term.clone() {
                            GeneralTerm::GeneralVariable(v) => Some(Variable {
                                sort: Sort::General,
                                name: v,
                            }),
                            GeneralTerm::IntegerTerm(
                                IntegerTerm::BasicIntegerTerm(
                                    BasicIntegerTerm::IntegerVariable(v),
                                ),
                            ) => Some(Variable {
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
                            GeneralTerm::IntegerTerm(
                                IntegerTerm::BasicIntegerTerm(
                                    BasicIntegerTerm::IntegerVariable(v),
                                ),
                            ) => Some(Variable {
                                sort: Sort::Integer,
                                name: v,
                            }),
                            _ => None,
                        };

                        let mut safety = true; // Simplify var = term or term = var but not both
                        // Don't restructure the conjunction tree unless simplification occurs
                        let mut restructured = vec![]; // Make the equality formula the top rhs leaf of a new conjunction tree
                        for i in 0..conjunctive_terms.len() {
                            if conjunctive_terms[i] != *ct {
                                restructured.push(conjunctive_terms[i].clone());
                            }
                        }
                        restructured.push(ct.clone());

                        let simplified = Formula::conjoin(restructured);

                        if let Some(v1) = lhs_is_var {
                            if enclosing_variables.contains(&v1) {
                                let simplification_result =
                                    subsort_equality(v1.clone(), g.term, simplified.clone());
                                safety = false;
                                if simplification_result.1 {
                                    result = (simplification_result.0, Some(v1));
                                } else {
                                    result = (formula.clone(), None);
                                }    
                            }
                        }
                        if let Some(v2) = rhs_is_var {
                            if enclosing_variables.contains(&v2) && safety {
                                let simplification_result = subsort_equality(
                                    v2.clone(),
                                    term.clone(),
                                    simplified,
                                );
                                safety = false;
                                if simplification_result.1 {
                                    result = (simplification_result.0, Some(v2));
                                } else {
                                    result = (formula.clone(), None);
                                }
                            }
                        }
                        if !safety {
                            break;
                        }
                    },

                    _ => (),
                }
            }
        }
    }
    result
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
                    mut variables,
                },
            formula: f,
        } => match f.clone().unbox() {
            UnboxedFormula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                ..
            } => {
                let simplification_result = simplify_conjunction_tree_with_equality(f, variables.clone());
                match simplification_result.1 {
                    Some(var) => {
                        variables.retain(|v| v != &var);
                        Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Exists,
                                variables,
                            },
                            formula: simplification_result.0.into(),
                        }
                    },
                    None => {
                        formula
                    }
                }
            }
            _ => formula,
        },

        // A universally quantified implication can sometimes be simplified
        // e.g. forall X1 .. Xj .. Xn  (F1 and .. Fi .. and Fm -> G), where Fi is Xj=t, and Xj doesn’t occur in t, and free variables occurring in t are not bound by quantifiers in F1, F2, ..
        // becomes forall X1 .. Xn  (F1 and .. and Fm -> G)
        // UnboxedFormula::QuantifiedFormula {
        //     quantification:
        //         Quantification {
        //             quantifier: Quantifier::Forall,
        //             variables,
        //         },
        //     formula: Formula::BinaryFormula {
        //         connective: BinaryConnective::Implication,
        //         lhs,
        //         rhs,
        //     },
        // } => {
        //     match lhs.clone().unbox() {
        //         UnboxedFormula::BinaryFormula {
        //             connective: BinaryConnective::Conjunction,
        //             ..
        //         }

        //         _ => formula,
        //     }
        // },

        _ => formula,
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

pub fn restrict_quantifiers(formula: Formula) -> Formula {
    formula.apply(&mut restrict_quantifiers_outer)
}

pub fn restrict_quantifiers_outer(formula: Formula) -> Formula {
    let mut simplified_formula = formula.clone();
    match formula.clone().unbox() {
        // Replace a general variable in an outer quantification with a fresh integer variable capturing an inner quantification
        // e.g. exists Z$g (exists I$i J$i (I$i = Z$g & G) & H) => exists K$i (exists I$i J$i (I$i = K$i & G) & H)
        // or forall Z$g (exists I$i J$i (I$i = Z$g & G) & H) => forall K$i (exists I$i J$i (I$i = K$i & G) & H)
        UnboxedFormula::QuantifiedFormula {
            quantification:
                Quantification {
                    quantifier: outer_quantifier,
                    variables: outer_vars,
                },
            formula: f,
        } => {
            match f.clone().unbox() {
                UnboxedFormula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    ..
                } => {
                    let conjunctive_terms = Formula::conjoin_invert(f.clone());
                    for ct in conjunctive_terms.iter() {
                        if let Formula::QuantifiedFormula {
                            quantification:
                                Quantification {
                                    quantifier: Quantifier::Exists,
                                    variables: inner_vars,
                                },
                            formula: inner_formula,
                        } = ct
                        {
                            match inner_formula.clone().unbox() {
                                UnboxedFormula::BinaryFormula {
                                    connective: BinaryConnective::Conjunction,
                                    ..
                                } => {
                                    let inner_ct = Formula::conjoin_invert(*inner_formula.clone());
                                    for ict in inner_ct.iter() {
                                        if let Formula::AtomicFormula(AtomicFormula::Comparison(
                                            comp,
                                        )) = ict
                                        {
                                            if comp.equality_comparison() {
                                                let outer_copy = outer_vars.clone();
                                                let inner_copy = inner_vars.clone();
                                                for ovar in outer_copy.iter() {
                                                    for ivar in inner_copy.iter() {
                                                        if ovar.sort == Sort::General
                                                            && ivar.sort == Sort::Integer
                                                        {
                                                            let ivar_term = GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(ivar.name.clone())));
                                                            let candidate = Comparison {
                                                                term: GeneralTerm::GeneralVariable(
                                                                    ovar.name.clone(),
                                                                ),
                                                                guards: vec![Guard {
                                                                    relation: Relation::Equal,
                                                                    term: ivar_term.clone(),
                                                                }],
                                                            };
                                                            let mut replace = false;
                                                            if comp == &candidate {
                                                                replace = true;
                                                            } else {
                                                                let candidate = Comparison {
                                                                term: ivar_term.clone(),
                                                                guards: vec![Guard {
                                                                    relation: Relation::Equal,
                                                                    term: GeneralTerm::GeneralVariable(ovar.name.clone()),
                                                                }],
                                                            };
                                                                if comp == &candidate {
                                                                    replace = true;
                                                                }
                                                            }

                                                            if replace {
                                                                let varnames =
                                                                    choose_fresh_variable_names(
                                                                        &formula.variables(),
                                                                        &ivar
                                                                            .name
                                                                            .chars()
                                                                            .next()
                                                                            .unwrap()
                                                                            .to_string(),
                                                                        1,
                                                                    );
                                                                let fvar = varnames[0].clone();
                                                                let fvar_term = GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(fvar.clone())));
                                                                let mut new_outer =
                                                                    outer_vars.clone();
                                                                new_outer.retain(|x| x != ovar);
                                                                new_outer.push(Variable {
                                                                    name: fvar,
                                                                    sort: Sort::Integer,
                                                                });
                                                                simplified_formula = Formula::QuantifiedFormula {
                                                                quantification: Quantification {
                                                                    quantifier: outer_quantifier.clone(),
                                                                    variables: new_outer,
                                                                },
                                                                formula: f.clone().substitute(ovar.clone(), fvar_term).into(),
                                                            };
                                                                break;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                                _ => (),
                            }
                        }
                    }
                }
                _ => (),
            }
        }
        _ => (),
    }
    simplified_formula
}

#[cfg(test)]
mod tests {
    use super::{
        basic_simplify, basic_simplify_outer, relation_simplify_outer, restrict_quantifiers,
        simplify, simplify_empty_quantifiers, simplify_nested_quantifiers,
        simplify_redundant_quantifiers, simplify_theory, simplify_variable_lists, simplify_conjunction_tree_with_equality,
    };

    use crate::syntax_tree::fol::{Variable, Sort};

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
    fn test_relation_simplify_outer() {
        for (src, target) in [
            ("s = s", "#true"),
            //("s = a", "#false"),  // These are only valid in the absence of placeholders
            //("s = X$i", "#false"),
            //("a = 5", "#false"),
            //("X$i = s", "#false"),
            //("5 = s", "#false"),
            //("X$i = X$i", "#true"),
            ("5 = 5", "#true"),
            ("(3 + 2) * -1 = -5", "#true"),
        ] {
            assert_eq!(
                relation_simplify_outer(src.parse().unwrap()),
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
    fn test_simplify_conjunction_tree() {
        for (src, target) in [
            ((
                "X = Z and not q(X)", 
                vec![
                    Variable { name: "X".to_string(), sort: Sort::General, },
                    Variable { name: "Y".to_string(), sort: Sort::General, },
                    ]
            ), "not q(Z)"),
        ] {
            let result = simplify_conjunction_tree_with_equality(src.0.parse().unwrap(), src.1).0;
            let target = target.parse().unwrap();
            assert_eq!(result, target, "{result} != {target}")
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
    fn test_restrict_quantifiers() {
        for (src, target) in [
            (
                "exists Z Z1 ( exists I$i J$i ( Z = J$i and q(I$i, J$i) ) and Z = Z1 )",
                "exists Z1 J1$i ( exists I$i J$i ( J1$i = J$i and q(I$i, J$i) ) and J1$i = Z1 )",
            ),
            (
                "exists Z Z1 ( exists I$i J$i ( q(I$i, J$i) and Z = J$i) and Z = Z1 )",
                "exists Z1 J1$i ( exists I$i J$i ( q(I$i, J$i) and J1$i = J$i) and J1$i = Z1 )",
            ),
            (
                "exists Z Z1 ( Z = Z1 and exists I$i J$i ( q(I$i, J$i) and Z = J$i) )",
                "exists Z1 J1$i ( J1$i = Z1 and exists I$i J$i ( q(I$i, J$i) and J1$i = J$i) )",
            ),
            (
                "exists Z Z1 ( Z = Z1 and exists I$i J$i ( q(I$i, J$i) and Z = J$i and 3 > 2) and 1 < 5 )",
                "exists Z1 J1$i ( J1$i = Z1 and exists I$i J$i ( q(I$i, J$i) and J1$i = J$i and 3 > 2) and 1 < 5 )",
            ),
        ] {
            let src =
                restrict_quantifiers(src.parse().unwrap());
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
                "exists X Y ( exists N1$i N2$i ( V1 = N1$i * N2$i and N1$i = X and N2$i = Y) and X > 1 and Y > 1)",
                "exists N$i N3$i ((V1 = N3$i * N$i) and N3$i > 1 and N$i > 1)",
            ),
            (
                "forall V1 (composite(V1) <-> exists I J (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = N$i and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z Z1 (Z = J and exists I$i J$i K$i (I$i = 2 and J$i = N$i and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1))))",
                "forall V1 (composite(V1) <-> exists K2$i K3$i (V1 = K3$i * K2$i and (2 <= K3$i <= N$i and 2 <= K2$i <= N$i))) ",
            ),
            // (
            //     "forall V1 (prime(V1) <-> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z)))))",
            //     "forall V1 (prime(V1) <-> exists J$i K$i (J$i = n and V1 = K$i and 2 <= K$i <= J$i) and not composite(V1))",
            // ),
            // (
            //     "forall V1 (composite(V1) <-> exists I J (exists I1$i J1$i (V1 = I1$i * J1$i and I1$i = I and J1$i = J) and (exists Z Z1 (Z = I and Z1 = 1 and Z > Z1) and exists Z Z1 (Z = J and Z1 = 1 and Z > Z1))))",
            //     "",
            // ),
            // (            // (
            //     "forall V1 (prime(V1) <-> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z)))))",
            //     "forall V1 (prime(V1) <-> exists J$i K$i (J$i = n and V1 = K$i and 2 <= K$i <= J$i) and not composite(V1))",
            // ),
            //     "forall V1 (prime(V1) <-> exists I (V1 = I and (exists Z Z1 (Z = I and exists I$i J$i K$i (I$i = 2 and J$i = n and Z1 = K$i and I$i <= K$i <= J$i) and Z = Z1) and exists Z (Z = I and not composite(Z)))))",
            //     "",
            // ),
            (
                "exists Z Z1 ( Z = I and (exists K$i (K$i = 2) and Z = Z1) )",
                "exists K$i(K$i = 2)",
            ),
            (
                "forall I (exists Z Z1 ( Z = I and ((q(Z)) and Z = Z1) ))",
                "forall I ( q(I) )",
            ),
        ] {
            let src = simplify(src.parse().unwrap(), false);
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
