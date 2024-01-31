use crate::{
    convenience::{
        apply::Apply as _,
        unbox::{fol::UnboxedFormula, Unbox as _},
    },
    syntax_tree::fol::{AtomicFormula, BinaryConnective, Formula, Quantification},
};

pub fn simplify(formula: Formula) -> Formula {
    formula.apply(&mut simplify_outer)
}

pub fn simplify_outer(formula: Formula) -> Formula {
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

pub fn simplify_quantifiers(formula: Formula) -> Formula {
    formula.apply(&mut simplify_quantifiers_outer)
}

pub fn simplify_quantifiers_outer(formula: Formula) -> Formula {
    match formula.unbox() {
        // Remove redundant existentials
        // e.g. exists Z$g (Z$g = X$g and F(Z$g)) => F(X$g)
        // UnboxedFormula::QuantifiedFormula {
        //     quantification: {
        //         quantifier: Quantifier::Exists,
        //         variables: vars,
        //     },
        //     formula: f,
        // } => {
        //     match f.unbox() {
        //         UnboxedFormula::BinaryFormula {
        //             connective: BinaryConnective::Conjunction,
        //             lhs: lhs @ Formula::AtomicFormula(AtomicFormula::Comparison{
        //                 term: GeneralTerm::GeneralVariable(v),
        //                 guards,
        //             }),
        //             rhs,
        //         } => {
        //             if vars.contains(GeneralVariable(v)) {
        //                 // todo
        //             } else {
        //                 formula
        //             }
        //         },
        //         _ => ???
        //     }
        // },
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

#[cfg(test)]
mod tests {
    use super::{
        simplify, simplify_empty_quantifiers, simplify_nested_quantifiers, simplify_outer,
    };

    #[test]
    fn test_simplify() {
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
            assert_eq!(simplify(src.parse().unwrap()), target.parse().unwrap())
        }
    }

    #[test]
    fn test_simplify_outer() {
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
                simplify_outer(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_simplify_nested_quantifiers() {
        for (src, target) in [
            ("exists X (exists Y (X = Y))", "exists X Y (X = Y)"),
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

    // #[test]
    // fn test_simplify_empty_quantifiers() {
    //     for (src, target) in [
    //         ("exists X (exists Y (1 < 2))", "1 < 2"),
    //         ("forall Z #true", "#true"),
    //     ] {
    //         assert_eq!(
    //             simplify_empty_quantifiers(src.parse().unwrap()),
    //             target.parse().unwrap()
    //         )
    //     }
    // }
}
