use {
    crate::{
        convenience::{
            apply::Apply as _,
            unbox::{fol::UnboxedFormula, Unbox as _},
        },
        simplifying::fol::ht::simplify as ht_simplify,
        syntax_tree::fol::{Formula, UnaryConnective},
    },
    log::debug,
};

// Applies simplifications in a loop, until no further simplifications are possible
pub fn classical_simplify(formula: Formula) -> Formula {
    let mut f1 = formula;
    let mut f2;
    debug!("Formula prior to simplification: \n{f1}\n");
    loop {
        f2 = ht_simplify(simplify_double_negation(f1.clone()), false, true);
        debug!("Formula after basic simplification: \n{f2}\n");

        if f1 == f2 {
            break;
        }
        f1 = f2;
    }
    f1
}

/// not not F => F
pub fn simplify_double_negation(formula: Formula) -> Formula {
    formula.apply(&mut simplify_double_negation_outer)
}

pub fn simplify_double_negation_outer(formula: Formula) -> Formula {
    match formula.unbox() {
        UnboxedFormula::UnaryFormula {
            connective: UnaryConnective::Negation,
            formula:
                Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula,
                },
        } => *formula,

        x => x.rebox(),
    }
}

#[cfg(test)]
mod tests {
    use super::simplify_double_negation;

    #[test]
    fn test_simplify_double_negation() {
        for (src, target) in [
            ("not not p", "p"),
            ("not not exists X (X = 5)", "exists X (X = 5)"),
            ("not not (a <- b)", "a <- b"),
        ] {
            assert_eq!(
                simplify_double_negation(src.parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }
}
