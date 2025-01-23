use {
    crate::{
        command_line::arguments::{FormulaRepresentation, TaskDecomposition},
        convenience::with_warnings::{Result, WithWarnings},
        syntax_tree::{asp, fol},
        translating::{
            asp_to_ht::{tau_star::tau_star, Version},
            shorthand::shorthand,
        },
        verifying::{
            problem::{AnnotatedFormula, FormulaType, Interpretation, Problem, Role},
            task::Task,
        },
    },
    std::convert::Infallible,
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum IntuitEquivalenceTaskError {}

pub struct IntuitEquivalenceTask {
    pub left: asp::Program,
    pub right: asp::Program,
    pub task_decomposition: TaskDecomposition,
    pub direction: fol::Direction,
    pub simplify: bool,
    pub break_equivalences: bool,
    pub translation: FormulaRepresentation,
}

impl Task for IntuitEquivalenceTask {
    type Error = IntuitEquivalenceTaskError;
    type Warning = Infallible;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let mut left = match self.translation {
            FormulaRepresentation::TauStarV1 => tau_star(self.left, Version::Original),
            FormulaRepresentation::Shorthand => shorthand(self.left),
            FormulaRepresentation::TauStarV2 => {
                tau_star(self.left, Version::AbstractGringoCompliant)
            }
        };
        let mut right = match self.translation {
            FormulaRepresentation::TauStarV1 => tau_star(self.right, Version::Original),
            FormulaRepresentation::Shorthand => shorthand(self.right),
            FormulaRepresentation::TauStarV2 => {
                tau_star(self.right, Version::AbstractGringoCompliant)
            }
        };

        if self.simplify {
            left = crate::simplifying::fol::ht::simplify(left);
            right = crate::simplifying::fol::ht::simplify(right);
        }

        if self.break_equivalences {
            left = crate::breaking::fol::ht::break_equivalences_theory(left);
            right = crate::breaking::fol::ht::break_equivalences_theory(right);
        }

        let (ftype, interp) = match self.translation {
            FormulaRepresentation::TauStarV1 | FormulaRepresentation::TauStarV2 => {
                (FormulaType::Tff, Interpretation::Standard)
            }
            FormulaRepresentation::Shorthand => (FormulaType::Fof, Interpretation::IltpStd),
        };

        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            problems.push(
                Problem::with_name("forward", interp.clone())
                    .add_theory(left.clone(), |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Axiom,
                        formula,
                        formula_type: ftype.clone(),
                    })
                    .add_theory(right.clone(), |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Conjecture,
                        formula,
                        formula_type: ftype.clone(),
                    })
                    .rename_conflicting_symbols(),
            );
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            problems.push(
                Problem::with_name("backward", interp)
                    .add_theory(right, |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Axiom,
                        formula,
                        formula_type: ftype.clone(),
                    })
                    .add_theory(left, |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Conjecture,
                        formula,
                        formula_type: ftype.clone(),
                    })
                    .rename_conflicting_symbols(),
            );
        }

        Ok(WithWarnings::flawless(
            problems
                .into_iter()
                .flat_map(|p: Problem| match self.task_decomposition {
                    TaskDecomposition::Independent => p.decompose_independent(),
                    TaskDecomposition::Sequential => p.decompose_sequential(),
                })
                .collect(),
        ))
    }
}
