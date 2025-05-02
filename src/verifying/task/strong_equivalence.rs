use {
    crate::{
        command_line::arguments::{FormulaRepresentation, TaskDecomposition},
        convenience::with_warnings::{Result, WithWarnings},
        syntax_tree::{asp, fol},
        translating::{
            asp_to_ht::{
                tau_star,
                Version::{AbstractGringoCompliant, Original},
            },
            gamma::{self, gamma},
        },
        verifying::{
            problem::{AnnotatedFormula, FormulaType, Interpretation, Problem, Role},
            task::Task,
        },
    },
    std::convert::Infallible,
    thiserror::Error,
};

impl From<fol::Theory> for fol::Formula {
    fn from(theory: fol::Theory) -> Self {
        fol::Formula::conjoin(theory.formulas)
    }
}

#[derive(Error, Debug)]
pub enum StrongEquivalenceCounterModelTaskError {}

pub struct StrongEquivalenceCounterModelTask {
    pub left: asp::Program,
    pub right: asp::Program,
    pub formula_representation: FormulaRepresentation,
    pub simplify: bool,
}

// TODO: refactor to use the same code as StrongEquivalenceTask
impl StrongEquivalenceCounterModelTask {
    fn transition_axioms(&self) -> fol::Theory {
        fn transition(p: asp::Predicate) -> fol::Formula {
            let p: fol::Predicate = p.into();

            let hp = gamma::here(p.clone().to_formula());
            let tp = gamma::there(p.to_formula());

            let variables = hp.free_variables();

            fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Implication,
                lhs: hp.into(),
                rhs: tp.into(),
            }
            .quantify(fol::Quantifier::Forall, variables.into_iter().collect())
        }

        let mut predicates = self.left.predicates();
        predicates.extend(self.right.predicates());

        fol::Theory {
            formulas: predicates.into_iter().map(transition).collect(),
        }
    }
}

impl Task for StrongEquivalenceCounterModelTask {
    type Error = StrongEquivalenceTaskError;
    type Warning = Infallible;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let transition_axioms = self.transition_axioms(); // These are the "forall X (hp(X) -> tp(X))" axioms.

        let version = match self.formula_representation {
            FormulaRepresentation::TauStarV1 => Original,
            FormulaRepresentation::TauStarV2 => AbstractGringoCompliant,
            FormulaRepresentation::Shorthand => Original, // Doesn't matter for shorthand?
        };

        let mut left = tau_star::tau_star(self.left, version);
        let mut right = tau_star::tau_star(self.right, version);

        if self.simplify {
            left = crate::simplifying::fol::ht::simplify(left);
            right = crate::simplifying::fol::ht::simplify(right);
        }

        left = gamma(left);
        right = gamma(right);

        if self.simplify {
            left = crate::simplifying::fol::classic::simplify(left);
            right = crate::simplifying::fol::classic::simplify(right);
        }

        // not ( gamma(tau-star(P1)) <-> gamma(tau-star(P2)) )
        let f = fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Equivalence,
                lhs: Box::new(left.into()),
                rhs: Box::new(right.into()),
            }
            .into(),
        };

        let conjecture = fol::Theory { formulas: vec![f] };

        let mut problems = Vec::new();
        problems.push(
            Problem::with_name("countermodel", Interpretation::Standard)
                .add_theory(transition_axioms.clone(), |i, formula| AnnotatedFormula {
                    name: format!("transition_axiom_{i}"),
                    role: Role::Axiom,
                    formula,
                    formula_type: FormulaType::Tff,
                })
                .add_theory(conjecture, |i, formula| AnnotatedFormula {
                    name: format!("conjecture_{i}"),
                    role: Role::Conjecture,
                    formula,
                    formula_type: FormulaType::Tff,
                })
                .rename_conflicting_symbols()
                .create_unique_formula_names(),
        );

        Ok(WithWarnings::flawless(problems))
    }
}

#[derive(Error, Debug)]
pub enum StrongEquivalenceTaskError {}

pub struct StrongEquivalenceTask {
    pub left: asp::Program,
    pub right: asp::Program,
    pub formula_representation: FormulaRepresentation,
    pub task_decomposition: TaskDecomposition,
    pub direction: fol::Direction,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl StrongEquivalenceTask {
    fn transition_axioms(&self) -> fol::Theory {
        fn transition(p: asp::Predicate) -> fol::Formula {
            let p: fol::Predicate = p.into();

            let hp = gamma::here(p.clone().to_formula());
            let tp = gamma::there(p.to_formula());

            let variables = hp.free_variables();

            fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Implication,
                lhs: hp.into(),
                rhs: tp.into(),
            }
            .quantify(fol::Quantifier::Forall, variables.into_iter().collect())
        }

        let mut predicates = self.left.predicates();
        predicates.extend(self.right.predicates());

        fol::Theory {
            formulas: predicates.into_iter().map(transition).collect(),
        }
    }
}

impl Task for StrongEquivalenceTask {
    type Error = StrongEquivalenceTaskError;
    type Warning = Infallible;

    fn decompose(self) -> Result<Vec<Problem>, Self::Warning, Self::Error> {
        let transition_axioms = self.transition_axioms(); // These are the "forall X (hp(X) -> tp(X))" axioms.

        let version = match self.formula_representation {
            FormulaRepresentation::TauStarV1 => Original,
            FormulaRepresentation::TauStarV2 => AbstractGringoCompliant,
            FormulaRepresentation::Shorthand => Original, // Doesn't matter for shorthand?
        };

        let mut left = tau_star::tau_star(self.left, version);
        let mut right = tau_star::tau_star(self.right, version);

        if self.simplify {
            left = crate::simplifying::fol::ht::simplify(left);
            right = crate::simplifying::fol::ht::simplify(right);
        }

        left = gamma(left);
        right = gamma(right);

        if self.simplify {
            left = crate::simplifying::fol::classic::simplify(left);
            right = crate::simplifying::fol::classic::simplify(right);
        }

        if self.break_equivalences {
            left = crate::breaking::fol::ht::break_equivalences_theory(left);
            right = crate::breaking::fol::ht::break_equivalences_theory(right);
        }

        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            problems.push(
                Problem::with_name("forward", Interpretation::Standard)
                    .add_theory(transition_axioms.clone(), |i, formula| AnnotatedFormula {
                        name: format!("transition_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                        formula_type: FormulaType::Tff,
                    })
                    .add_theory(left.clone(), |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Axiom,
                        formula,
                        formula_type: FormulaType::Tff,
                    })
                    .add_theory(right.clone(), |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Conjecture,
                        formula,
                        formula_type: FormulaType::Tff,
                    })
                    .rename_conflicting_symbols(),
            );
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            problems.push(
                Problem::with_name("backward", Interpretation::Standard)
                    .add_theory(transition_axioms, |i, formula| AnnotatedFormula {
                        name: format!("transition_axiom_{i}"),
                        role: Role::Axiom,
                        formula,
                        formula_type: FormulaType::Tff,
                    })
                    .add_theory(right, |i, formula| AnnotatedFormula {
                        name: format!("right_{i}"),
                        role: Role::Axiom,
                        formula,
                        formula_type: FormulaType::Tff,
                    })
                    .add_theory(left, |i, formula| AnnotatedFormula {
                        name: format!("left_{i}"),
                        role: Role::Conjecture,
                        formula,
                        formula_type: FormulaType::Tff,
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
