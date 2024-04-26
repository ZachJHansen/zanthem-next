use {
    crate::{
        command_line::Decomposition,
        convenience::apply::Apply,
        syntax_tree::{asp, fol},
        translating::{completion::completion, tau_star::tau_star},
        verifying::{
            problem::{AnnotatedFormula, Problem, Role},
            task::Task,
        },
    },
    either::Either,
    indexmap::{IndexMap, IndexSet},
    std::fmt::Display,
    thiserror::Error,
};

#[derive(Debug)]
pub struct ExternalEquivalenceTask {
    pub specification: Either<asp::Program, fol::Specification>,
    pub program: asp::Program,
    pub user_guide: fol::UserGuide,
    pub proof_outline: fol::Specification,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub simplify: bool,
    pub break_equivalences: bool,
}

#[derive(Error, Debug)]
pub enum ExternalEquivalenceTaskError {
    InputOutputPredicatesOverlap(Vec<fol::Predicate>),
    InputPredicateInRuleHead(Vec<fol::Predicate>),
}

impl Display for ExternalEquivalenceTaskError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExternalEquivalenceTaskError::InputOutputPredicatesOverlap(predicates) => {
                write!(
                    f,
                    "the following predicates are declared as input and output predicates: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
            ExternalEquivalenceTaskError::InputPredicateInRuleHead(predicates) => {
                write!(
                    f,
                    "the following predicates are declared as input and output predicates: "
                )?;

                let mut iter = predicates.iter().peekable();
                for predicate in predicates {
                    write!(f, "{predicate}")?;
                    if iter.peek().is_some() {
                        write!(f, ", ")?;
                    }
                }

                writeln!(f)
            }
        }
    }
}

impl ExternalEquivalenceTask {
    fn ensure_input_and_output_predicates_are_disjoint(
        &self,
    ) -> Result<(), ExternalEquivalenceTaskError> {
        let input_predicates = self.user_guide.input_predicates();
        let output_predicates = self.user_guide.output_predicates();

        let intersection: Vec<_> = input_predicates
            .intersection(&output_predicates)
            .cloned()
            .collect();

        if intersection.is_empty() {
            Ok(())
        } else {
            Err(ExternalEquivalenceTaskError::InputOutputPredicatesOverlap(
                intersection,
            ))
        }
    }

    fn ensure_program_heads_do_not_contain_input_predicates(
        &self,
    ) -> Result<(), ExternalEquivalenceTaskError> {
        let input_predicates = self.user_guide.input_predicates();
        let head_predicates: IndexSet<_> = self
            .program
            .head_predicates()
            .into_iter()
            .map(fol::Predicate::from)
            .collect();

        let intersection: Vec<_> = input_predicates
            .intersection(&head_predicates)
            .cloned()
            .collect();

        if intersection.is_empty() {
            Ok(())
        } else {
            Err(ExternalEquivalenceTaskError::InputPredicateInRuleHead(
                intersection,
            ))
        }
    }
}

impl Task for ExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;

    fn decompose(&self) -> Result<Vec<Problem>, Self::Error> {
        self.ensure_input_and_output_predicates_are_disjoint()?;
        self.ensure_program_heads_do_not_contain_input_predicates()?;

        // TODO: Ensure there's not a$i and a$g in the user guide
        let placeholder = self
            .user_guide
            .placeholders()
            .into_iter()
            .map(|p| (p.name.clone(), p))
            .collect();

        let public_predicates = self.user_guide.public_predicates();

        // TODO: Apply simplifications
        // TODO: Apply equivalence breaking
        // TODO: Rename private predicates

        let head_predicate = |formula: fol::Formula| {
            let head_formula = *match formula {
                fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::Equivalence,
                    lhs,
                    ..
                } => lhs,
                fol::Formula::QuantifiedFormula { formula, .. } => match *formula {
                    fol::Formula::BinaryFormula {
                        connective: fol::BinaryConnective::Equivalence,
                        lhs,
                        ..
                    } => lhs,
                    _ => None?,
                },
                _ => None?,
            };

            Some(
                match head_formula {
                    fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(a)) => a,
                    _ => None?,
                }
                .predicate(),
            )
        };

        let group = |theory: fol::Theory| {
            let mut stable = Vec::new();
            let mut unstable = Vec::new();

            for formula in theory.formulas {
                // TODO: Remove clone
                match head_predicate(formula.clone()) {
                    Some(p) if !public_predicates.contains(&p) => stable.push(formula),
                    _ => unstable.push(formula),
                }
            }

            (stable, unstable)
        };

        let mut stable_premises: Vec<fol::Formula> = Vec::new();
        let mut forward_premises: Vec<fol::Formula> = Vec::new();
        let mut forward_conclusions: Vec<fol::Formula> = Vec::new();
        let mut backward_premises: Vec<fol::Formula> = Vec::new();
        let mut backward_conclusions: Vec<fol::Formula> = Vec::new();

        for formula in self.user_guide.formulas() {
            match formula.role {
                fol::Role::Assumption => stable_premises.push(formula.formula),
                fol::Role::Spec => todo!(),  // TODO Report user error,
                fol::Role::Lemma => todo!(), // TODO Report user error
            }
        }

        // TODO: Avoid cloning
        match self.specification.clone() {
            Either::Left(specification) => {
                let specification =
                    completion(tau_star(specification).replace_placeholders(&placeholder))
                        .expect("tau_star did not create a completable theory");

                let (mut stable, mut unstable) = group(specification);
                stable_premises.append(&mut stable);
                // TODO: Unstable premises
            }

            Either::Right(_specification) => todo!(),
        }

        let program = completion(tau_star(self.program.clone()).replace_placeholders(&placeholder))
            .expect("tau_star did not create a completable theory");

        let (mut stable, mut unstable) = group(program);
        stable_premises.append(&mut stable);

        // TODO Avoid clone
        let mut lemmas = Vec::new();
        for formula in self.proof_outline.formulas.clone() {
            match formula.role {
                fol::Role::Assumption => todo!(), // TODO Report user error
                fol::Role::Spec => todo!(),       // TODO Report user error
                fol::Role::Lemma => lemmas.push(formula.formula),
            }
        }

        // forward direction
        // S, F |= FL
        // S, F, L |= B

        // backward direction
        // S, B |= BL
        // S, B, L |= F

        // S, F |= FL, B

        // forward
        //   - stable
        //       - assumptions from the user guide
        //       - assumptions from specification
        //       - completed definitions of private predicates from the program
        //   - forward
        //       - specs from the specification
        // |=
        //    - forward lemmas

        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            problems.push(
                Problem::default()
                    .add_formulas(stable_premises, |i, formula| AnnotatedFormula {
                        name: format!("stable_premise_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_formulas(forward_premises, |i, formula| AnnotatedFormula {
                        name: format!("forward_premise_{i}"),
                        role: Role::Axiom,
                        formula,
                    })
                    .add_formulas(lemmas, |i, formula| AnnotatedFormula {
                        name: format!("lemma_{i}"),
                        role: Role::Conjecture,
                        formula,
                    }),
            )
        }

        Ok(problems
            .into_iter()
            .map(|p: Problem| match self.decomposition {
                Decomposition::Independent => p.decompose_independent(),
                Decomposition::Sequential => p.decompose_sequential(),
            })
            .flatten()
            .collect())

        // TODO
        // forward_premises.append(&mut unstable.clone());
        // backward_conclusions.append(&mut unstable);

        // specification (program)
        // Is formular a forall X p(X) <-> F or p <-> F
        //     If p is input or output? => backward_conclusions, forward_premises
        //     Else? => stable_premises
        // Else?
        //     forward_conclusions, backwards_premises

        // program
        // Is formular a forall X p(X) <-> F or p <-> F
        //     If p is input or output? => forward_conclusions, backward_premises
        //     Else? => stable_premises
        // Else?
        //     forward_conclusions, backwards_premises

        // stable premises
        // forward premises
        // forward conclusions
        // backward premises
        // backward conclusions
    }
}

impl Display for ExternalEquivalenceTask {
    fn fmt(&self, _f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

// TODO: The following could be much easier with an enum over all types of nodes which implements the apply trait
trait ReplacePlaceholders {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self;
}

impl ReplacePlaceholders for fol::Theory {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self {
        fol::Theory {
            formulas: self
                .formulas
                .into_iter()
                .map(|f| f.replace_placeholders(mapping))
                .collect(),
        }
    }
}

impl ReplacePlaceholders for fol::Formula {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self {
        self.apply(&mut |formula| match formula {
            fol::Formula::AtomicFormula(a) => {
                fol::Formula::AtomicFormula(a.replace_placeholders(mapping))
            }
            x => x,
        })
    }
}

impl ReplacePlaceholders for fol::AtomicFormula {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self {
        match self {
            fol::AtomicFormula::Atom(a) => {
                fol::AtomicFormula::Atom(a.replace_placeholders(mapping))
            }
            fol::AtomicFormula::Comparison(c) => {
                fol::AtomicFormula::Comparison(c.replace_placeholders(mapping))
            }
            x => x,
        }
    }
}

impl ReplacePlaceholders for fol::Atom {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self {
        fol::Atom {
            predicate_symbol: self.predicate_symbol,
            terms: self
                .terms
                .into_iter()
                .map(|t| t.replace_placeholders(mapping))
                .collect(),
        }
    }
}

impl ReplacePlaceholders for fol::Comparison {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self {
        fol::Comparison {
            term: self.term.replace_placeholders(mapping),
            guards: self
                .guards
                .into_iter()
                .map(|g| g.replace_placeholders(mapping))
                .collect(),
        }
    }
}

impl ReplacePlaceholders for fol::Guard {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self {
        fol::Guard {
            relation: self.relation,
            term: self.term.replace_placeholders(mapping),
        }
    }
}

impl ReplacePlaceholders for fol::GeneralTerm {
    fn replace_placeholders(self, mapping: &IndexMap<String, fol::FunctionConstant>) -> Self {
        match self {
            fol::GeneralTerm::SymbolicTerm(fol::SymbolicTerm::Symbol(s)) => {
                if let Some(fc) = mapping.get(&s) {
                    match fc.sort {
                        fol::Sort::General => fol::GeneralTerm::FunctionConstant(s),
                        fol::Sort::Integer => {
                            fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::FunctionConstant(s))
                        }
                        fol::Sort::Symbol => {
                            fol::GeneralTerm::SymbolicTerm(fol::SymbolicTerm::FunctionConstant(s))
                        }
                    }
                } else {
                    fol::GeneralTerm::SymbolicTerm(fol::SymbolicTerm::Symbol(s))
                }
            }
            x => x,
        }
    }
}
