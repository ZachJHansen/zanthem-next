use {
    crate::{
        command_line::Decomposition,
        convenience::apply::Apply,
        syntax_tree::{asp, fol},
        translating::{completion::completion, tau_star::tau_star},
        verifying::{problem::Problem, task::Task},
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

        // TODO: Apply simplifications
        // TODO: Apply equivalence breaking

        let program = completion(tau_star(self.program.clone()).replace_placeholders(&placeholder));

        todo!()
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
