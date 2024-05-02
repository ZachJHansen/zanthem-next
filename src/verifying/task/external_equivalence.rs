use {
    crate::{
        command_line::Decomposition,
        convenience::{
            apply::Apply,
            unbox::{fol::UnboxedFormula, Unbox as _},
        },
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

fn convert_predicate_list(predicates: IndexSet<asp::Predicate>) -> IndexSet<fol::Predicate> {
    let mut result = IndexSet::new();
    for predicate in predicates.iter() {
        result.insert(fol::Predicate::from(predicate.clone()));
    }
    result
}

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
    Other,
}

#[derive(Error, Debug)]
pub enum ProofOutlineError {
    Basic(fol::Formula),
}

#[derive(Debug)]
pub struct ProofOutline {
    pub forward_definitions: Vec<fol::AnnotatedFormula>,
    pub forward_basic_lemmas: Vec<fol::AnnotatedFormula>,
    //pub forward_inductive_lemmas: <fol::AnnotatedFormula>,
    pub backward_definitions: Vec<fol::AnnotatedFormula>,
    pub backward_basic_lemmas: Vec<fol::AnnotatedFormula>,
    //pub backward_inductive_lemmas: Vec<fol::AnnotatedFormula>,
}

impl ProofOutline {
    fn construct(
        spec: fol::Specification,
        mut taken_predicates: IndexSet<fol::Predicate>,
    ) -> Result<Self, ProofOutlineError> {
        let mut forward_definitions: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut backward_definitions: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut forward_basic_lemmas: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut backward_basic_lemmas: Vec<fol::AnnotatedFormula> = Vec::new();
        // process a specification, line by line, adding each definitions predicate to the
        // list of taken predicates before the next iteration
        for anf in spec.formulas.iter() {
            match anf.role {
                fol::Role::Definition => {
                    let predicate = anf.formula.clone().definition(&taken_predicates)?;
                    taken_predicates.insert(predicate);
                    match anf.direction {
                        fol::Direction::Forward => {
                            forward_definitions.push(anf.clone());
                            //forward_definitions.push(AnnotatedFormula::from((anf.clone(), Role::Axiom)));
                        }
                        fol::Direction::Backward => {
                            backward_definitions.push(anf.clone());
                        }
                        fol::Direction::Universal => {
                            let f = anf.clone();
                            forward_definitions.push(f.clone());
                            backward_definitions.push(f);
                        }
                    }
                }
                fol::Role::Lemma => match anf.direction {
                    fol::Direction::Forward => {
                        forward_basic_lemmas.push(anf.clone());
                        //forward_definitions.push(AnnotatedFormula::from((anf.clone(), Role::Axiom)));
                    }
                    fol::Direction::Backward => {
                        backward_basic_lemmas.push(anf.clone());
                    }
                    fol::Direction::Universal => {
                        let f = anf.clone();
                        forward_basic_lemmas.push(f.clone());
                        backward_basic_lemmas.push(f);
                    }
                },
                fol::Role::Assumption | fol::Role::Spec => {
                    return Err(ProofOutlineError::Basic(anf.formula.clone()));
                }
            }
        }
        Ok(ProofOutline {
            forward_definitions,
            forward_basic_lemmas,
            backward_definitions,
            backward_basic_lemmas,
        })
    }
}

trait CheckDefinition {
    // Returns the predicate defined in the LHS of the formula if it is a valid definition, else returns an error
    fn definition(
        self,
        taken_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<fol::Predicate, ProofOutlineError>;
}

impl CheckDefinition for fol::Formula {
    fn definition(
        self,
        taken_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<fol::Predicate, ProofOutlineError> {
        let original = self.clone();
        match self.unbox() {
            UnboxedFormula::QuantifiedFormula {
                quantification:
                    fol::Quantification {
                        quantifier: fol::Quantifier::Forall,
                        variables,
                    },
                formula:
                    fol::Formula::BinaryFormula {
                        connective: fol::BinaryConnective::Equivalence,
                        lhs,
                        rhs,
                    },
            } => {
                match lhs.unbox() {
                    UnboxedFormula::AtomicFormula(fol::AtomicFormula::Atom(a)) => {
                        // check variables has no duplicates
                        let uniques: IndexSet<fol::Variable> =
                            IndexSet::from_iter(variables.clone());
                        if uniques.len() < variables.len() {
                            return Err(ProofOutlineError::Basic(original));
                        }

                        // check predicate is totally fresh
                        let predicate = a.predicate();
                        if taken_predicates.contains(&predicate) {
                            return Err(ProofOutlineError::Basic(original));
                        }

                        // check RHS has no free variables other than those in uniques
                        if rhs.free_variables().difference(&uniques).count() > 0 {
                            return Err(ProofOutlineError::Basic(original));
                        }
                        if uniques.difference(&rhs.free_variables()).count() > 0 {
                            println!("Warning: The universally quantified list of vars contains members which do not occur in RHS.");
                        }

                        // check RHS has no predicates other than taken predicates
                        if rhs.predicates().difference(&taken_predicates).count() > 0 {
                            return Err(ProofOutlineError::Basic(original));
                        }

                        return Ok(predicate);
                    }
                    _ => Err(ProofOutlineError::Basic(original)),
                }
            }
            _ => Err(ProofOutlineError::Basic(original)),
        }
    }
}

impl Display for ProofOutlineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProofOutlineError::Basic(formula) => {
                write!(f, "oh no: {formula} ")?;

                writeln!(f)
            }
        }
    }
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
            ExternalEquivalenceTaskError::Other => {
                write!(f, "temporary error")?;
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

    fn task_predicates(&self) -> IndexSet<fol::Predicate> {
        let mut predicates = self.user_guide.predicates();
        predicates.extend(convert_predicate_list(self.program.predicates()));
        match &self.specification {
            Either::Left(prog) => {
                predicates.extend(convert_predicate_list(prog.predicates()));
            }
            Either::Right(spec) => {
                predicates.extend(spec.predicates());
            }
        }
        predicates
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

        // // TODO: Apply simplifications
        // // TODO: Apply equivalence breaking
        // // TODO: Rename private predicates

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
                    Some(p) => {
                        let anf = AnnotatedFormula {
                            name: format!("completed_definition_of_{p}"),
                            role: Role::Axiom, // maybe we need an Undetermined role
                            formula: formula.clone(),
                        };
                        if !public_predicates.contains(&p) {
                            stable.push(anf);
                        } else {
                            unstable.push(anf); // this isnt strictly accurate since unstable premises are sometimes axioms and sometimes conjectures depending on later context
                        }
                    }
                    _ => {
                        let anf = AnnotatedFormula {
                            name: format!("constraint"),
                            role: Role::Axiom, // maybe we need an Undetermined role
                            formula: formula.clone(),
                        };
                        unstable.push(anf);
                    }
                }
            }

            (stable, unstable)
        };

        let mut stable_premises: Vec<AnnotatedFormula> = Vec::new();
        let mut forward_premises: Vec<AnnotatedFormula> = Vec::new();
        let mut forward_conclusions: Vec<AnnotatedFormula> = Vec::new();
        let mut backward_premises: Vec<AnnotatedFormula> = Vec::new();
        let mut backward_conclusions: Vec<AnnotatedFormula> = Vec::new();

        for formula in self.user_guide.formulas() {
            match formula.role {
                fol::Role::Assumption => {
                    stable_premises.push(AnnotatedFormula::from((formula, Role::Axiom)))
                }
                fol::Role::Spec => todo!(),  // TODO Report user error,
                fol::Role::Lemma => todo!(), // TODO Report user error
                fol::Role::Definition => todo!(), // TODO Report user error
            }
        }

        // // TODO: Avoid cloning
        match self.specification.clone() {
            Either::Left(specification) => {
                let specification =
                    completion(tau_star(specification).replace_placeholders(&placeholder))
                        .expect("tau_star did not create a completable theory");

                let (mut stable, mut unstable) = group(specification);

                // S, F |= B
                stable_premises.append(&mut stable);
                forward_premises.append(&mut unstable.clone());
                for annotated_formula in unstable.iter() {
                    backward_conclusions.push(
                        AnnotatedFormula {
                            name: annotated_formula.name.clone(),
                            role: Role::Conjecture,
                            formula: annotated_formula.formula.clone(),
                        }
                    );
                }
            }

            Either::Right(specification) => {
                for formula in specification.formulas {
                    match formula {
                        fol::AnnotatedFormula {
                            role: fol::Role::Assumption,
                            direction,
                            formula: ref f,
                            ..
                        } => match direction {
                            fol::Direction::Universal => stable_premises.push(AnnotatedFormula::from((formula, Role::Axiom))),
                            fol::Direction::Forward => forward_premises.push(AnnotatedFormula::from((formula, Role::Axiom))),
                            fol::Direction::Backward => println!("A backward assumption has no effect in this context. Ignoring formula {}", f),
                        },

                        fol::AnnotatedFormula {
                            role: fol::Role::Spec,
                            direction,
                            ..
                        } => match direction {
                            fol::Direction::Universal => {
                                forward_premises.push(AnnotatedFormula::from((formula.clone(), Role::Axiom)));
                                backward_conclusions.push(AnnotatedFormula::from((formula, Role::Conjecture)));
                            },
                            fol::Direction::Forward => {
                                forward_premises.push(AnnotatedFormula::from((formula, Role::Axiom)));
                            },
                            fol::Direction::Backward => {
                                backward_conclusions.push(AnnotatedFormula::from((formula, Role::Conjecture)));
                            },
                        },
                        
                        _ => {
                            return Err(ExternalEquivalenceTaskError::Other);
                        },
                    }
                }
            },
        }

        let program = completion(tau_star(self.program.clone()).replace_placeholders(&placeholder))
            .expect("tau_star did not create a completable theory");

        let (mut stable, mut unstable) = group(program);

        // S, B |= F
        stable_premises.append(&mut stable);
        backward_premises.append(&mut unstable.clone());
        for annotated_formula in unstable.iter() {
            forward_conclusions.push(
                AnnotatedFormula {
                    name: annotated_formula.name.clone(),
                    role: Role::Conjecture,
                    formula: annotated_formula.formula.clone(),
                }
            );
        }

        // // TODO Avoid clone
        let proof_outline =
            match ProofOutline::construct(self.proof_outline.clone(), self.task_predicates()) {
                Ok(outline) => Ok(outline),
                Err(_) => Err(ExternalEquivalenceTaskError::Other),
            }?;

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
            let mut forward_sequence = Problem::from_components(
                stable_premises.clone(),
                forward_premises,
                forward_conclusions,
                proof_outline.forward_definitions,
                proof_outline.forward_basic_lemmas,
            );
            problems.append(&mut forward_sequence);
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            let mut backward_sequence = Problem::from_components(
                stable_premises,
                backward_premises,
                backward_conclusions,
                proof_outline.backward_definitions,
                proof_outline.backward_basic_lemmas,
            );
            problems.append(&mut backward_sequence);
        }

        let result: Vec<Problem> = problems
        .into_iter()
        .map(|p: Problem| match self.decomposition {
            Decomposition::Independent => p.decompose_independent(),
            Decomposition::Sequential => p.decompose_sequential(),
        })
        .flatten()
        .collect();

        //println!("{} problems now", result.len());

        Ok(result)

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
