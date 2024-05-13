use {
    crate::{
        command_line::Decomposition,
        convenience::apply::Apply,
        simplifying::fol::ht::{simplify, simplify_theory},
        syntax_tree::{asp, fol},
        translating::{completion::completion, tau_star::tau_star},
        verifying::{
            problem::{self, AnnotatedFormula, Problem},
            task::{ProofOutline, Task},
        },
    },
    either::Either,
    indexmap::{IndexMap, IndexSet},
    thiserror::Error,
};

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

trait RenamePredicates {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self;
}

impl RenamePredicates for fol::Theory {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        fol::Theory {
            formulas: self
                .formulas
                .into_iter()
                .map(|f| f.rename_predicates(mapping))
                .collect(),
        }
    }
}

impl RenamePredicates for fol::Formula {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        self.apply(&mut |formula| match formula {
            fol::Formula::AtomicFormula(a) => {
                fol::Formula::AtomicFormula(a.rename_predicates(mapping))
            }
            x => x,
        })
    }
}

impl RenamePredicates for fol::AtomicFormula {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        match self {
            fol::AtomicFormula::Atom(a) => fol::AtomicFormula::Atom(a.rename_predicates(mapping)),
            x => x,
        }
    }
}

impl RenamePredicates for fol::Atom {
    fn rename_predicates(self, mapping: &IndexMap<fol::Predicate, String>) -> Self {
        match mapping.get(&self.predicate()) {
            Some(name_extension) => fol::Atom {
                predicate_symbol: format!("{}_{}", self.predicate_symbol, name_extension),
                terms: self.terms,
            },
            None => self,
        }
    }
}

#[derive(Error, Debug)]
pub enum ExternalEquivalenceTaskError {
    #[error("could not parse the proof outline: {0}")]
    ProofOutline(String),
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

impl Task for ExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;

    fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
        //self.ensure_input_and_output_predicates_are_disjoint()?;
        //self.ensure_program_heads_do_not_contain_input_predicates()?;

        // TODO: Ensure there's not a$i and a$g in the user guide
        let placeholder = self
            .user_guide
            .placeholders()
            .into_iter()
            .map(|p| (p.name.clone(), p))
            .collect();

        let public_predicates = self.user_guide.public_predicates();

        let mut program_private_predicates: IndexSet<fol::Predicate> = IndexSet::new();
        for predicate in self.program.predicates() {
            let candidate = fol::Predicate {
                symbol: predicate.symbol,
                arity: predicate.arity,
            };
            if !public_predicates.contains(&candidate) {
                program_private_predicates.insert(candidate);
            }
        }

        let mut specification_private_predicates: IndexSet<fol::Predicate> = IndexSet::new();
        match self.specification.clone() {
            Either::Left(lp) => {
                for predicate in lp.predicates() {
                    let candidate = fol::Predicate {
                        symbol: predicate.symbol,
                        arity: predicate.arity,
                    };
                    if !public_predicates.contains(&candidate) {
                        specification_private_predicates.insert(candidate);
                    }
                }
            }
            Either::Right(_) => (),
        }

        let conflicting_predicates: IndexSet<fol::Predicate> = program_private_predicates
            .intersection(&specification_private_predicates)
            .cloned()
            .collect();

        let mut program_renaming_map = IndexMap::new();
        let mut specification_renaming_map = IndexMap::new();
        for predicate in conflicting_predicates {
            specification_renaming_map.insert(predicate.clone(), "1".to_string());
            program_renaming_map.insert(predicate, "2".to_string());
        }

        // // TODO: Apply simplifications

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

        // Translate a first-order theory corresponding to the completion of an ASP program
        // into a control language specification
        let control_translate = |theory: fol::Theory| {
            let mut control_formulas: Vec<fol::AnnotatedFormula> = Vec::new();

            for formula in theory.formulas {
                match head_predicate(formula.clone()) {
                    Some(p) => {
                        if !public_predicates.contains(&p) {
                            control_formulas.push(fol::AnnotatedFormula {
                                name: format!("completed_definition_of_{}_{}", p.symbol, p.arity),
                                role: fol::Role::Assumption,
                                direction: fol::Direction::Universal,
                                formula: formula.clone(),
                            });
                        } else {
                            control_formulas.push(fol::AnnotatedFormula {
                                name: format!("completed_definition_of_{}_{}", p.symbol, p.arity),
                                role: fol::Role::Spec,
                                direction: fol::Direction::Universal,
                                formula: formula.clone(),
                            });
                        }
                    }
                    _ => control_formulas.push(fol::AnnotatedFormula {
                        name: "constraint".to_string(),
                        role: fol::Role::Spec,
                        direction: fol::Direction::Universal,
                        formula: formula.clone(),
                    }),
                }
            }

            control_formulas
        };

        let program = completion(tau_star(self.program.clone()).replace_placeholders(&placeholder))
            .expect("tau_star did not create a completable theory");
        let right = match self.simplify {
            true => control_translate(
                simplify_theory(program, true).rename_predicates(&program_renaming_map),
            ),
            false => control_translate(program.rename_predicates(&program_renaming_map)),
        };

        let left = match self.specification.clone() {
            Either::Left(specification) => {
                let specification =
                    completion(tau_star(specification).replace_placeholders(&placeholder))
                        .expect("tau_star did not create a completable theory");
                match self.simplify {
                    true => control_translate(
                        simplify_theory(specification, true)
                            .rename_predicates(&specification_renaming_map),
                    ),
                    false => control_translate(
                        specification.rename_predicates(&specification_renaming_map),
                    ),
                }
            }
            Either::Right(specification) => match self.simplify {
                true => {
                    let mut simplified = Vec::new();
                    for anf in specification.formulas {
                        simplified.push(fol::AnnotatedFormula {
                            role: anf.role,
                            direction: anf.direction,
                            name: anf.name,
                            formula: simplify(anf.formula, true),
                        });
                    }
                    simplified
                }
                false => specification.formulas,
            },
        };

        let mut taken_predicates = self.user_guide.input_predicates();
        for anf in left.iter() {
            taken_predicates.extend(anf.formula.predicates());
        }
        for anf in right.iter() {
            taken_predicates.extend(anf.formula.predicates());
        }

        let proof_outline = match ProofOutline::construct(self.proof_outline, taken_predicates) {
            Ok(outline) => Ok(outline),
            Err(e) => Err(ExternalEquivalenceTaskError::ProofOutline(e.to_string())),
        }?;

        // TODO: Add more error handing

        // TODO: apply simplifications

        let mut user_guide_assumptions = vec![];
        for formula in self.user_guide.formulas() {
            match formula.role {
                fol::Role::Assumption => user_guide_assumptions.push(formula),
                fol::Role::Spec => todo!(),  // TODO Report user error,
                fol::Role::Lemma => todo!(), // TODO Report user error
                fol::Role::Definition => todo!(), // TODO Report user error
                fol::Role::InductiveLemma => todo!(), // TODO Report user error
            }
        }

        let validated = ValidatedExternalEquivalenceTask {
            left,
            right,
            user_guide_assumptions,
            proof_outline,
            decomposition: self.decomposition,
            direction: self.direction,
            break_equivalences: self.break_equivalences,
        };
        validated.decompose()
    }
}

struct ValidatedExternalEquivalenceTask {
    pub left: Vec<fol::AnnotatedFormula>,
    pub right: Vec<fol::AnnotatedFormula>,
    pub user_guide_assumptions: Vec<fol::AnnotatedFormula>,
    pub proof_outline: ProofOutline,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
    pub break_equivalences: bool,
}

impl Task for ValidatedExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;

    fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
        let mut stable_premises: Vec<problem::AnnotatedFormula> = Vec::new();
        let mut forward_premises: Vec<problem::AnnotatedFormula> = Vec::new();
        let mut forward_conclusions: Vec<problem::AnnotatedFormula> = Vec::new();
        let mut backward_premises: Vec<problem::AnnotatedFormula> = Vec::new();
        let mut backward_conclusions: Vec<problem::AnnotatedFormula> = Vec::new();

        for assumption in self.user_guide_assumptions {
            stable_premises.push(AnnotatedFormula::from((assumption, problem::Role::Axiom)));
        }

        // S, F |= B
        for formula in self.left {
            match formula {
                fol::AnnotatedFormula {
                    role: fol::Role::Assumption,
                    direction,
                    formula: ref f,
                    ..
                } => match direction {
                    fol::Direction::Universal => stable_premises
                        .push(AnnotatedFormula::from((formula, problem::Role::Axiom))),
                    fol::Direction::Forward => forward_premises
                        .push(AnnotatedFormula::from((formula, problem::Role::Axiom))),
                    fol::Direction::Backward => println!(
                        "A backward assumption has no effect in this context. Ignoring formula {}",
                        f
                    ),
                },

                fol::AnnotatedFormula {
                    role: fol::Role::Spec,
                    direction,
                    ..
                } => match direction {
                    fol::Direction::Universal => {
                        forward_premises.push(AnnotatedFormula::from((
                            formula.clone(),
                            problem::Role::Axiom,
                        )));
                        if self.break_equivalences {
                            let conjectures = formula.break_equivalences();
                            for c in conjectures {
                                backward_conclusions
                                    .push(AnnotatedFormula::from((c, problem::Role::Conjecture)));
                            }
                        } else {
                            backward_conclusions
                                .push(AnnotatedFormula::from((formula, problem::Role::Conjecture)));
                        }
                    }
                    fol::Direction::Forward => {
                        forward_premises
                            .push(AnnotatedFormula::from((formula, problem::Role::Axiom)));
                    }
                    fol::Direction::Backward => {
                        if self.break_equivalences {
                            let conjectures = formula.break_equivalences();
                            for c in conjectures {
                                backward_conclusions
                                    .push(AnnotatedFormula::from((c, problem::Role::Conjecture)));
                            }
                        } else {
                            backward_conclusions
                                .push(AnnotatedFormula::from((formula, problem::Role::Conjecture)));
                        }
                    }
                },

                _ => todo!(), // error
            }
        }

        // S, B |= F
        for formula in self.right {
            match formula {
                fol::AnnotatedFormula {
                    role: fol::Role::Assumption,
                    direction,
                    formula: ref f,
                    ..
                } => match direction {
                    fol::Direction::Universal => stable_premises
                        .push(AnnotatedFormula::from((formula, problem::Role::Axiom))),
                    fol::Direction::Forward => println!(
                        "A forward assumption has no effect in this context. Ignoring formula {}",
                        f
                    ),
                    fol::Direction::Backward => backward_premises
                        .push(AnnotatedFormula::from((formula, problem::Role::Axiom))),
                },

                fol::AnnotatedFormula {
                    role: fol::Role::Spec,
                    direction,
                    ..
                } => match direction {
                    fol::Direction::Universal => {
                        backward_premises.push(AnnotatedFormula::from((
                            formula.clone(),
                            problem::Role::Axiom,
                        )));
                        if self.break_equivalences {
                            let conjectures = formula.break_equivalences();
                            for c in conjectures {
                                forward_conclusions
                                    .push(AnnotatedFormula::from((c, problem::Role::Conjecture)));
                            }
                        } else {
                            forward_conclusions
                                .push(AnnotatedFormula::from((formula, problem::Role::Conjecture)));
                        }
                    }
                    fol::Direction::Forward => {
                        backward_premises
                            .push(AnnotatedFormula::from((formula, problem::Role::Axiom)));
                    }
                    fol::Direction::Backward => {
                        if self.break_equivalences {
                            let conjectures = formula.break_equivalences();
                            for c in conjectures {
                                forward_conclusions
                                    .push(AnnotatedFormula::from((c, problem::Role::Conjecture)));
                            }
                        } else {
                            forward_conclusions
                                .push(AnnotatedFormula::from((formula, problem::Role::Conjecture)));
                        }
                    }
                },

                _ => todo!(), // error
            }
        }

        let task = AssembledExternalEquivalenceTask {
            stable_premises,
            forward_premises,
            forward_conclusions,
            backward_premises,
            backward_conclusions,
            proof_outline: self.proof_outline,
            decomposition: self.decomposition,
            direction: self.direction,
        };
        task.decompose()
    }
}

struct AssembledExternalEquivalenceTask {
    pub stable_premises: Vec<problem::AnnotatedFormula>,
    pub forward_premises: Vec<problem::AnnotatedFormula>,
    pub forward_conclusions: Vec<problem::AnnotatedFormula>,
    pub backward_premises: Vec<problem::AnnotatedFormula>,
    pub backward_conclusions: Vec<problem::AnnotatedFormula>,
    pub proof_outline: ProofOutline,
    pub decomposition: Decomposition,
    pub direction: fol::Direction,
}

impl Task for AssembledExternalEquivalenceTask {
    type Error = ExternalEquivalenceTaskError;

    fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
        let mut problems = Vec::new();
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Forward
        ) {
            let mut forward_sequence = Problem::from_components(
                "forward".to_string(),
                self.stable_premises.clone(),
                self.forward_premises,
                self.forward_conclusions,
                self.proof_outline.forward_lemmas,
                self.proof_outline.forward_definitions,
            );
            problems.append(&mut forward_sequence);
        }
        if matches!(
            self.direction,
            fol::Direction::Universal | fol::Direction::Backward
        ) {
            let mut backward_sequence = Problem::from_components(
                "backward".to_string(),
                self.stable_premises,
                self.backward_premises,
                self.backward_conclusions,
                self.proof_outline.backward_lemmas,
                self.proof_outline.backward_definitions,
            );
            problems.append(&mut backward_sequence);
        }

        let result: Vec<Problem> = problems
            .into_iter()
            .flat_map(|p: Problem| match self.decomposition {
                Decomposition::Independent => p.decompose_independent(),
                Decomposition::Sequential => p.decompose_sequential(),
            })
            .collect();

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use indexmap::IndexMap;

    use super::{
        AssembledExternalEquivalenceTask, Either, ExternalEquivalenceTask, ProofOutline,
        RenamePredicates, Task, ValidatedExternalEquivalenceTask,
    };
    use crate::{
        command_line::Decomposition,
        syntax_tree::{asp, fol},
        verifying::problem,
    };

    #[test]
    fn test_rename_predicates() {
        let mut rename_map = IndexMap::new();
        rename_map.insert(
            fol::Predicate {
                symbol: "p".to_string(),
                arity: 0,
            },
            "2".to_string(),
        );
        let theory: fol::Theory = "p <-> q or t. 1 < 5 or t and not p.".parse().unwrap();
        let renamed_theory = theory.rename_predicates(&rename_map);
        let target: fol::Theory = "p_2 <-> q or t. 1 < 5 or t and not p_2.".parse().unwrap();
        assert_eq!(renamed_theory, target)
    }

    #[test]
    fn test_decompose_external() {
        let program: asp::Program = "p :- t. p :- n < 5. r :- p.".parse().unwrap();
        let spec: asp::Program = "p :- n = 0, not t. r :- p.".parse().unwrap();
        let user_guide: fol::UserGuide =
            "input: t/0. input: n$i. output: r/0. assumption: n$i = 3."
                .parse()
                .unwrap();
        let proof_outline: fol::Specification = "".parse().unwrap();
        let external = ExternalEquivalenceTask {
            specification: Either::Left(spec),
            program,
            user_guide,
            proof_outline,
            decomposition: Decomposition::Independent,
            direction: fol::Direction::Universal,
            simplify: false,
            break_equivalences: false,
        };

        let f1: fol::AnnotatedFormula = "assumption[completed_definition_of_p_1_0]: p_1 <-> exists Z Z1 (Z = n$i and Z1 = 0 and Z = Z1) and not t".parse().unwrap();
        let f2: fol::AnnotatedFormula = "spec[completed_definition_of_r_0]: r <-> p_1"
            .parse()
            .unwrap();
        let f3: fol::AnnotatedFormula = "assumption[completed_definition_of_p_2_0]: p_2 <-> t or exists Z Z1 (Z = n$i and Z1 = 5 and Z < Z1)".parse().unwrap();
        let f4: fol::AnnotatedFormula = "spec[completed_definition_of_r_0]: r <-> p_2"
            .parse()
            .unwrap();
        let user_guide_assumptions: Vec<fol::AnnotatedFormula> =
            vec!["assumption: n$i = 3".parse().unwrap()];
        let proof_outline = ProofOutline {
            forward_definitions: vec![],
            forward_lemmas: vec![],
            backward_definitions: vec![],
            backward_lemmas: vec![],
        };
        let validated = ValidatedExternalEquivalenceTask {
            left: vec![f1, f2],
            right: vec![f3, f4],
            user_guide_assumptions,
            proof_outline,
            decomposition: Decomposition::Independent,
            direction: fol::Direction::Universal,
            break_equivalences: false,
        };

        let src = external.decompose().unwrap();
        let target = validated.decompose().unwrap();
        for i in 0..src.len() {
            let p1 = src[i].clone();
            let p2 = target[i].clone();
            assert_eq!(src, target, "{p1} != {p2}")
        }
    }

    #[test]
    fn test_decompose_validated() {
        let left: Vec<fol::AnnotatedFormula> = vec![
            "assumption[about_n]: n$i > 1".parse().unwrap(),
            "spec: forall X (p(X) <-> q(X))".parse().unwrap(),
        ];
        let right: Vec<fol::AnnotatedFormula> = vec![
            "assumption(backward): n$i != 5".parse().unwrap(),
            "spec[t_or_q]: t or q".parse().unwrap(),
        ];
        let assumption_1: fol::AnnotatedFormula = "assumption: t -> q".parse().unwrap();
        let proof_outline = ProofOutline {
            forward_definitions: vec![],
            backward_definitions: vec![],
            forward_lemmas: vec![],
            backward_lemmas: vec![],
        };
        let validated = ValidatedExternalEquivalenceTask {
            left,
            right,
            user_guide_assumptions: vec![assumption_1],
            proof_outline,
            decomposition: crate::command_line::Decomposition::Sequential,
            direction: fol::Direction::Universal,
            break_equivalences: true,
        };

        let stable_premises: Vec<problem::AnnotatedFormula> = vec![
            problem::AnnotatedFormula {
                name: "assumption".to_string(),
                role: problem::Role::Axiom,
                formula: "t -> q".parse().unwrap(),
            },
            problem::AnnotatedFormula {
                name: "about_n".to_string(),
                role: problem::Role::Axiom,
                formula: "n$i > 1".parse().unwrap(),
            },
        ];
        let forward_premises: Vec<problem::AnnotatedFormula> = vec![problem::AnnotatedFormula {
            name: "spec".to_string(),
            role: problem::Role::Axiom,
            formula: "forall X (p(X) <-> q(X))".parse().unwrap(),
        }];
        let forward_conclusions: Vec<problem::AnnotatedFormula> = vec![problem::AnnotatedFormula {
            name: "t_or_q".to_string(),
            role: problem::Role::Conjecture,
            formula: "t or q".parse().unwrap(),
        }];
        let backward_premises: Vec<problem::AnnotatedFormula> = vec![
            problem::AnnotatedFormula {
                name: "assumption".to_string(),
                role: problem::Role::Axiom,
                formula: "n$i != 5".parse().unwrap(),
            },
            problem::AnnotatedFormula {
                name: "t_or_q".to_string(),
                role: problem::Role::Axiom,
                formula: "t or q".parse().unwrap(),
            },
        ];
        let backward_conclusions: Vec<problem::AnnotatedFormula> = vec![
            problem::AnnotatedFormula {
                name: "_forward".to_string(),
                role: problem::Role::Conjecture,
                formula: "forall X ( p(X) -> q(X) )".parse().unwrap(),
            },
            problem::AnnotatedFormula {
                name: "_backward".to_string(),
                role: problem::Role::Conjecture,
                formula: "forall X ( p(X) <- q(X) )".parse().unwrap(),
            },
        ];
        let proof_outline = ProofOutline {
            forward_definitions: vec![],
            backward_definitions: vec![],
            forward_lemmas: vec![],
            backward_lemmas: vec![],
        };

        let assembled = AssembledExternalEquivalenceTask {
            stable_premises,
            forward_premises,
            forward_conclusions,
            backward_premises,
            backward_conclusions,
            proof_outline,
            decomposition: crate::command_line::Decomposition::Sequential,
            direction: fol::Direction::Universal,
        };

        let src = validated.decompose().unwrap();
        let target = assembled.decompose().unwrap();
        for i in 0..src.len() {
            let p1 = src[i].clone();
            let p2 = target[i].clone();
            assert_eq!(src, target, "{p1} != {p2}")
        }
    }
}
