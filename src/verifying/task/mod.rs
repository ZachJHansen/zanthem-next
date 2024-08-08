pub mod derivation;
pub mod external_equivalence;
pub mod strong_equivalence;

use {
    crate::{
        convenience::unbox::{fol::UnboxedFormula, Unbox as _},
        syntax_tree::fol,
        verifying::problem::{AnnotatedFormula, Problem, Role},
    },
    indexmap::IndexSet,
    thiserror::Error,
};

pub trait Task {
    type Error;
    fn decompose(self) -> Result<Vec<Problem>, Self::Error>;
}

// If all the conjectures are proven,
// then all consequences can added as axioms to the next proof step
// A basic lemma F has conjectures [F] and consequences [F]
// An inductive lemma F has conjectures [Base, Step] and axioms [F]
#[derive(Clone, Debug, PartialEq)]
pub struct GeneralLemma {
    pub conjectures: Vec<AnnotatedFormula>,
    pub consequences: Vec<AnnotatedFormula>,
}

impl fol::AnnotatedFormula {
    fn general_lemma(self) -> Result<GeneralLemma, ProofOutlineError> {
        match self.role {
            fol::Role::Lemma => Ok(GeneralLemma {
                conjectures: vec![AnnotatedFormula::from((self.clone(), Role::Conjecture))],
                consequences: vec![AnnotatedFormula::from((self.clone(), Role::Axiom))],
            }),
            fol::Role::InductiveLemma => {
                let (base, step) = self.formula.clone().inductive_lemma()?;
                let base_annotated = fol::AnnotatedFormula {
                    role: fol::Role::Lemma,
                    direction: self.direction,
                    name: format!("{}_base_case", self.name),
                    formula: base,
                };
                let step_annotated = fol::AnnotatedFormula {
                    role: fol::Role::Lemma,
                    direction: self.direction,
                    name: format!("{}_inductive_step", self.name),
                    formula: step,
                };
                Ok(GeneralLemma {
                    conjectures: vec![
                        AnnotatedFormula::from((base_annotated, Role::Conjecture)),
                        AnnotatedFormula::from((step_annotated, Role::Conjecture)),
                    ],
                    consequences: vec![AnnotatedFormula::from((self, Role::Axiom))],
                })
            }
            fol::Role::Assumption | fol::Role::Definition | fol::Role::Spec => {
                unreachable!("this formula is not a lemma")
            }
        }
    }
}

#[derive(Error, Debug, PartialEq)]
pub enum ProofOutlineError {
    #[error("the definition `{0}` contains duplicated variables in outermost quantification")]
    DuplicatedVariables(fol::Formula),
    #[error("predicate `{0}` is taken - definitions require fresh predicates")]
    TakenPredicate(fol::Predicate),
    #[error("the definition `{0}` contains free variables in the RHS")]
    FreeRhsVariables(fol::Formula),
    #[error("undefined predicate - {predicate:?} occurs for the first time in the RHS of definition {definition:?}")]
    UndefinedRhsPredicate {
        definition: fol::Formula,
        predicate: fol::Predicate,
    },
    #[error("the inductive lemma `{0}` is malformed")]
    MalformedInductiveLemma(fol::Formula),
    #[error("there was an issue with formula `{0}` in the proof outline")]
    Basic(fol::Formula),
}

#[derive(Clone, Debug, PartialEq)]
pub struct ProofOutline {
    pub forward_definitions: Vec<fol::AnnotatedFormula>,
    pub forward_lemmas: Vec<GeneralLemma>,
    pub backward_definitions: Vec<fol::AnnotatedFormula>,
    pub backward_lemmas: Vec<GeneralLemma>,
}

impl ProofOutline {
    fn construct(
        spec: fol::Specification,
        mut taken_predicates: IndexSet<fol::Predicate>,
    ) -> Result<Self, ProofOutlineError> {
        let mut forward_definitions: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut backward_definitions: Vec<fol::AnnotatedFormula> = Vec::new();
        let mut forward_lemmas: Vec<GeneralLemma> = Vec::new();
        let mut backward_lemmas: Vec<GeneralLemma> = Vec::new();
        // process a specification, line by line, adding each definition's predicate to the
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
                fol::Role::Lemma | fol::Role::InductiveLemma => {
                    let general_lemma = anf.clone().general_lemma()?;
                    match anf.direction {
                        fol::Direction::Forward => {
                            forward_lemmas.push(general_lemma);
                        }
                        fol::Direction::Backward => {
                            backward_lemmas.push(general_lemma);
                        }
                        fol::Direction::Universal => {
                            forward_lemmas.push(general_lemma.clone());
                            backward_lemmas.push(general_lemma);
                        }
                    }
                }
                fol::Role::Assumption | fol::Role::Spec => {
                    return Err(ProofOutlineError::Basic(anf.formula.clone()));
                }
            }
        }
        Ok(ProofOutline {
            forward_definitions,
            forward_lemmas,
            backward_definitions,
            backward_lemmas,
        })
    }
}

trait CheckInternal {
    // Returns the predicate defined in the LHS of the formula if it is a valid definition, else returns an error
    fn definition(
        self,
        taken_predicates: &IndexSet<fol::Predicate>,
    ) -> Result<fol::Predicate, ProofOutlineError>;

    // Returns the base case and inductive step formulas if the formula is a valid inductive lemma, else returns an error
    fn inductive_lemma(self) -> Result<(fol::Formula, fol::Formula), ProofOutlineError>;
}

impl CheckInternal for fol::Formula {
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
                            return Err(ProofOutlineError::DuplicatedVariables(original));
                        }

                        // check predicate is totally fresh
                        let predicate = a.predicate();
                        if taken_predicates.contains(&predicate) {
                            return Err(ProofOutlineError::TakenPredicate(predicate));
                        }

                        // check RHS has no free variables other than those in uniques
                        if rhs.free_variables().difference(&uniques).count() > 0 {
                            return Err(ProofOutlineError::FreeRhsVariables(original));
                        }
                        if uniques.difference(&rhs.free_variables()).count() > 0 {
                            println!("Warning: The universally quantified list of vars contains members which do not occur in RHS.");
                        }

                        // check RHS has no predicates other than taken predicates
                        // this should ensure no recursion through definition sequence
                        if let Some(predicate) =
                            rhs.predicates().difference(taken_predicates).next()
                        {
                            return Err(ProofOutlineError::UndefinedRhsPredicate {
                                definition: original,
                                predicate: predicate.clone(),
                            });
                        }

                        Ok(predicate)
                    }
                    _ => Err(ProofOutlineError::Basic(original)),
                }
            }
            _ => Err(ProofOutlineError::Basic(original)),
        }
    }

    fn inductive_lemma(self) -> Result<(fol::Formula, fol::Formula), ProofOutlineError> {
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
                        connective: fol::BinaryConnective::Implication,
                        lhs,
                        rhs,
                    },
            } => match lhs.clone().unbox() {
                UnboxedFormula::AtomicFormula(fol::AtomicFormula::Comparison(
                    fol::Comparison { term, guards },
                )) => {
                    if guards.len() != 1 || variables.len() != 1 {
                        return Err(ProofOutlineError::MalformedInductiveLemma(original));
                    }

                    let varset: IndexSet<fol::Variable> = IndexSet::from_iter(variables.clone());
                    if varset != rhs.free_variables() {
                        return Err(ProofOutlineError::MalformedInductiveLemma(original));
                    }

                    let induction_variable = variables[0].clone();
                    if induction_variable.sort != fol::Sort::Integer {
                        return Err(ProofOutlineError::MalformedInductiveLemma(original));
                    }

                    let guard = guards[0].clone();
                    let intended_induction_term =
                        fol::IntegerTerm::Variable(induction_variable.name.clone());
                    match term {
                        fol::GeneralTerm::IntegerTerm(induction_term) => {
                            if induction_term != intended_induction_term {
                                return Err(ProofOutlineError::MalformedInductiveLemma(original));
                            }

                            match guard {
                                fol::Guard {
                                    relation: fol::Relation::GreaterEqual,
                                    term:
                                        fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(n)),
                                } => {
                                    let least_term =
                                        fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::Numeral(n));
                                    let base_case = rhs
                                        .clone()
                                        .substitute(induction_variable.clone(), least_term);

                                    let inductive_step_antecedent = fol::Formula::BinaryFormula {
                                        connective: fol::BinaryConnective::Conjunction,
                                        lhs: lhs.clone(),
                                        rhs: rhs.clone(),
                                    };

                                    let successor = fol::GeneralTerm::IntegerTerm(
                                        fol::IntegerTerm::BinaryOperation {
                                            op: fol::BinaryOperator::Add,
                                            lhs: induction_term.clone().into(),
                                            rhs: fol::IntegerTerm::Numeral(1).into(),
                                        },
                                    );

                                    let inductive_step_consequent =
                                        rhs.substitute(induction_variable.clone(), successor);
                                    let inductive_step = fol::Formula::QuantifiedFormula {
                                        quantification: fol::Quantification {
                                            quantifier: fol::Quantifier::Forall,
                                            variables: vec![induction_variable],
                                        },
                                        formula: fol::Formula::BinaryFormula {
                                            connective: fol::BinaryConnective::Implication,
                                            lhs: inductive_step_antecedent.into(),
                                            rhs: inductive_step_consequent.into(),
                                        }
                                        .into(),
                                    };

                                    Ok((base_case, inductive_step))
                                }
                                _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
                            }
                        }
                        _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
                    }
                }
                _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
            },
            _ => Err(ProofOutlineError::MalformedInductiveLemma(original)),
        }
    }
}

#[cfg(test)]
mod tests {
    use {
        super::ProofOutlineError,
        crate::{syntax_tree::fol, verifying::task::CheckInternal},
        frame_support::assert_err,
        indexmap::IndexSet,
    };

    #[test]
    fn check_correct_definition() {
        for (src, target) in [
            (
                "forall X ( p(X) <-> 1 < 2 )",
                fol::Predicate {
                    symbol: "p".to_string(),
                    arity: 1,
                },
            ),
            (
                "forall X Y$i ( pred(X, Y$i) <-> exists N$i (X = N$i and t(X) or t(Y$i)) )",
                fol::Predicate {
                    symbol: "pred".to_string(),
                    arity: 2,
                },
            ),
        ] {
            let taken_predicates: IndexSet<fol::Predicate> =
                IndexSet::from_iter(vec![fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }]);
            let formula: fol::Formula = src.parse().unwrap();
            assert_eq!(formula.definition(&taken_predicates).unwrap(), target)
        }
    }

    #[test]
    fn check_incorrect_definition() {
        for (src, target) in [
            (
                "forall X Y X ( p(X) <-> 1 < 2 )",
                ProofOutlineError::DuplicatedVariables(
                    "forall X Y X ( p(X) <-> 1 < 2 )".parse().unwrap(),
                ),
            ),
            (
                "forall X ( t(X) <-> 1 < 2 )",
                ProofOutlineError::TakenPredicate(fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }),
            ),
            (
                "forall Z1 Z2 ( ancestor(Z1, Z2) <-> t(X) and t(Z2) )",
                ProofOutlineError::FreeRhsVariables(
                    "forall Z1 Z2 ( ancestor(Z1, Z2) <-> t(X) and t(Z2) )"
                        .parse()
                        .unwrap(),
                ),
            ),
            (
                "forall Z1 Z2 ( ancestor(Z1, Z2) <-> ancestor(Z1, Z2) )",
                ProofOutlineError::UndefinedRhsPredicate {
                    definition: "forall Z1 Z2 ( ancestor(Z1, Z2) <-> ancestor(Z1, Z2) )"
                        .parse()
                        .unwrap(),
                    predicate: fol::Predicate {
                        symbol: "ancestor".to_string(),
                        arity: 2,
                    },
                },
            ),
        ] {
            let taken_predicates: IndexSet<fol::Predicate> =
                IndexSet::from_iter(vec![fol::Predicate {
                    symbol: "t".to_string(),
                    arity: 1,
                }]);
            let formula: fol::Formula = src.parse().unwrap();
            assert_err!(formula.definition(&taken_predicates), target)
        }
    }

    #[test]
    fn test_correct_inductive_lemma() {
        for (src, base, step) in [
            (
                "forall I$i ( I$i >= 5 -> p(I$i) )",
                "p(5)",
                "forall I$i ( (I$i >= 5 and p(I$i)) -> p(I$i+1) )",
            ),
            (
                "forall N$i ( N$i >= 1 -> squareLEb(N$i) )",
                "squareLEb(1)",
                "forall N$i ( (N$i >= 1 and squareLEb(N$i)) -> squareLEb(N$i+1) )",
            ),
            (
                "forall I$ ( I$ >= 5 -> (p(I$) and not q(I$,5)) )",
                "p(5) and not q(5,5)",
                "forall I$ ( ( I$ >= 5 and (p(I$) and not q(I$,5)) ) -> ( p(I$+1) and not q(I$+1,5) ) )",
            ),
        ] {
            let formula: fol::Formula = src.parse().unwrap();
            let (base_result, step_result) = formula.inductive_lemma().unwrap();
            let (base_target, step_target): (fol::Formula, fol::Formula) = (base.parse().unwrap(), step.parse().unwrap());
            assert_eq!((base_result.clone(), step_result.clone()), (base_target.clone(), step_target.clone()), "\n({base_result},{step_result})\n != ({base_target},{step_target})")
        }
    }

    #[test]
    fn check_incorrect_inductive_lemma() {
        for (src, target) in [
            (
                "forall X ( X >= 0 -> p(X) )",
                ProofOutlineError::MalformedInductiveLemma(
                    "forall X ( X >= 0 -> p(X) )".parse().unwrap(),
                ),
            ),
            (
                "forall X$i ( X$i > 0 -> p(X$i) )",
                ProofOutlineError::MalformedInductiveLemma(
                    "forall X$i ( X$i > 0 -> p(X$i) )".parse().unwrap(),
                ),
            ),
            (
                "forall X$i Y$i ( X$i >= 0 -> p(X$i, Y$i) )",
                ProofOutlineError::MalformedInductiveLemma(
                    "forall X$i Y$i ( X$i >= 0 -> p(X$i, Y$i) )"
                        .parse()
                        .unwrap(),
                ),
            ),
        ] {
            let formula: fol::Formula = src.parse().unwrap();
            assert_err!(formula.inductive_lemma(), target)
        }
    }

    // #[test]
    // fn test_general_lemma() {

    // }

    // #[test]
    // fn test_proof_outline_constructor() {
    //     let f1: fol::AnnotatedFormula =
    //         "definition[p]: forall X (p(X) <-> exists Y$i (X = Y$i and 0 <= Y$i <= 10))"
    //             .parse()
    //             .unwrap();
    //     let f2: fol::AnnotatedFormula = "lemma(backward)[l1]: exists X (X = n$i)".parse().unwrap();
    //     let f3: fol::AnnotatedFormula = "definition(forward)[q]: forall X (q(X) <-> p(X) or t(X))"
    //         .parse()
    //         .unwrap();
    //     let f4: fol::AnnotatedFormula = "lemma[l2]: n$i > 0".parse().unwrap();
    //     let f5: fol::AnnotatedFormula =
    //         "inductive-lemma[il1]: forall N$i ( N$i >= 0 -> square(N$i) )"
    //             .parse()
    //             .unwrap();
    //     let f6: fol::AnnotatedFormula = "lemma[il1_base_case]: square(0)".parse().unwrap();
    //     let f7: fol::AnnotatedFormula =
    //         "lemma[il1_inductive_step]: forall N$i ( N$i >= 0 and square(N$i) -> square(N$i+1) )"
    //             .parse()
    //             .unwrap();
    //     let il1 = GeneralLemma {
    //         conjectures: vec![f6, f7],
    //         consequences: vec![f5],
    //     };

    //     let spec = fol::Specification {
    //         formulas: vec![f1.clone(), f2.clone(), f3.clone(), f4.clone(), f5],
    //     };
    //     let taken_predicates: IndexSet<fol::Predicate> =
    //         IndexSet::from_iter(vec![fol::Predicate {
    //             symbol: "t".to_string(),
    //             arity: 1,
    //         }]);
    //     let proof_outline = ProofOutline::construct(spec, taken_predicates).unwrap();
    //     let target = ProofOutline {
    //         forward_definitions: vec![f1.clone(), f3],
    //         forward_basic_lemmas: vec![f4.clone()],
    //         forward_inductive_lemmas: vec![il1.clone()],
    //         backward_definitions: vec![f1],
    //         backward_basic_lemmas: vec![f2, f4],
    //         backward_inductive_lemmas: vec![il1],
    //     };
    //     assert_eq!(proof_outline, target)
    // }
}
