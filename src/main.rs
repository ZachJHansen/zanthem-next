pub mod command_line;
pub mod convenience;
pub mod formatting;
pub mod parsing;
pub mod simplifying;
pub mod syntax_tree;
pub mod translating;

use crate::convenience::unbox::fol::UnboxedFormula;
use crate::convenience::unbox::Unbox;

use {
    crate::{
        command_line::{Arguments, Command, Translation},
        syntax_tree::{asp, fol, fol::*},
        translating::tau_star::tau_star,
    },
    anyhow::{Context, Result},
    clap::Parser as _,
    std::{fs::read_to_string, collections::HashSet},
    translating::gamma::gamma,
};

fn inductive_lemma_handle(lemma: AnnotatedFormula) -> Option<(AnnotatedFormula, AnnotatedFormula)> {
    match lemma {
        AnnotatedFormula {
            role: Role::InductiveLemma,
            direction,
            name,
            formula,
        } => {
            match formula.unbox() {
                UnboxedFormula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier: Quantifier::Forall,
                            variables,
                        },
                    formula:
                        Formula::BinaryFormula {
                            connective: BinaryConnective::Implication,
                            lhs,
                            rhs,
                        },
                } => {
                    match lhs.clone().unbox() {
                        UnboxedFormula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                            term,
                            guards,
                        })) => {
                            if guards.len() != 1 || variables.len() != 1 {
                                return None;
                            }

                            if HashSet::from_iter(variables.clone()) != rhs.free_variables() {
                                return None;
                            }

                            let induction_variable = variables[0].clone();
                            if induction_variable.sort != Sort::Integer {
                                return None;
                            }

                            let guard = guards[0].clone();          
                            let intended_induction_term = IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(induction_variable.name.clone()));
                            match term {
                                GeneralTerm::IntegerTerm(induction_term) => {
                                    if induction_term != intended_induction_term {
                                        return None;
                                    }

                                    match guard {
                                        Guard {
                                            relation: Relation::GreaterEqual,
                                            term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(n))),
                                        } => {
                                            let least_term = GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(n)));
                                            let base_case = rhs.clone().substitute(induction_variable.clone(), least_term);
    
                                            let inductive_step_antecedent = Formula::BinaryFormula {
                                                connective: BinaryConnective::Conjunction,
                                                lhs: rhs.clone(),
                                                rhs: lhs.clone(),
                                            };

                                            let successor = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                                                op: BinaryOperator::Add,
                                                lhs: induction_term.clone().into(),
                                                rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                                            });

                                            let inductive_step_consequent = rhs.substitute(induction_variable.clone(), successor);
                                            let inductive_step = Formula::QuantifiedFormula {
                                                quantification: Quantification {
                                                    quantifier: Quantifier::Forall,
                                                    variables: vec![induction_variable],
                                                },
                                                formula: Formula::BinaryFormula {
                                                    connective: BinaryConnective::Implication,
                                                    lhs: inductive_step_antecedent.into(),
                                                    rhs: inductive_step_consequent.into(),
                                                }.into(),
                                            };
    
                                            let base_case_annotated = AnnotatedFormula {
                                                name: FormulaName(Some(format!("{name}_base_case"))),
                                                role: Role::Conjecture,
                                                direction: direction.clone(),
                                                formula: base_case,
                                            };

                                            let inductive_step_annotated = AnnotatedFormula {
                                                name: FormulaName(Some(format!("{name}_inductive_step"))),
                                                role: Role::Conjecture,
                                                direction,
                                                formula: inductive_step,
                                            };

                                            let cases = (base_case_annotated, inductive_step_annotated);
                                            Some(cases)
                                        },
                                        _ => None,
                                    }
                                },
                                _ => None,
                            }
                        },
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Translate { with, input } => {
            let content = read_to_string(&input)
                .with_context(|| format!("could not read file `{}`", input.display()))?;

            match with {
                Translation::Gamma => {
                    let theory: fol::Theory = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let theory = gamma(theory);

                    print!("{theory}")
                }

                Translation::TauStar => {
                    let program: asp::Program = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let theory = tau_star(program);
                    // let thing: fol::AnnotatedFormula =
                    //     "definition[comp_1]: forall X (composite(X) <-> q(X))."
                    //         .parse()
                    //         .unwrap();
                    // println!("{:?}", thing);
                    //print!("{theory}")

                    let thing: fol::AnnotatedFormula = "inductive-lemma[p_int]: forall I$ (I$ >= 5 -> (p(I$) and not q(I$,5))).".parse().unwrap();
                    let res = inductive_lemma_handle(thing.clone());
                    match res {
                        Some((thing1, thing2)) => {
                            println!("{}", thing1.formula);
                            println!("{}", thing2.formula);
                        },
                        None => println!("not a properly formatted inductive lemma"),
                    }
                    
                }
            }

            Ok(())
        }
    }
}
