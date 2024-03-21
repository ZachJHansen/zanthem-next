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
    std::fs::read_to_string,
    translating::gamma::gamma,
};

fn inductive_lemma_handle(lemma: AnnotatedFormula) -> (AnnotatedFormula, AnnotatedFormula) {
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
                            let induction_variable = variables[0].clone();  // TODO - check length and type of variables list
                            let guard = guards[0].clone();          // TODO - check length of guards list
                            let induction_term = IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(induction_variable.name.clone()));
                            if GeneralTerm::IntegerTerm(induction_term.clone()) == term {
                                match guard {
                                    Guard {
                                        relation: Relation::GreaterEqual,
                                        term: least_term,
                                    } => {
                                        let base_case = rhs.clone().substitute(induction_variable, least_term);

                                        let inductive_step_antecedent = Formula::BinaryFormula {
                                            connective: BinaryConnective::Conjunction,
                                            lhs: rhs.clone(),
                                            rhs: lhs.clone(),
                                        };
                                    },
                                    _ => todo!("wrong form"),
                                }
                            }
                            todo!()
                        },
                        _ => todo!("wrong form"),
                    }
                    // let induction_variable = Variable { name: "N".to_string(), sort: Sort::Integer };
                    // let induction_term = IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable("N".to_string()));

                    // // TODO - check if rhs contains free variables other than N$

                    // let least_term = GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(100000000000000)));

                    // let base_case = rhs.clone().substitute(induction_variable, least_term);

                    // let inductive_step_antecedent = Formula::BinaryFormula {
                    //     connective: BinaryConnective::Conjunction,
                    //     lhs: rhs.clone(),
                    //     rhs: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                    //         term: GeneralTerm::IntegerTerm(induction_term.clone()),
                    //         guards: vec![
                    //             Guard {
                    //                 relation: Relation::GreaterEqual,
                    //                 term: least_term,
                    //             }
                    //         ],
                    //     })).into(),
                    // };
                    // let successor = GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                    //     op: BinaryOperator::Add,
                    //     lhs: induction_term.into(),
                    //     rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                    // });
                    // let inductive_step_consequent = rhs.substitute(induction_variable, successor);
                    // let inductive_step = Formula::QuantifiedFormula {
                    //     quantification: Quantification {
                    //         quantifier: Quantifier::Forall,
                    //         variables: vec![induction_variable],
                    //     },
                    //     formula: Formula::BinaryFormula {
                    //         connective: BinaryConnective::Implication,
                    //         lhs: inductive_step_antecedent.into(),
                    //         rhs: inductive_step_consequent.into(),
                    //     }.into(),
                    // };

                    // let annotated_base_case = AnnotatedFormula {
                    //     role: Role::Lemma,
                    //     direction: direction.clone(),
                    //     formula: base_case,
                    //     name: FormulaName(Some("base_case".to_string())),    // TODO - using variant of original lemmas name
                    // };

                    // let annotated_inductive_step = AnnotatedFormula {
                    //     role: Role::Lemma,
                    //     direction: direction.clone(),
                    //     formula: inductive_step,
                    //     name: FormulaName(Some("inductive_step".to_string())),    // TODO - using variant of original lemmas name
                    // };

                    // (annotated_base_case, annotated_inductive_step)
                }
                _ => todo!("inductive lemmas need a special form"),
            }
        }
        _ => todo!("error"),
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
                    let thing: fol::AnnotatedFormula =
                        "definition[comp_1]: forall X (composite(X) <-> q(X))."
                            .parse()
                            .unwrap();
                    println!("{:?}", thing);
                    print!("{theory}")
                }
            }

            Ok(())
        }
    }
}
