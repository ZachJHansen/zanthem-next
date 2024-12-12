use {
    crate::{
        convenience::unbox::{fol::UnboxedFormula, Unbox as _},
        syntax_tree::fol::{
            Atom, AtomicFormula, BinaryConnective, Formula, Predicate, Quantification, Quantifier,
            Theory, UnaryConnective,
        },
    },
    itertools::{max, Itertools},
    petgraph::graph::DiGraph,
    std::collections::{HashMap, HashSet},
};

// pub enum Occurrence {
//     Positive,
//     StrictlyPositive,
//     NonPositive,
// }

#[derive(Eq, PartialEq, Clone, Hash, Debug)]
struct Occurrence {
    pub atom: Atom,
    pub id: usize,
}

#[derive(Eq, PartialEq, Copy, Clone, Hash, Debug)]
struct OccurrenceData {
    pub count: usize,
    pub negated: bool,
}

type OccurrenceCounter = HashMap<Occurrence, OccurrenceData>;

fn choose_unique_id(
    key: &Occurrence,
    lhs: &OccurrenceCounter,
    rhs: &OccurrenceCounter,
) -> Occurrence {
    let matching_lhs_ids = lhs
        .keys()
        .filter(|occurrence| occurrence.atom == key.atom)
        .map(|occurrence| occurrence.id);

    let matching_rhs_ids = rhs
        .keys()
        .filter(|occurrence| occurrence.atom == key.atom)
        .map(|occurrence| occurrence.id);

    let lhs_max = match max(matching_lhs_ids) {
        Some(i) => i,
        None => 0,
    };

    let rhs_max = match max(matching_rhs_ids) {
        Some(i) => i,
        None => 0,
    };

    let id;
    if lhs_max >= rhs_max {
        id = lhs_max + 1;
    } else {
        id = rhs_max + 1;
    }

    Occurrence {
        id,
        atom: key.atom.clone(),
    }
}

trait Join {
    fn join(self, other: OccurrenceCounter) -> Self;
}

impl Join for OccurrenceCounter {
    fn join(self, other: OccurrenceCounter) -> Self {
        let mut new_counter = self.clone();

        for occurrence in other.keys() {
            if self.keys().contains(occurrence) {
                let new_key = choose_unique_id(occurrence, &self, &other);
                new_counter.insert(new_key, other[occurrence]);
            } else {
                new_counter.insert(occurrence.clone(), other[occurrence]);
            }
        }

        new_counter
    }
}

impl Formula {
    // Counts the number of implications in which this occurrence
    // occurs in the antecedent of the implication
    fn atom_occurrences(&self, occurrences: OccurrenceCounter) -> OccurrenceCounter {
        match &self {
            Formula::AtomicFormula(atomic_formula) => match atomic_formula {
                AtomicFormula::Truth | AtomicFormula::Falsity | AtomicFormula::Comparison(_) => {
                    occurrences
                }
                AtomicFormula::Atom(atom) => {
                    let mut right = OccurrenceCounter::new();
                    right.insert(
                        Occurrence {
                            atom: atom.clone(),
                            id: 0,
                        },
                        OccurrenceData {
                            count: 0,
                            negated: false,
                        },
                    );
                    occurrences.join(right)
                }
            },
            Formula::UnaryFormula {
                connective,
                formula,
            } => match connective {
                UnaryConnective::Negation => {
                    let mut counter = formula.atom_occurrences(occurrences);
                    for key in counter.clone().keys() {
                        if let Some(val) = counter.get_mut(key) {
                            *val = OccurrenceData {
                                count: (*val).count + 1,
                                negated: true,
                            };
                        }
                    }
                    counter
                }
            },
            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => match connective {
                BinaryConnective::Implication => {
                    let mut lhs_counter = lhs.atom_occurrences(occurrences.clone());
                    for key in lhs_counter.clone().keys() {
                        if let Some(val) = lhs_counter.get_mut(key) {
                            match rhs.clone().unbox() {
                                UnboxedFormula::AtomicFormula(AtomicFormula::Falsity) => {
                                    *val = OccurrenceData {
                                        count: (*val).count + 1,
                                        negated: true,
                                    };
                                }

                                _ => {
                                    *val = OccurrenceData {
                                        count: (*val).count + 1,
                                        negated: (*val).negated,
                                    };
                                }
                            }
                        }
                    }
                    let rhs_counter = rhs.atom_occurrences(occurrences);
                    lhs_counter.join(rhs_counter)
                }
                _ => {
                    let lhs_counter = lhs.atom_occurrences(occurrences.clone());
                    let rhs_counter = rhs.atom_occurrences(occurrences);
                    lhs_counter.join(rhs_counter)
                }
            },
            Formula::QuantifiedFormula { formula, .. } => formula.atom_occurrences(occurrences),
        }
    }
}

impl Theory {
    // Return the vertex and edge sets corresponding to the PDG of SM & Circ Sec 6.2
    pub fn cnf_pdg(&self, intensional: HashSet<Predicate>) -> DiGraph<(), ()> {
        let mut dependency_graph = DiGraph::<(), ()>::new();
        let mut mapping = HashMap::new();

        for predicate in intensional {
            let node = dependency_graph.add_node(());
            mapping.insert(predicate, node);
        }

        for rule in self.formulas.clone() {
            // TODO: check cnf

            let (antecedent, consequent) = match rule.unbox() {
                UnboxedFormula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs,
                    rhs,
                } => (lhs, rhs),
                UnboxedFormula::QuantifiedFormula {
                    quantification:
                        Quantification {
                            quantifier: Quantifier::Forall,
                            ..
                        },
                    formula:
                        Formula::BinaryFormula {
                            connective: BinaryConnective::Implication,
                            lhs,
                            rhs,
                        },
                } => (*lhs, *rhs),
                _ => unreachable!(), //(x.rebox().clone(), x.rebox()), //unreachable!("Formula {rule} is not in Clark Normal Form"),
            };

            //let counter = OccurrenceCounter::new();
            //let _occurrences = antecedent.atom_occurrences(counter);

            let _temp = Theory {
                formulas: vec![antecedent, consequent],
            };
        }

        let formula: Formula = "(((p(a) -> p(b)) and p(b)) -> q(b)) or (p(a) -> q(b)) and p(a)"
            .parse()
            .unwrap();
        let occurrences = formula.atom_occurrences(OccurrenceCounter::new());

        for (occ, data) in occurrences {
            println!(
                "({}, {}): {} / {}",
                occ.atom, occ.id, data.count, data.negated
            );
        }

        dependency_graph
    }
}

// impl Formula {
//     // Subformula self is negated in formula
//     fn negated(&self, formula: Formula) -> bool {
//         todo!()
//     }

//     // Subformula self occurs positively, strictly positively, or non-positively in formula
//     fn occurs(&self, formula: Formula) -> Occurrence {
//         todo!()
//     }
// }

// //But we need occurrences of a predicate, not the predicate itself...

// impl Predicate {
//     // Predicate self is negated in formula
//     fn negated(&self, formula: Formula) -> bool {
//         todo!()
//     }

//     // Predicate self occurs positively, strictly positively, or non-positively in formula
//     fn occurs(&self, formula: Formula) -> Occurrence {
//         todo!()
//     }
// }

#[cfg(test)]
mod tests {
    use super::{choose_unique_id, Occurrence, OccurrenceCounter, OccurrenceData};
    use crate::syntax_tree::fol::Atom;

    #[test]
    fn test_choose_unique_id() {
        let pa: Atom = "p(a)".parse().unwrap();
        let qb: Atom = "q(b)".parse().unwrap();

        let key = Occurrence {
            atom: pa.clone(),
            id: 3,
        };

        let mut left = OccurrenceCounter::new();
        left.insert(
            key.clone(),
            OccurrenceData {
                count: 1,
                negated: false,
            },
        );
        left.insert(
            Occurrence { atom: qb, id: 0 },
            OccurrenceData {
                count: 2,
                negated: false,
            },
        );

        let mut right = OccurrenceCounter::new();
        right.insert(
            Occurrence {
                atom: pa.clone(),
                id: 1,
            },
            OccurrenceData {
                count: 0,
                negated: false,
            },
        );

        let new_key = choose_unique_id(&key, &left, &right);

        assert_eq!(new_key, Occurrence { atom: pa, id: 4 })
    }

    // #[test]
    // fn test_count_occurrences() {
    //     let formula: Formula = "(p(a) and p(b)) or (p(a) -> q(b)) and p(a)".parse().unwrap();
    //     let occurrences = formula.atom_occurrences(OccurrenceCounter::new());

    //     let mut target = OccurrenceCounter::new();
    //     target.insert()
    //     for (occ, count) in occurrences {
    //         println!("({}, {}): {}", occ.atom, occ.id, count);
    //     }
    // }
}
