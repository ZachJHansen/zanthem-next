use {
    crate::{
        convenience::unbox::{fol::UnboxedFormula, Unbox as _},
        syntax_tree::fol::{
            Atom, AtomicFormula, BinaryConnective, Formula, Predicate, Quantification, Quantifier,
            Theory, UnaryConnective,
        },
    },
    itertools::{max, Itertools},
    petgraph::graph::{DiGraph, NodeIndex},
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

    let lhs_max = max(matching_lhs_ids).unwrap_or(0);

    let rhs_max = max(matching_rhs_ids).unwrap_or(0);

    let id = if lhs_max >= rhs_max {
        lhs_max + 1
    } else {
        rhs_max + 1
    };

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
                                count: val.count + 1,
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
                                        count: val.count + 1,
                                        negated: true,
                                    };
                                }

                                _ => {
                                    *val = OccurrenceData {
                                        count: val.count + 1,
                                        negated: val.negated,
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

    pub fn cnf_pdg(&self, intensional: HashSet<Predicate>) -> DiGraph<(), ()> {
        Theory {
            formulas: vec![self.clone()],
        }
        .cnf_pdg(intensional)
        .0
    }
}

impl Theory {
    // Return the predicate dependency graph (SM & Circ Sec. 6.2)
    // and the node mapping
    pub fn cnf_pdg(
        &self,
        intensional: HashSet<Predicate>,
    ) -> (DiGraph<(), ()>, HashMap<Predicate, NodeIndex>) {
        let mut dependency_graph = DiGraph::<(), ()>::new();
        let mut mapping = HashMap::new();

        for predicate in intensional.iter() {
            let node = dependency_graph.add_node(());
            mapping.insert(predicate.clone(), node);
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

            if let Formula::AtomicFormula(AtomicFormula::Atom(atom)) = consequent {
                let head_predicate = atom.predicate();
                if intensional.contains(&head_predicate) {
                    let occurrences = antecedent.atom_occurrences(OccurrenceCounter::new());
                    for (occ, data) in occurrences {
                        if !data.negated && (data.count % 2 == 0) {
                            let body_predicate = occ.atom.predicate();
                            if intensional.contains(&body_predicate) {
                                dependency_graph.update_edge(
                                    mapping[&head_predicate],
                                    mapping[&body_predicate],
                                    (),
                                );
                            }
                        }
                    }
                }
            }
        }

        (dependency_graph, mapping)
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{choose_unique_id, Occurrence, OccurrenceCounter, OccurrenceData},
        crate::syntax_tree::fol::{Atom, Predicate, Theory},
        std::collections::HashSet,
    };

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

    #[test]
    fn test_cnf_dpg() {
        let mut intensional = HashSet::new();

        let p0 = Predicate {
            symbol: "p".into(),
            arity: 0,
        };
        intensional.insert(p0.clone());

        let q0 = Predicate {
            symbol: "q".into(),
            arity: 0,
        };
        intensional.insert(q0.clone());

        let p1 = Predicate {
            symbol: "p".into(),
            arity: 1,
        };
        intensional.insert(p1.clone());

        let q1 = Predicate {
            symbol: "q".into(),
            arity: 1,
        };
        intensional.insert(q1.clone());

        // F1 contributes edge (p/0, q/0)
        // F2 contributes edge (p/1, q/0)
        // F3 contributes edge (q/1, p/0)
        let theory: Theory = "q -> p. forall X ((q(X) -> q) -> p(X)). forall Y ( (forall X ((q(X) -> p(X)) -> p) ) -> q(Y) ).".parse().unwrap();

        let (graph, map) = theory.cnf_pdg(intensional.clone());

        assert!(graph.contains_edge(map[&p0], map[&q0]));
        assert!(graph.contains_edge(map[&p1], map[&q0]));
        assert!(graph.contains_edge(map[&q1], map[&p0]));
        assert!(graph.contains_edge(map[&q1], map[&q1]));

        assert_eq!(graph.node_count(), 4);
        assert_eq!(graph.edge_count(), 4);

        let r2 = Predicate {
            symbol: "r".into(),
            arity: 2,
        };
        intensional.insert(r2.clone());

        let t2 = Predicate {
            symbol: "t".into(),
            arity: 2,
        };
        intensional.insert(t2.clone());

        // F1 contributes no edges
        // F2 contributes edge (p/0, p/0)
        // F3 contributes no edges
        // F4 contributes edge (r/2, t/2)
        let theory: Theory = "forall X Y (r(X,Y) -> #false). (not q) and p -> p. (p -> #false) -> p. forall X Z (t(Z,X) and not t(X,Z) -> r(X,Z)).".parse().unwrap();

        let (graph, map) = theory.cnf_pdg(intensional);

        assert!(graph.contains_edge(map[&p0], map[&p0]));
        assert!(graph.contains_edge(map[&r2], map[&t2]));

        assert_eq!(graph.node_count(), 6);
        assert_eq!(graph.edge_count(), 2);
    }
}
