use {
    crate::syntax_tree::fol,
    crate::syntax_tree::fol::{Formula, FunctionConstant, Predicate, Sort, Theory},
    indexmap::IndexSet,
    itertools::Itertools,
    std::{fmt, iter::repeat},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash, Default)]
pub enum Interpretation {
    #[default]
    Standard,
}

impl fmt::Display for Interpretation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, include_str!("standard_interpretation.p"))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Role {
    Axiom,
    Conjecture,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Role::Axiom => write!(f, "axiom"),
            Role::Conjecture => write!(f, "conjecture"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedFormula {
    pub name: String,
    pub role: Role,
    pub formula: Formula,
}

impl From<(fol::AnnotatedFormula, Role)> for AnnotatedFormula {
    fn from(pair: (fol::AnnotatedFormula, Role)) -> Self {
        let name = match pair.0.role {
            fol::Role::Spec => "spec".to_string(),
            fol::Role::Assumption => "assumption".to_string(),
            fol::Role::Definition => "definition".to_string(),
            fol::Role::Lemma => "lemma".to_string(),
        };
        if pair.0.name == String::default() {
            return AnnotatedFormula {
                name,
                role: pair.1,
                formula: pair.0.formula,
            };
        } else {
            return AnnotatedFormula {
                name: pair.0.name.clone(),
                role: pair.1,
                formula: pair.0.formula,
            };
        }
    }
}

impl AnnotatedFormula {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        self.formula.predicates()
    }

    pub fn symbols(&self) -> IndexSet<String> {
        self.formula.symbols()
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        self.formula.function_constants()
    }
}

impl fmt::Display for AnnotatedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = &self.name;
        let role = &self.role;
        let formula = crate::formatting::fol::tptp::Format(&self.formula);
        writeln!(f, "tff({name}, {role}, {formula}).")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Default)]
pub struct Problem {
    pub interpretation: Interpretation,
    pub formulas: Vec<AnnotatedFormula>,
}

impl Problem {
    pub fn summarize(&self) {
        println!("\n#### Premises ####");
        for f in self.axioms() {
            println!("\t{}", f.formula);
        }
        println!("\n#### Conclusions ####");
        for f in self.conjectures() {
            println!("\t{}", f.formula);
        }
    }

    pub fn from_components(
        stable: Vec<AnnotatedFormula>,
        premises: Vec<AnnotatedFormula>,
        conclusions: Vec<AnnotatedFormula>,
        definitions: Vec<fol::AnnotatedFormula>,
        lemmas: Vec<fol::AnnotatedFormula>,
    ) -> Vec<Self> {
        let mut initial_problem = Problem::default();

        for axiom in stable.iter() {
            initial_problem.formulas.push(axiom.clone());
        }
        for axiom in premises.iter() {
            initial_problem.formulas.push(axiom.clone());
        }
        for axiom in definitions.iter() {
            initial_problem
                .formulas
                .push(AnnotatedFormula::from((axiom.clone(), Role::Axiom)));
        }

        let mut final_problem = initial_problem.clone();

        for formula in lemmas.iter() {
            initial_problem
                .formulas
                .push(AnnotatedFormula::from((formula.clone(), Role::Conjecture)));
            final_problem
                .formulas
                .push(AnnotatedFormula::from((formula.clone(), Role::Axiom)));
        }
        for conjecture in conclusions.iter() {
            final_problem.formulas.push(conjecture.clone());
        }

        let mut problem_sequence = initial_problem.decompose_sequential();
        problem_sequence.push(final_problem);
        problem_sequence
    }

    pub fn add_theory<F>(mut self, theory: Theory, mut annotate: F) -> Self
    where
        F: FnMut(usize, Formula) -> AnnotatedFormula,
    {
        self.add_formulas(theory.formulas, annotate)
    }

    pub fn add_formulas<F>(
        mut self,
        formulas: impl IntoIterator<Item = Formula>,
        mut annotate: F,
    ) -> Self
    where
        F: FnMut(usize, Formula) -> AnnotatedFormula,
    {
        for (i, formula) in formulas.into_iter().enumerate() {
            self.formulas.push(annotate(i, formula))
        }
        self
    }

    pub fn axioms(&self) -> Vec<AnnotatedFormula> {
        self.formulas
            .iter()
            .filter(|f| f.role == Role::Axiom)
            .cloned()
            .collect_vec()
    }

    pub fn conjectures(&self) -> Vec<AnnotatedFormula> {
        self.formulas
            .iter()
            .filter(|f| f.role == Role::Conjecture)
            .cloned()
            .collect_vec()
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.predicates())
        }
        result
    }

    pub fn symbols(&self) -> IndexSet<String> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.symbols())
        }
        result
    }

    pub fn function_constants(&self) -> IndexSet<FunctionConstant> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.function_constants())
        }
        result
    }

    pub fn decompose_independent(&self) -> Vec<Self> {
        let axioms = self.axioms();
        self.conjectures()
            .into_iter()
            .map(|c| {
                let mut formulas = axioms.clone();
                formulas.push(c);
                Problem {
                    interpretation: self.interpretation.clone(),
                    formulas,
                }
            })
            .collect_vec()
    }

    pub fn decompose_sequential(&self) -> Vec<Self> {
        let mut formulas = self.axioms();
        self.conjectures()
            .into_iter()
            .map(|c| {
                if let Some(last) = formulas.last_mut() {
                    last.role = Role::Axiom;
                }

                formulas.push(c);

                Problem {
                    interpretation: self.interpretation.clone(),
                    formulas: formulas.clone(),
                }
            })
            .collect_vec()
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.interpretation)?;

        for (i, predicate) in self.predicates().into_iter().enumerate() {
            let symbol = predicate.symbol;
            // let input: String = repeat("general")
            //     .take(predicate.arity)
            //     .intersperse(" * ")
            //     .collect();
            let input: String =
                Itertools::intersperse(repeat("general").take(predicate.arity), " * ").collect();
            writeln!(f, "tff(predicate_{i}, type, {symbol}: ({input}) > $o).")?
        }

        for (i, symbol) in self.symbols().into_iter().enumerate() {
            writeln!(f, "tff(type_symbol_{i}, type, {symbol}: symbol).")?
        }

        for (i, constant) in self.function_constants().into_iter().enumerate() {
            let name = crate::formatting::fol::tptp::Format(&constant);
            let sort = match constant.sort {
                Sort::General => "general",
                Sort::Integer => "$int",
                Sort::Symbol => "symbol",
            };
            writeln!(f, "tff(type_function_constant_{i}, type, {name}: {sort}).")?
        }

        let mut symbols = Vec::from_iter(self.symbols());
        symbols.sort_unstable();
        for (i, s) in symbols.windows(2).enumerate() {
            writeln!(
                f,
                "tff(symbol_order_{i}, axiom, p__less__(f__symbolic__({}), f__symbolic__({}))).",
                s[0], s[1]
            )?
        }

        for formula in &self.formulas {
            formula.fmt(f)?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{AnnotatedFormula, Interpretation, Problem, Role},
        std::vec,
    };

    #[test]
    fn test_decomposition() {
        let problem = Problem {
            interpretation: Interpretation::Standard,
            formulas: vec![
                AnnotatedFormula {
                    name: "axiom_0".into(),
                    role: Role::Axiom,
                    formula: "p(a)".parse().unwrap(),
                },
                AnnotatedFormula {
                    name: "axiom_1".into(),
                    role: Role::Axiom,
                    formula: "forall X p(X) -> q(X)".parse().unwrap(),
                },
                AnnotatedFormula {
                    name: "conjecture_0".into(),
                    role: Role::Conjecture,
                    formula: "p(a)".parse().unwrap(),
                },
                AnnotatedFormula {
                    name: "conjecture_1".into(),
                    role: Role::Conjecture,
                    formula: "q(a)".parse().unwrap(),
                },
            ],
        };

        assert_eq!(
            problem.decompose_independent(),
            vec![
                Problem {
                    interpretation: Interpretation::Standard,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_0".into(),
                            role: Role::Conjecture,
                            formula: "p(a)".parse().unwrap(),
                        },
                    ],
                },
                Problem {
                    interpretation: Interpretation::Standard,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_1".into(),
                            role: Role::Conjecture,
                            formula: "q(a)".parse().unwrap(),
                        },
                    ],
                }
            ]
        );

        assert_eq!(
            problem.decompose_sequential(),
            vec![
                Problem {
                    interpretation: Interpretation::Standard,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_0".into(),
                            role: Role::Conjecture,
                            formula: "p(a)".parse().unwrap(),
                        },
                    ],
                },
                Problem {
                    interpretation: Interpretation::Standard,
                    formulas: vec![
                        AnnotatedFormula {
                            name: "axiom_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "axiom_1".into(),
                            role: Role::Axiom,
                            formula: "forall X p(X) -> q(X)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_0".into(),
                            role: Role::Axiom,
                            formula: "p(a)".parse().unwrap(),
                        },
                        AnnotatedFormula {
                            name: "conjecture_1".into(),
                            role: Role::Conjecture,
                            formula: "q(a)".parse().unwrap(),
                        },
                    ],
                }
            ]
        );
    }
}
