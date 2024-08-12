use {
    super::task::{external_equivalence::ReplacePlaceholders, GeneralLemma},
    crate::syntax_tree::fol::{self, Formula, FunctionConstant, Predicate, Sort, Theory},
    anyhow::{Context as _, Result},
    indexmap::{IndexMap, IndexSet},
    itertools::Itertools,
    std::{fmt, fs::File, io::Write as _, iter::repeat, path::Path},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Interpretation {
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
        let name;
        if self.name.starts_with("_") {
            name = format!("f{}", &self.name);
        } else {
            name = self.name.clone();
        }
        let role = &self.role;
        let formula = crate::formatting::fol::tptp::Format(&self.formula);
        writeln!(f, "tff({name}, {role}, {formula}).")
    }
}

impl From<(fol::AnnotatedFormula, Role)> for AnnotatedFormula {
    fn from(pair: (fol::AnnotatedFormula, Role)) -> Self {
        let name = match pair.0.role {
            fol::Role::Spec => "spec".to_string(),
            fol::Role::Assumption => "assumption".to_string(),
            fol::Role::Lemma => "lemma".to_string(),
            _ => "unknown_role".to_string(),
        };
        if pair.0.name == String::default() {
            AnnotatedFormula {
                name,
                role: pair.1,
                formula: pair.0.formula,
            }
        } else {
            AnnotatedFormula {
                name: pair.0.name.clone(),
                role: pair.1,
                formula: pair.0.formula,
            }
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Problem {
    pub name: String,
    pub interpretation: Interpretation,
    pub formulas: Vec<AnnotatedFormula>,
}

impl Problem {
    pub fn with_name<S: Into<String>>(name: S) -> Problem {
        Problem {
            name: name.into(),
            interpretation: Interpretation::Standard,
            formulas: vec![],
        }
    }

    pub fn add_theory<F>(mut self, theory: Theory, mut annotate: F) -> Self
    where
        F: FnMut(usize, Formula) -> AnnotatedFormula,
    {
        for (i, formula) in theory.formulas.into_iter().enumerate() {
            self.formulas.push(annotate(i, formula))
        }
        self
    }

    pub fn summarize(&self) {
        println!("\n------------ Problem: {} ------------", self.name);
        println!("\n#### Premises ####");
        for f in self.axioms() {
            println!("\t{}", f.formula);
        }
        println!("\n#### Conclusions ####");
        for f in self.conjectures() {
            println!("\t{}", f.formula);
        }
    }

    pub fn from_derivation_components(
        name: String,
        assumptions: Vec<AnnotatedFormula>,
        lemmas: Vec<GeneralLemma>,
    ) -> Vec<Self> {
        let mut initial_problem = Problem::with_name(name);
        initial_problem.formulas.extend(assumptions);

        let mut problem_sequence: Vec<Problem> = vec![];
        for general_lemma in lemmas {
            let mut lemma_sequence: Vec<Problem> = vec![];
            for conjecture in general_lemma.conjectures {
                let mut extended_problem = initial_problem.clone();
                extended_problem.formulas.push(conjecture);
                lemma_sequence.push(extended_problem);
            }
            initial_problem
                .formulas
                .extend(general_lemma.consequences.clone());
            problem_sequence.extend(lemma_sequence);
        }

        problem_sequence
    }

    pub fn from_components(
        name: String,
        stable: Vec<AnnotatedFormula>,
        premises: Vec<AnnotatedFormula>,
        conclusions: Vec<AnnotatedFormula>,
        lemmas: Vec<GeneralLemma>,
        definitions: Vec<fol::AnnotatedFormula>,
        placeholder: IndexMap<String, FunctionConstant>,
    ) -> Vec<Self> {
        let mut initial_problem = Problem::with_name(name);

        // Add axioms
        initial_problem.formulas.extend(stable);
        initial_problem.formulas.extend(premises);
        for definition in definitions {
            initial_problem.formulas.push(AnnotatedFormula::from((
                definition.replace_placeholders(&placeholder),
                Role::Axiom,
            )));
        }

        let mut final_problem = initial_problem.clone();
        initial_problem.name = format!("{}_outline", initial_problem.name).to_string();

        // Create a problem sequence from the proof outline
        let mut i = 0;
        let mut problem_sequence: Vec<Problem> = vec![];
        for general_lemma in lemmas {
            let general_lemma = general_lemma.replace_placeholders(&placeholder);
            let mut lemma_sequence: Vec<Problem> = vec![];
            for conjecture in general_lemma.conjectures {
                let mut extended_problem = initial_problem.clone();
                extended_problem.name = format!("{}_{}", extended_problem.name, i);
                extended_problem.formulas.push(conjecture);
                lemma_sequence.push(extended_problem);
                i = i + 1;
            }
            initial_problem
                .formulas
                .extend(general_lemma.consequences.clone());
            lemma_sequence.push(initial_problem.clone()); // TODO - WHY DO WE NEED THIS LINE
            problem_sequence.extend(lemma_sequence);

            final_problem.formulas.extend(general_lemma.consequences);
        }

        // Add conclusions as conjectures of final_problem
        final_problem.formulas.extend(conclusions);
        if !final_problem.conjectures().is_empty() {
            problem_sequence.push(final_problem);
        }
        problem_sequence
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
            .enumerate()
            .map(|(i, c)| {
                let mut formulas = axioms.clone();
                formulas.push(c);
                Problem {
                    name: format!("{}_{i}", self.name),
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
            .enumerate()
            .map(|(i, c)| {
                if let Some(last) = formulas.last_mut() {
                    last.role = Role::Axiom;
                }

                formulas.push(c);

                Problem {
                    name: format!("{}_{i}", self.name),
                    interpretation: self.interpretation.clone(),
                    formulas: formulas.clone(),
                }
            })
            .collect_vec()
    }

    pub fn to_file<P: AsRef<Path>>(&self, path: P) -> Result<()> {
        let path = path.as_ref();
        let mut file = File::create(path)
            .with_context(|| format!("could not create file `{}`", path.display()))?;
        write!(file, "{self}").with_context(|| format!("could not write file `{}`", path.display()))
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
            if predicate.arity > 0 {
                writeln!(f, "tff(predicate_{i}, type, {symbol}: ({input}) > $o).")?
            } else {
                writeln!(f, "tff(predicate_{i}, type, {symbol}: $o).")?
            }
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
            name: "problem".into(),
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
                    name: "problem_0".into(),
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
                    name: "problem_1".into(),
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
                    name: "problem_0".into(),
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
                    name: "problem_1".into(),
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
