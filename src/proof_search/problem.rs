use {
    crate::{
        convenience::{apply::Apply as _, unbox::fol::UnboxedFormula, unbox::Unbox},
        formatting::fol::tptp::Format,
        syntax_tree::{asp, fol},
        translating::{completion::completion, tau_star::tau_star},
    },
    regex::Regex,
    std::collections::{HashMap, HashSet},
    std::fs,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FileType {
    MiniGringoProgram { program: asp::Program },
    FirstOrderSpecification { specification: fol::Specification },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Role {
    Axiom,
    Conjecture,
}

impl Role {
    pub fn display(&self) -> &str {
        match &self {
            Role::Axiom => "axiom",
            Role::Conjecture => "conjecture",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VampireTypes {
    Ttype,
    Object,
    Int,
    I,
    O,
}

impl VampireTypes {
    pub fn display(&self) -> &str {
        match &self {
            VampireTypes::Ttype => "$tType",
            VampireTypes::Object => "object",
            VampireTypes::Int => "$int",
            VampireTypes::I => "$i",
            VampireTypes::O => "$o",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeSpec {
    return_type: VampireTypes,
    args: Vec<VampireTypes>,
}

impl TypeSpec {
    pub fn display(&self) -> String {
        let mut spec = "".to_owned();
        if self.args.len() > 0 {
            spec.push_str("(");
            spec.push_str(self.args[0].display());
            for i in 1..self.args.len() {
                spec.push_str(" * ");
                spec.push_str(self.args[i].display());
            }
            spec.push_str(") > ");
        }
        spec.push_str(self.return_type.display());
        spec
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Statement {
    AnnotatedFormula {
        name: String,
        role: Role,
        formula: fol::Formula,
    },
    TypedAtom {
        name: String,
        atom: String,
        spec: TypeSpec,
    },
}

impl Statement {
    pub fn display(&self) -> String {
        match &self {
            Statement::AnnotatedFormula {
                name,
                role,
                formula,
            } => {
                let intermediate =
                    format!("\ntff({}, {}, {}).", name, role.display(), Format(formula)); // Placeholders special chars need to be replaced with actual names
                let re = Regex::new(r"%-(?P<ph>[[:alpha:]]+)-%").unwrap();
                let mut modified = intermediate.clone();
                for caps in re.captures_iter(&intermediate) {
                    let ph_specific_re =
                        Regex::new(format!(r"%-{}-%i", &caps["ph"]).as_str()).unwrap();
                    modified = ph_specific_re
                        .replace_all(&modified, &caps["ph"].to_lowercase())
                        .to_string();
                }
                modified
            }
            Statement::TypedAtom { atom, name, spec } => {
                format!("\ntff({}, type, {}: {}).", name, atom, spec.display())
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Interpretation {
    Standard,
}

// Reflects the SZS ontology
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ProblemStatus {
    Theorem,
    ContradictoryAxioms,
    CounterSatisfiable,
    Timeout,
    GaveUp,
    Error,
    Unknown,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Problem {
    pub status: ProblemStatus,
    pub interpretation: Interpretation,
    pub predicates: Vec<Statement>,
    pub functions: Vec<Statement>,
    pub axioms: Vec<fol::Formula>,
    pub conjecture: fol::Formula,
}

impl Problem {
    pub fn display(&self, verbose: bool) -> String {
        let mut problem = "".to_owned();
        if verbose {
            problem.push_str("\n%%%%%%%\n");
            let tptp_preamble_anthem_types =
                include_str!("standard_preamble_types.tptp").trim_end();
            problem.push_str(tptp_preamble_anthem_types);
            problem.push_str("\n%%%%%%%\n");
            let tptp_preamble_anthem_axioms =
                include_str!("standard_preamble_axioms.tptp").trim_end();
            problem.push_str(tptp_preamble_anthem_axioms);
            problem.push_str("\n%%%%%%%\n");

            problem.push_str("\n%%%% Predicates %%%%\n");
            for p in self.predicates.iter() {
                problem.push_str(&p.display());
            }
            problem.push_str("\n%%%% Functions %%%%\n");
            for f in self.functions.iter() {
                problem.push_str(&f.display());
            }
        }

        problem.push_str("\n%%%% Axioms %%%%");
        for a in self.axioms.iter() {
            let s = Statement::AnnotatedFormula {
                name: "statement".to_string(),
                role: Role::Axiom,
                formula: a.clone(),
            };
            problem.push_str(&s.display());
            problem.push_str("\n");
        }

        problem.push_str("\n%%%% Conjecture %%%%");
        let s = Statement::AnnotatedFormula {
            name: "statement".to_string(),
            role: Role::Conjecture,
            formula: self.conjecture.clone(),
        };
        problem.push_str(&s.display());
        problem.push_str("\n");

        problem
    }

    pub fn print_to_file(&self, fname: String) {
        //     let write_title = |formatter: &mut dyn std::fmt::Write, title, section_separator|
        //     -> std::fmt::Result
        // {
        //     write!(formatter, "{}{}", section_separator, "%".repeat(72))?;
        //     write!(formatter, "\n% {}", title)?;
        //     writeln!(formatter, "\n{}", "%".repeat(72))
        // };

        // let mut section_separator = "";

        // write_title(formatter, "anthem types", section_separator)?;
        // section_separator = "\n";

        let file_contents = self.display(true);
        let success = fs::write(fname, file_contents.as_str());
        match success {
            Ok(_) => (),
            Err(e) => {
                println!("Error: {}", e);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Claim {
    pub name: String,
    pub premises: Vec<fol::Formula>,
    pub conclusions: Vec<fol::Formula>,
    pub status: ProblemStatus,
}

// Qx (Head <=> Body)   becomes     [Qx (Head => Body), Qx (Head <= Body)]
// Head <=> Body        becomes     [Head => Body, Head <= Body]
pub fn equivalence_breaker(formula: fol::Formula) -> Option<Vec<fol::Formula>> {
    match formula {
        fol::Formula::QuantifiedFormula {
            quantification: q,
            formula: f,
        } => {
            match f.unbox() {
                UnboxedFormula::BinaryFormula {
                    connective: c,
                    lhs: f1,
                    rhs: f2,
                } => match c {
                    fol::BinaryConnective::Equivalence => {
                        let imp1 = fol::Formula::QuantifiedFormula {
                            quantification: q.clone(),
                            formula: fol::Formula::BinaryFormula {
                                connective: fol::BinaryConnective::Implication,
                                lhs: f1.clone().into(),
                                rhs: f2.clone().into(),
                            }.into(),
                        };
                        let imp2 = fol::Formula::QuantifiedFormula {
                            quantification: q.clone(),
                            formula: fol::Formula::BinaryFormula {
                                connective: fol::BinaryConnective::ReverseImplication,
                                lhs: f1.into(),
                                rhs: f2.into(),
                            }.into(),
                        };
                        return Some(vec![imp1, imp2]);
                    },
                    _ => {
                        return None;
                    },
                },
                _ => {
                    return None;
                },
            }
        },

        fol::Formula::BinaryFormula {
            connective: c,
            lhs: f1,
            rhs: f2,
        } => match c {
            fol::BinaryConnective::Equivalence => { 
                let imp1 = fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::Implication,
                    lhs: f1.clone(),
                    rhs: f2.clone(),
                };
                let imp2 = fol::Formula::BinaryFormula {
                    connective: fol::BinaryConnective::ReverseImplication,
                    lhs: f1.clone(),
                    rhs: f2.clone(),
                };
                return Some(vec![imp1, imp2]);
            },
            _ => {
                return None;
            },
        },

        _ => {
            return None;
        },
    }
}

impl Claim {
    pub fn decompose_claim_default(
        &self,
        problem_predicates: &Vec<Statement>,
        problem_functions: &Vec<Statement>,
        break_equivalences: bool,
    ) -> Vec<Problem> {
        let mut problems = Vec::<Problem>::new();
        for conclusion in self.conclusions.iter() {
            if break_equivalences {
                let implications = equivalence_breaker(conclusion.clone());
                match implications {
                    Some(mut formulas) => {
                        problems.push(Problem {
                            status: ProblemStatus::Unknown,
                            interpretation: Interpretation::Standard,
                            predicates: problem_predicates.clone(),
                            functions: problem_functions.clone(),
                            axioms: self.premises.clone(),
                            conjecture: formulas.pop().unwrap(),
                        });
                        problems.push(Problem {
                            status: ProblemStatus::Unknown,
                            interpretation: Interpretation::Standard,
                            predicates: problem_predicates.clone(),
                            functions: problem_functions.clone(),
                            axioms: self.premises.clone(),
                            conjecture: formulas.pop().unwrap(),
                        });        
                    },
                    None => {
                        problems.push(Problem {
                            status: ProblemStatus::Unknown,
                            interpretation: Interpretation::Standard,
                            predicates: problem_predicates.clone(),
                            functions: problem_functions.clone(),
                            axioms: self.premises.clone(),
                            conjecture: conclusion.clone(),
                        });
                    },
                }
            } else {
                problems.push(Problem {
                    status: ProblemStatus::Unknown,
                    interpretation: Interpretation::Standard,
                    predicates: problem_predicates.clone(),
                    functions: problem_functions.clone(),
                    axioms: self.premises.clone(),
                    conjecture: conclusion.clone(),
                });
            }
        }
        problems
    }

    pub fn decompose_claim_sequential(
        &self,
        problem_predicates: &Vec<Statement>,
        problem_functions: &Vec<Statement>,
        break_equivalences: bool,
    ) -> Vec<Problem> {
        let mut problems = Vec::<Problem>::new();
        let n = self.conclusions.len();
        assert!(n > 0);
        if n == 1 {
            if break_equivalences {
                let implications = equivalence_breaker(self.conclusions[0].clone());
                match implications {
                    Some(mut formulas) => {
                        problems.push(Problem {
                            status: ProblemStatus::Unknown,
                            interpretation: Interpretation::Standard,
                            predicates: problem_predicates.clone(),
                            functions: problem_functions.clone(),
                            axioms: self.premises.clone(),
                            conjecture: formulas.pop().unwrap(),
                        });
                        problems.push(Problem {
                            status: ProblemStatus::Unknown,
                            interpretation: Interpretation::Standard,
                            predicates: problem_predicates.clone(),
                            functions: problem_functions.clone(),
                            axioms: self.premises.clone(),
                            conjecture: formulas.pop().unwrap(),
                        });   
                    },
                    None => {
                        problems.push(Problem {
                            status: ProblemStatus::Unknown,
                            interpretation: Interpretation::Standard,
                            predicates: problem_predicates.clone(),
                            functions: problem_functions.clone(),
                            axioms: self.premises.clone(),
                            conjecture: self.conclusions[0].clone(),
                        });
                    },
                }
            } else {
                problems.push(Problem {
                    status: ProblemStatus::Unknown,
                    interpretation: Interpretation::Standard,
                    predicates: problem_predicates.clone(),
                    functions: problem_functions.clone(),
                    axioms: self.premises.clone(),
                    conjecture: self.conclusions[0].clone(),
                });
            }
        } else {
            let mut axioms = self.premises.clone();
            for i in 0..n {
                if break_equivalences {
                    let implications = equivalence_breaker(self.conclusions[i].clone());
                    match implications {
                        Some(mut formulas) => {
                            problems.push(Problem {
                                status: ProblemStatus::Unknown,
                                interpretation: Interpretation::Standard,
                                predicates: problem_predicates.clone(),
                                functions: problem_functions.clone(),
                                axioms: axioms.clone(),
                                conjecture: formulas.pop().unwrap(),
                            });
                            problems.push(Problem {
                                status: ProblemStatus::Unknown,
                                interpretation: Interpretation::Standard,
                                predicates: problem_predicates.clone(),
                                functions: problem_functions.clone(),
                                axioms: axioms.clone(),
                                conjecture: formulas.pop().unwrap(),
                            });
                        },
                        None => {
                            problems.push(Problem {
                                status: ProblemStatus::Unknown,
                                interpretation: Interpretation::Standard,
                                predicates: problem_predicates.clone(),
                                functions: problem_functions.clone(),
                                axioms: axioms.clone(),
                                conjecture: self.conclusions[i].clone(),
                            });
                        },
                    }
                } else {
                    problems.push(Problem {
                        status: ProblemStatus::Unknown,
                        interpretation: Interpretation::Standard,
                        predicates: problem_predicates.clone(),
                        functions: problem_functions.clone(),
                        axioms: axioms.clone(),
                        conjecture: self.conclusions[i].clone(),
                    });
                }
                axioms.push(self.conclusions[i].clone());
            }
        }
        problems
    }

    pub fn display(&self) -> String {
        let mut claim = "Claim: ".to_owned();
        claim.push_str(&self.name);
        claim.push_str("\nPremises:\n");
        for f in self.premises.iter() {
            claim.push_str(format!("{}\n", f).as_str());
        }
        claim.push_str("\nConclusions:\n");
        for c in self.conclusions.iter() {
            claim.push_str(format!("{}\n", c).as_str());
        }
        claim
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProblemHandler {
    placeholders: HashSet<fol::Placeholder>,
    predicates: Vec<Statement>,
    functions: Vec<Statement>,
    interpretation: Interpretation,
    memory: Vec<Claim>,
    pub goals: HashMap<Claim, Vec<Problem>>,
}

// Forward direction: assume program publics, prove spec publics
// Backward direction: assume spec publics, prove program publics
impl ProblemHandler {
    pub fn new(
        program: &asp::Program,
        specification: &FileType,
        user_guide: &fol::Specification,
    ) -> Self {
        let needs_renaming = match &specification {
            &FileType::MiniGringoProgram { .. } => true,
            &FileType::FirstOrderSpecification { .. } => false,
        };

        let public_predicates = public_predicates(specification, user_guide);

        let specification_private_predicates = match &specification {
            &FileType::MiniGringoProgram { program: p } => {
                prog_private_predicates(p, &public_predicates, needs_renaming, true)
            }
            &FileType::FirstOrderSpecification { specification: s } => {
                spec_private_predicates(s, &public_predicates, needs_renaming)
            }
        };
        
        println!("Spec private predicates: {:?}", specification_private_predicates); 

        let program_private_predicates =
            prog_private_predicates(program, &public_predicates, needs_renaming, false);

        println!("program private predicates: {:?}", program_private_predicates); 

        let mut private_predicates: HashSet<fol::Predicate> = HashSet::new();
        private_predicates.extend(specification_private_predicates);
        private_predicates.extend(program_private_predicates);

        let problem_predicates = public_predicates.union(&private_predicates);
        //  TODO - how to handle spec private predicates? are they part of the problem types? or only for one direction?

        let mut forward_premises = Vec::<fol::Formula>::new();
        let mut forward_conclusions = Vec::<fol::Formula>::new();

        let mut backward_premises = Vec::<fol::Formula>::new();
        let mut backward_conclusions = Vec::<fol::Formula>::new();

        let mut placeholders = HashSet::<fol::Placeholder>::new(); // Placeholders, disjoint from functions
        let mut functions = HashSet::<String>::new(); // Function constants occurring in the problem

        let mut predicates = Vec::<Statement>::new();
        for (i, p) in problem_predicates.enumerate() {
            predicates.push(Statement::TypedAtom {
                name: ["predicate", i.to_string().as_str()].join("_"),
                atom: p.symbol.clone(),
                spec: TypeSpec {
                    return_type: VampireTypes::O,
                    args: vec![VampireTypes::Object; p.arity],
                },
            });
        }

        parse_program(
            program,
            &mut forward_premises,
            &mut backward_premises,
            &mut backward_conclusions,
            &public_predicates,
            &mut functions,
            needs_renaming,
        );

        parse_user_guide(
            user_guide,
            &mut forward_premises,
            &mut backward_premises,
            &mut predicates,
            &mut placeholders,
        );

        parse_specification(
            specification,
            &mut forward_premises,
            &mut backward_premises,
            &mut forward_conclusions,
            &mut predicates,
            &mut functions,
            &public_predicates,
            needs_renaming,
        );

        placeholder_replacements(&mut forward_premises, &placeholders);
        placeholder_replacements(&mut forward_conclusions, &placeholders);
        placeholder_replacements(&mut backward_premises, &placeholders);
        placeholder_replacements(&mut backward_conclusions, &placeholders);

        let forward = Claim {
            name: "forward".to_string(),
            premises: forward_premises,
            conclusions: forward_conclusions,
            status: ProblemStatus::Unknown,
        };

        let backward = Claim {
            name: "backward".to_string(),
            premises: backward_premises,
            conclusions: backward_conclusions,
            status: ProblemStatus::Unknown,
        };

        let mut function_statements = Vec::<Statement>::new();
        for ph in placeholders.iter() {
            function_statements.push(Statement::TypedAtom {
                name: "placeholder".to_string(),
                atom: ph.to_string(),
                spec: TypeSpec {
                    return_type: VampireTypes::Int,
                    args: vec![],
                },
            });
        }

        let mut ground_function_constants = Vec::new();
        let placeholder_names: Vec<String> =
            placeholders.iter().map(|ph| ph.name.clone()).collect();
        for f in functions.iter() {
            if !placeholder_names.contains(f) {
                ground_function_constants.push(f);
            }
        }

        let uniqueness_axioms = axiomatize_partial_order(ground_function_constants.clone());

        for f in ground_function_constants.iter() {
            function_statements.push(Statement::TypedAtom {
                name: "ground_function_constant".to_string(),
                atom: f.to_string(),
                spec: TypeSpec {
                    return_type: VampireTypes::Object,
                    args: vec![],
                },
            });
        }

        for ax in uniqueness_axioms.iter() {
            function_statements.push(Statement::AnnotatedFormula {
                formula: ax.clone(),
                role: Role::Axiom,
                name: "uniqueness_axiom".into(),
            });
        }

        let mut goals: HashMap<Claim, Vec<Problem>> = HashMap::new();
        goals.insert(
            forward.clone(),
            //forward.decompose_claim(&predicates, &function_statements),
            Vec::new(),
        );
        goals.insert(
            backward.clone(),
            //backward.decompose_claim(&predicates, &function_statements),
            Vec::new(),
        );

        ProblemHandler {
            placeholders,
            predicates,
            functions: function_statements,
            interpretation: Interpretation::Standard,
            memory: vec![],
            goals,
        }
    }

    pub fn default_decomposition(&mut self, break_equivalences: bool) {
        let mut goals: HashMap<Claim, Vec<Problem>> = HashMap::new();
        for c in self.goals.keys() {
            let claim = c.clone();
            goals.insert(
                claim.clone(),
                claim.decompose_claim_default(&self.predicates, &self.functions, break_equivalences),
            );
        }
        self.goals = goals;
    }

    pub fn sequential_decomposition(&mut self, break_equivalences: bool) {
        let mut goals: HashMap<Claim, Vec<Problem>> = HashMap::new();
        for c in self.goals.keys() {
            let claim = c.clone();
            goals.insert(
                claim.clone(),
                claim.decompose_claim_sequential(&self.predicates, &self.functions, break_equivalences),
            );
        }
        self.goals = goals;
    }

    pub fn display(&self) {
        println!("Goals:\n");
        for (claim, problems) in self.goals.iter() {
            println!("{}", claim.display());
            println!("Claim Problems:");
            for p in problems.iter() {
                println!("{}", p.display(false));
            }
            println!("");
        }
    }

    pub fn generate_problem_files(&self) {
        for (claim, problems) in self.goals.iter() {
            for (i, p) in problems.iter().enumerate() {
                let pname = format!("{}_{}.p", claim.name, i + 1);
                p.print_to_file(pname);
            }
            println!("");
        }
    }

    pub fn add_lemmas(&mut self, lemmas: fol::Specification) {
        let mut problem_claims = Vec::new();
        for claim in self.goals.keys() {
            problem_claims.push(claim.clone());
        }
        problem_claims.sort_by_key(|c| c.name.clone());

        assert_eq!(problem_claims[0].name, "backward");
        assert_eq!(problem_claims[1].name, "forward");

        // Insert lemmas as the first claim conclusions to be proven
        let mut forward_lemmas = Vec::new();
        let mut backward_lemmas = Vec::new();

        for lemma in lemmas.specs.iter() {
            match lemma {
                fol::Spec::Lemma(fol::Lemma {
                    direction: fol::Direction::Forward,
                    formula,
                }) => {
                    forward_lemmas.push(formula.clone());
                }
                fol::Spec::Lemma(fol::Lemma {
                    direction: fol::Direction::Backward,
                    formula,
                }) => {
                    backward_lemmas.push(formula.clone());
                }
                fol::Spec::Lemma(fol::Lemma {
                    direction: fol::Direction::Universal,
                    formula,
                }) => {
                    forward_lemmas.push(formula.clone());
                    backward_lemmas.push(formula.clone());
                }
                _ => {
                    panic!("Only lemmas should occur in helper lemmas file");
                }
            }
        }

        placeholder_replacements(&mut forward_lemmas, &self.placeholders);
        placeholder_replacements(&mut backward_lemmas, &self.placeholders);

        forward_lemmas.extend(problem_claims[1].conclusions.clone());
        backward_lemmas.extend(problem_claims[0].conclusions.clone());

        let forward = Claim {
            name: "forward".to_string(),
            premises: problem_claims[1].premises.clone(),
            conclusions: forward_lemmas,
            status: ProblemStatus::Unknown,
        };

        let backward = Claim {
            name: "backward".to_string(),
            premises: problem_claims[0].premises.clone(),
            conclusions: backward_lemmas,
            status: ProblemStatus::Unknown,
        };

        let mut goals: HashMap<Claim, Vec<Problem>> = HashMap::new();
        goals.insert(forward.clone(), Vec::new());
        goals.insert(backward.clone(), Vec::new());

        self.goals = goals;
    }

    pub fn make_sequential(&mut self) {
        todo!();
    }
}

pub fn axiomatize_partial_order(function_constants: Vec<&String>) -> Vec<fol::Formula> {
    let mut sorted_fns = Vec::new();
    for f in function_constants.iter() {
        sorted_fns.push(f.to_string());
    }
    sorted_fns.sort();

    let n = sorted_fns.len();
    let mut axioms = Vec::new();
    if n > 1 {
        for i in 0..(n - 1) {
            for j in (i + 1)..n {
                let ax =
                    fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
                        term: fol::GeneralTerm::Symbol(sorted_fns[i].clone()),
                        guards: vec![fol::Guard {
                            relation: fol::Relation::Less,
                            term: fol::GeneralTerm::Symbol(sorted_fns[j].clone()),
                        }],
                    }));
                axioms.push(ax);
            }
        }
    }
    axioms
}

pub fn parse_specification(
    specification: &FileType,
    forward_premises: &mut Vec<fol::Formula>,
    backward_premises: &mut Vec<fol::Formula>,
    forward_conclusions: &mut Vec<fol::Formula>,
    predicates: &mut Vec<Statement>,
    functions: &mut HashSet<String>,
    public_predicates: &HashSet<fol::Predicate>,
    needs_renaming: bool,
) {
    match specification {
        FileType::MiniGringoProgram { program: m } => {
            let gamma = completion(&tau_star(m.clone()));
            match gamma {
                Some(completion) => {
                    for f in completion.formulas.iter() {
                        // Spec formulas
                        let formula = if needs_renaming {
                            rename_predicates(f.clone(), "_1", public_predicates)
                        } else {
                            f.clone()
                        };

                        for function in formula.function_constants() {
                            functions.insert(function);
                        }

                        let head_symbol = formula_head(&formula);
                        match head_symbol {
                            Some(s) => {
                                if public_predicates.contains(&s) {
                                    // Completed definition of public predicate
                                    forward_conclusions.push(formula.clone());
                                    backward_premises.push(formula.clone());
                                } else {
                                    // Completed definition of private predicate
                                    forward_premises.push(formula.clone());
                                    backward_premises.push(formula.clone());
                                }
                            }
                            None => {
                                // Formula representation of a constraint
                                forward_conclusions.push(formula.clone());
                                backward_premises.push(formula.clone());
                            }
                        }
                    }
                }
                None => todo!(),
            }
        }
        FileType::FirstOrderSpecification { specification: s } => {
            for (_i, spec) in s.specs.iter().enumerate() {
                match spec {
                    // fol::Spec::PlaceholderDeclaration { placeholders } => {
                    //     for ph in placeholders.iter() {
                    //         functions.push(Statement::TypedAtom {
                    //             name: ["statement", i.to_string().as_str()].join("_"),
                    //             atom: ph.name.clone(),
                    //             spec: TypeSpec {
                    //                 return_type: VampireTypes::Int,
                    //                 args: vec![],
                    //             },
                    //         });
                    //     }
                    // }
                    fol::Spec::Input { predicates: preds }
                    | fol::Spec::Output { predicates: preds } => {
                        for (i, p) in preds.iter().enumerate() {
                            predicates.push(Statement::TypedAtom {
                                name: ["predicate", i.to_string().as_str()].join("_"),
                                atom: p.symbol.clone(),
                                spec: TypeSpec {
                                    return_type: VampireTypes::O,
                                    args: vec![VampireTypes::Object; p.arity],
                                },
                            });
                        }
                    }
                    fol::Spec::Assumption { formula } => {
                        forward_premises.push(formula.clone());
                        backward_premises.push(formula.clone());

                        for function in formula.function_constants() {
                            functions.insert(function);
                        }
                    }
                    fol::Spec::Conjecture { formula } => {
                        forward_conclusions.push(formula.clone());
                        backward_premises.push(formula.clone());

                        for function in formula.function_constants() {
                            functions.insert(function);
                        }
                    }
                    _ => todo!(),
                }
            }
        }
    }
}

pub fn parse_program(
    program: &asp::Program,
    forward_premises: &mut Vec<fol::Formula>,
    backward_premises: &mut Vec<fol::Formula>,
    backward_conclusions: &mut Vec<fol::Formula>,
    public_predicates: &HashSet<fol::Predicate>,
    functions: &mut HashSet<String>,
    needs_renaming: bool,
) {
    let gamma = completion(&tau_star(program.clone()));
    match gamma {
        Some(completion) => {
            for f in completion.formulas.iter() {
                let formula = if needs_renaming {
                    rename_predicates(f.clone(), "_2", public_predicates)
                } else {
                    f.clone()
                };

                for function in formula.function_constants() {
                    functions.insert(function);
                }

                let head_symbol = formula_head(&formula);
                match head_symbol {
                    Some(s) => {
                        if public_predicates.contains(&s) {
                            // Completed definition of public predicate
                            forward_premises.push(formula.clone());
                            backward_conclusions.push(formula.clone());
                        } else {
                            // Completed definition of private predicate
                            forward_premises.push(formula.clone());
                            backward_premises.push(formula.clone());
                        }
                    }
                    None => {
                        // Formula representation of a constraint
                        forward_premises.push(formula.clone());
                        backward_conclusions.push(formula.clone());
                    }
                }
            }
        }
        None => todo!(),
    }
}

pub fn parse_user_guide(
    user_guide: &fol::Specification,
    forward_premises: &mut Vec<fol::Formula>,
    backward_premises: &mut Vec<fol::Formula>,
    predicates: &mut Vec<Statement>,
    placeholder_fns: &mut HashSet<fol::Placeholder>,
) {
    let mut preds = Vec::<Statement>::new();
    let mut axioms = Vec::<fol::Formula>::new();

    for (_i, spec) in user_guide.specs.iter().enumerate() {
        match spec {
            fol::Spec::PlaceholderDeclaration { placeholders } => {
                for ph in placeholders.iter() {
                    placeholder_fns.insert(ph.clone());
                }
            }
            fol::Spec::Input { predicates } | fol::Spec::Output { predicates } => {
                for p in predicates.iter() {
                    if !predicates.contains(&p) {
                        preds.push(Statement::TypedAtom {
                            name: "predicate".to_string(),
                            atom: p.symbol.clone(),
                            spec: TypeSpec {
                                return_type: VampireTypes::O,
                                args: vec![VampireTypes::Object; p.arity],
                            },
                        });
                    }
                }
            }
            fol::Spec::Assumption { formula } => {
                axioms.push(formula.clone());
            }
            fol::Spec::Conjecture { formula } => {
                println!("A user guide cannot contain formulas annotated as conjectures! Ignoring formula:\n\t{formula}");
            }
            fol::Spec::Lemma(_) => {
                println!("A user guide cannot contain lemmas!");
            }
        }
    }

    forward_premises.extend(axioms.clone());
    backward_premises.extend(axioms);
    predicates.extend(preds);
}

pub fn public_predicates(
    specification: &FileType,
    user_guide: &fol::Specification,
) -> HashSet<fol::Predicate> {
    match specification {
        FileType::MiniGringoProgram { program: m } => prog_public_predicates(&m, user_guide),
        FileType::FirstOrderSpecification { specification: s } => {
            spec_public_predicates(&s, user_guide)
        }
    }
}

pub fn spec_public_predicates(
    specification: &fol::Specification,
    user_guide: &fol::Specification,
) -> HashSet<fol::Predicate> {
    let mut public_predicates = HashSet::<fol::Predicate>::new();

    for spec in user_guide.specs.iter() {
        match spec {
            fol::Spec::Input { predicates } => {
                for pred in predicates.iter() {
                    public_predicates.insert(pred.clone());
                }
            }
            fol::Spec::Output { predicates } => {
                for pred in predicates.iter() {
                    public_predicates.insert(pred.clone());
                }
            }
            _ => (),
        }
    }

    for spec in specification.specs.iter() {
        match spec {
            fol::Spec::Input { predicates } => {
                for pred in predicates.iter() {
                    public_predicates.insert(pred.clone());
                }
            }
            fol::Spec::Output { predicates } => {
                for pred in predicates.iter() {
                    public_predicates.insert(pred.clone());
                }
            }
            _ => (),
        }
    }
    public_predicates
}

pub fn prog_public_predicates(
    _specification: &asp::Program,
    user_guide: &fol::Specification,
) -> HashSet<fol::Predicate> {
    let mut public_predicates = HashSet::<fol::Predicate>::new();

    for spec in user_guide.specs.iter() {
        match spec {
            fol::Spec::Input { predicates } => {
                for pred in predicates.iter() {
                    public_predicates.insert(pred.clone());
                }
            }
            fol::Spec::Output { predicates } => {
                for pred in predicates.iter() {
                    public_predicates.insert(pred.clone());
                }
            }
            _ => (),
        }
    }

    // TODO - allow parsing #show statements in ASP programs to define public predicates

    public_predicates
}

pub fn prog_private_predicates(
    program: &asp::Program,
    publics: &HashSet<fol::Predicate>,
    needs_renaming: bool,
    prog_type: bool,
) -> HashSet<fol::Predicate> {
    let mut privates = HashSet::<fol::Predicate>::new();
    for p in program.predicates().iter() {
        let pred = fol::Predicate {
            symbol: p.symbol.clone(),
            arity: p.arity,
        };
        if !publics.contains(&pred) {
            if needs_renaming {
                let mut s = p.symbol.clone();
                if prog_type {
                    s.push_str("_1");
                } else {
                    s.push_str("_2");
                }
                let renamed_pred = fol::Predicate {
                    symbol: s,
                    arity: p.arity,
                };
                privates.insert(renamed_pred);
            } else {
                privates.insert(pred);
            }
        }
    }
    privates
}

pub fn spec_private_predicates(
    specification: &fol::Specification,
    publics: &HashSet<fol::Predicate>,
    needs_renaming: bool,
) -> HashSet<fol::Predicate> {
    let mut privates = HashSet::<fol::Predicate>::new();
    for spec in specification.specs.iter() {
        match spec {
            fol::Spec::Assumption { formula } | fol::Spec::Conjecture { formula } => {
                for pred in formula.predicates() {
                    if !publics.contains(&pred) {
                        if needs_renaming {
                            let mut s = pred.symbol.clone();
                            s.push_str("_2");
                            let renamed_pred = fol::Predicate {
                                symbol: s,
                                arity: pred.arity,
                            };
                            privates.insert(renamed_pred);
                        } else {
                            privates.insert(pred);
                        }
                    }
                }
            }
            _ => {
                println!("A specification should only contain assumptions and conjectures.");
            }
        }
    }
    privates
}

// For a formula of the form "forall X (p(X) <-> Body)" Return p/n
// For a formula of the form "forall X (Body -> #false)" Return None
// For a formula of the form "p <-> Body" Return p/0
pub fn formula_head(formula: &fol::Formula) -> Option<fol::Predicate> {
    match formula {
        fol::Formula::QuantifiedFormula { formula: f, .. } => match *f.clone() {
            fol::Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => match connective {
                fol::BinaryConnective::Equivalence => match *lhs {
                    fol::Formula::AtomicFormula(a) => match a {
                        fol::AtomicFormula::Atom(af) => Some(af.predicate()),
                        _ => todo!(),
                    },
                    _ => todo!(),
                },
                fol::BinaryConnective::Implication => match *rhs {
                    fol::Formula::AtomicFormula(a) => match a {
                        fol::AtomicFormula::Falsity => None,
                        _ => panic!(),
                    },
                    _ => panic!(),
                },
                _ => todo!(),
            },
            _ => todo!(),
        },
        fol::Formula::BinaryFormula { lhs, .. } => match lhs.clone().unbox() {
            UnboxedFormula::AtomicFormula(a) => match a {
                fol::AtomicFormula::Atom(af) => Some(af.predicate()),
                _ => todo!(),
            },
            _ => todo!(),
        },
        _ => todo!(),
    }
}

fn append_predicate(
    formula: fol::Formula,
    postfix: &'static str,
    publics: &HashSet<fol::Predicate>,
) -> fol::Formula {
    formula.apply(&mut |formula| match formula {
        fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(mut a)) => {
            if !publics.contains(&a.predicate()) {
                a.predicate_symbol.push_str(postfix);
            }
            fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(a))
        }
        x => x,
    })
}

pub fn rename_predicates(
    formula: fol::Formula,
    postfix: &'static str,
    publics: &HashSet<fol::Predicate>,
) -> fol::Formula {
    match formula {
        x @ fol::Formula::AtomicFormula(_) => append_predicate(x, postfix, publics),

        fol::Formula::UnaryFormula {
            connective: connective @ fol::UnaryConnective::Negation,
            formula,
        } => fol::Formula::UnaryFormula {
            connective,
            formula: append_predicate(*formula, postfix, publics).into(),
        },

        fol::Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => fol::Formula::BinaryFormula {
            connective,
            lhs: append_predicate(*lhs, postfix, publics).into(),
            rhs: append_predicate(*rhs, postfix, publics).into(),
        },

        fol::Formula::QuantifiedFormula {
            quantification,
            formula,
        } => fol::Formula::QuantifiedFormula {
            quantification,
            formula: append_predicate(*formula, postfix, publics).into(),
        },
    }
}

fn insert_replacement(formula: fol::Formula, placeholder: &str) -> fol::Formula {
    let replacement_name = format!("%-{}-%", placeholder.to_uppercase().to_string());
    let replacement = fol::GeneralTerm::IntegerTerm(fol::IntegerTerm::BasicIntegerTerm(
        fol::BasicIntegerTerm::IntegerVariable(replacement_name.clone()),
    ));
    let original = fol::GeneralTerm::Symbol(placeholder.to_string());

    formula.apply(&mut |formula| match formula {
        fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(mut a)) => {
            let n = a.terms.len();
            for i in 0..n - 1 {
                if a.terms[i] == original {
                    a.terms[i] = replacement.clone();
                }
            }
            fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(a))
        }
        fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(mut c)) => {
            if c.term == original {
                c.term = replacement.clone();
            }
            let n = c.guards.len();
            if n == 1 {
                if c.guards[0].term == original {
                    c.guards[0].term = replacement.clone();
                }
            } else {
                for i in 0..n - 1 {
                    if c.guards[i].term == original {
                        c.guards[i].term = replacement.clone();
                    }
                }
            }
            fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(c))
        }
        x => x,
    })
}

pub fn replace_placeholders(formula: fol::Formula, placeholder: &str) -> fol::Formula {
    //println!("Replacing {placeholder} within {formula}");
    match formula {
        x @ fol::Formula::AtomicFormula(_) => insert_replacement(x, placeholder),

        fol::Formula::UnaryFormula {
            connective: connective @ fol::UnaryConnective::Negation,
            formula,
        } => fol::Formula::UnaryFormula {
            connective,
            formula: insert_replacement(*formula, placeholder).into(),
        },

        fol::Formula::BinaryFormula {
            connective,
            lhs,
            rhs,
        } => fol::Formula::BinaryFormula {
            connective,
            lhs: insert_replacement(*lhs, placeholder).into(),
            rhs: insert_replacement(*rhs, placeholder).into(),
        },

        fol::Formula::QuantifiedFormula {
            quantification,
            formula,
        } => fol::Formula::QuantifiedFormula {
            quantification,
            formula: insert_replacement(*formula, placeholder).into(),
        },
    }
}

pub fn placeholder_replacements(
    formulas: &mut Vec<fol::Formula>,
    placeholders: &HashSet<fol::Placeholder>,
) {
    let mut borrow_nightmare = HashSet::new();
    for ph in placeholders.iter() {
        borrow_nightmare.insert(ph.name.clone());
    }
    //println!("Replacing {} placeholders within {} formulas", placeholders.len(), formulas.len());
    let n = formulas.len();
    for i in 0..=n - 1 {
        for ph in borrow_nightmare.iter() {
            formulas[i] = replace_placeholders(formulas[i].clone(), ph);
            //println!("\n\n%%%%%\nNew formula: {}\n%%%%%%", formulas[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::syntax_tree::fol;
    use super::equivalence_breaker;

    #[test]
    fn test_break_equivalences_some() {
        for (src, target) in [
            ("forall X (p(X) <-> q(X))", ["forall X (p(X) -> q(X))", "forall X (p(X) <- q(X))"]),
            ("forall X ((p(X) and q) <-> t)", ["forall X ((p(X) and q) -> t)", "forall X ((p(X) and q) <- t)"]),
            ("p <-> q", ["p -> q", "p <- q"]),
            ("p <-> q or t", ["p -> q or t", "p <- q or t"]),
            ("p(X) <-> q(X)", ["p(X) -> q(X)", "p(X) <- q(X)"]),
        ] {
            let f: fol::Formula = src.parse().unwrap();
            let result: Option<Vec<fol::Formula>> = Some(vec![target[0].parse().unwrap(), target[1].parse().unwrap()]);
            assert_eq!(result, equivalence_breaker(f))
        }
    }

    #[test]
    fn test_break_equivalences_none() {
        for src in [
            "forall X (p(X) -> q(X))",
            "q(a)",
            "forall X (p(X) and (q <-> t))",
        ] {
            let f: fol::Formula = src.parse().unwrap(); 
            assert_eq!(None, equivalence_breaker(f))
        }
    }
}
