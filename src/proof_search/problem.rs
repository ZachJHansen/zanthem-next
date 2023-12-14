use {
    crate::{
        convenience::{
            apply::Apply as _,
            unbox::fol::UnboxedFormula,
            unbox::Unbox,
        },
        formatting::fol::tptp::Format,
        syntax_tree::{asp, fol},
        translating::{completion::completion, tau_star::tau_star},
    },
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
                format!("\ntff({}, {}, {}).", name, role.display(), Format(formula))
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
    name: String,
    premises: Vec<fol::Formula>,
    conclusions: Vec<fol::Formula>,
    status: ProblemStatus,
}

impl Claim {
    pub fn decompose_claim(
        &self,
        problem_predicates: &Vec<Statement>,
        problem_functions: &Vec<Statement>,
    ) -> Vec<Problem> {
        let mut problems = Vec::<Problem>::new();
        for conclusion in self.conclusions.iter() {
            problems.push(Problem {
                status: ProblemStatus::Unknown,
                interpretation: Interpretation::Standard,
                predicates: problem_predicates.clone(),
                functions: problem_functions.clone(),
                axioms: self.premises.clone(),
                conjecture: conclusion.clone(),
            });
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
    predicates: Vec<Statement>,
    functions: Vec<Statement>,
    interpretation: Interpretation,
    memory: Vec<Claim>,
    pub goals: HashMap<Claim, Vec<Problem>>,
}

// Forward direction: assume program publics, prove spec publics
// Backward direction: assume spec publics, prove program publics
impl ProblemHandler {
    pub fn init(
        program: &asp::Program,
        specification: &FileType,
        user_guide: &fol::Specification,
    ) -> Self {
        let needs_renaming = match &specification {
            &FileType::MiniGringoProgram { .. } => true,
            &FileType::FirstOrderSpecification { .. } => false,
        };

        let public_predicates = public_predicates(specification, user_guide);

        let spec_private_predicates = match &specification {
            &FileType::MiniGringoProgram { program: p } => {
                prog_private_predicates(p, &public_predicates, needs_renaming, true);
            },
            &FileType::FirstOrderSpecification { specification: s } => {
                spec_private_predicates(s, &public_predicates, needs_renaming);
            },
        };

        let program_private_predicates =
            prog_private_predicates(program, &public_predicates, needs_renaming);

        let problem_predicates = public_predicates.union(&program_private_predicates);
        //  TODO - how to handle spec private predicates? are they part of the problem types? or only for one direction?

        let mut forward_premises = Vec::<fol::Formula>::new();
        let mut forward_conclusions = Vec::<fol::Formula>::new();

        let mut backward_premises = Vec::<fol::Formula>::new();
        let mut backward_conclusions = Vec::<fol::Formula>::new();

        let mut functions = Vec::<Statement>::new();
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
            needs_renaming,
        );

        parse_user_guide(
            user_guide,
            &mut forward_premises,
            &mut backward_premises,
            &mut predicates,
            &mut functions,
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

        let mut goals: HashMap<Claim, Vec<Problem>> = HashMap::new();
        goals.insert(
            forward.clone(),
            forward.decompose_claim(&predicates, &functions),
        );
        goals.insert(
            backward.clone(),
            backward.decompose_claim(&predicates, &functions),
        );

        ProblemHandler {
            predicates,
            functions,
            interpretation: Interpretation::Standard,
            memory: vec![],
            goals,
        }
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
}

pub fn parse_specification(
    specification: &FileType,
    forward_premises: &mut Vec<fol::Formula>,
    backward_premises: &mut Vec<fol::Formula>,
    forward_conclusions: &mut Vec<fol::Formula>,
    predicates: &mut Vec<Statement>,
    functions: &mut Vec<Statement>,
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
                            rename_predicates(f.clone(), "_2", public_predicates)
                        } else {
                            f.clone()
                        };
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
            for (i, spec) in s.specs.iter().enumerate() {
                match spec {
                    fol::Spec::PlaceholderDeclaration { placeholders } => {
                        for ph in placeholders.iter() {
                            functions.push(Statement::TypedAtom {
                                name: ["statement", i.to_string().as_str()].join("_"),
                                atom: ph.name.clone(),
                                spec: TypeSpec {
                                    return_type: VampireTypes::Int,
                                    args: vec![],
                                },
                            });
                        }
                    }
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
                    }
                    fol::Spec::Conjecture { formula } => {
                        forward_conclusions.push(formula.clone());
                        backward_premises.push(formula.clone());
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
    needs_renaming: bool,
) {
    let gamma = completion(&tau_star(program.clone()));
    match gamma {
        Some(completion) => {
            for f in completion.formulas.iter() {
                let formula = if needs_renaming {
                    rename_predicates(f.clone(), "_1", public_predicates)
                } else {
                    f.clone()
                };
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
    functions: &mut Vec<Statement>,
) {
    let mut fns = Vec::<Statement>::new();
    let mut preds = Vec::<Statement>::new();
    let mut axioms = Vec::<fol::Formula>::new();

    for (i, spec) in user_guide.specs.iter().enumerate() {
        match spec {
            fol::Spec::PlaceholderDeclaration { placeholders } => {
                for ph in placeholders.iter() {
                    fns.push(Statement::TypedAtom {
                        name: ["statement", i.to_string().as_str()].join("_"),
                        atom: ph.name.clone(),
                        spec: TypeSpec {
                            return_type: VampireTypes::Int,
                            args: vec![],
                        },
                    });
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
    functions.extend(fns);
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
                    if !publics.contains(pred) {
                        if needs_renaming {
                            let mut s = p.symbol.clone();
                            s.push_str("_2");
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
            },
            _ => {
                println!("A specification should only contain assumptions and conjectures.");
            },
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
                        fol::AtomicFormula::Atom(af) => Some(af.predicate),
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
        fol::Formula::BinaryFormula {
            lhs,
            ..
        } => match lhs.clone().unbox() {
            UnboxedFormula::AtomicFormula(a) => match a {
                fol::AtomicFormula::Atom(af) => Some(af.predicate),
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
            if !publics.contains(&a.predicate) {
                a.predicate.symbol.push_str(postfix);
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