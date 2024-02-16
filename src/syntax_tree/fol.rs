use {
    crate::{
        formatting::fol::default::Format,
        parsing::fol::pest::{
            AtomParser, AtomicFormulaParser, BasicIntegerTermParser, BinaryConnectiveParser,
            BinaryOperatorParser, ComparisonParser, FormulaParser, GeneralTermParser, GuardParser,
            IntegerTermParser, LemmaParser, PlaceholderParser, PredicateParser,
            QuantificationParser, QuantifierParser, RelationParser, SpecParser,
            SpecificationParser, TheoryParser, UnaryConnectiveParser, UnaryOperatorParser,
            VariableParser,
        },
        syntax_tree::{impl_node, Node},
    },
    std::{collections::HashSet, hash::Hash},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BasicIntegerTerm {
    Infimum,
    Supremum,
    Numeral(isize),
    IntegerVariable(String),
}

impl_node!(BasicIntegerTerm, Format, BasicIntegerTermParser);

impl BasicIntegerTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            BasicIntegerTerm::IntegerVariable(v) => HashSet::from([Variable {
                name: v.to_string(),
                sort: Sort::Integer,
            }]),
            _ => HashSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
}

impl_node!(BinaryOperator, Format, BinaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum IntegerTerm {
    BasicIntegerTerm(BasicIntegerTerm),
    UnaryOperation {
        op: UnaryOperator,
        arg: Box<IntegerTerm>,
    },
    BinaryOperation {
        op: BinaryOperator,
        lhs: Box<IntegerTerm>,
        rhs: Box<IntegerTerm>,
    },
}

impl_node!(IntegerTerm, Format, IntegerTermParser);

impl IntegerTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            IntegerTerm::BasicIntegerTerm(t) => t.variables(),
            IntegerTerm::UnaryOperation { arg: t, .. } => t.variables(),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }

    pub fn substitute(self, var: Variable, term: IntegerTerm) -> Self {
        match self {
            IntegerTerm::BasicIntegerTerm(t) => match t {
                BasicIntegerTerm::IntegerVariable(s)
                    if var.name == s && var.sort == Sort::Integer =>
                {
                    term
                }
                _ => IntegerTerm::BasicIntegerTerm(t),
            },
            IntegerTerm::UnaryOperation { op, arg } => IntegerTerm::UnaryOperation {
                op,
                arg: arg.substitute(var, term).into(),
            },
            IntegerTerm::BinaryOperation { op, lhs, rhs } => IntegerTerm::BinaryOperation {
                op,
                lhs: lhs.substitute(var.clone(), term.clone()).into(),
                rhs: rhs.substitute(var, term).into(),
            },
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum GeneralTerm {
    Symbol(String),
    GeneralVariable(String),
    IntegerTerm(IntegerTerm),
}

impl_node!(GeneralTerm, Format, GeneralTermParser);

impl GeneralTerm {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            GeneralTerm::Symbol(_) => HashSet::new(),
            GeneralTerm::GeneralVariable(v) => HashSet::from([Variable {
                name: v.to_string(),
                sort: Sort::General,
            }]),
            GeneralTerm::IntegerTerm(t) => t.variables(),
        }
    }

    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            GeneralTerm::Symbol(s) => HashSet::from([s.to_string()]),
            GeneralTerm::GeneralVariable(_) | GeneralTerm::IntegerTerm(_) => HashSet::new(),
        }
    }

    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self.clone() {
            GeneralTerm::GeneralVariable(s) if var.name == s && var.sort == Sort::General => term,
            GeneralTerm::IntegerTerm(t) if var.sort == Sort::Integer => match term {
                GeneralTerm::IntegerTerm(term) => GeneralTerm::IntegerTerm(t.substitute(var, term)),
                _ => panic!("cannot substitute general term `{term}` for the integer variable `{var}`"),
            },
            t => t,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Predicate {
    pub symbol: String,
    pub arity: usize,
}

impl_node!(Predicate, Format, PredicateParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Atom {
    pub predicate_symbol: String,
    pub terms: Vec<GeneralTerm>,
}

impl Atom {
    pub fn predicate(&self) -> Predicate {
        Predicate {
            symbol: self.predicate_symbol.clone(),
            arity: self.terms.len(),
        }
    }
}

impl_node!(Atom, Format, AtomParser);

impl Atom {
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        let predicate_symbol = self.predicate_symbol;

        let mut terms = Vec::new();
        for t in self.terms {
            terms.push(t.substitute(var.clone(), term.clone()))
        }

        Atom {
            predicate_symbol,
            terms,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Relation {
    Equal,
    NotEqual,
    Greater,
    Less,
    GreaterEqual,
    LessEqual,
}

impl_node!(Relation, Format, RelationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Guard {
    pub relation: Relation,
    pub term: GeneralTerm,
}

impl_node!(Guard, Format, GuardParser);

impl Guard {
    pub fn variables(&self) -> HashSet<Variable> {
        self.term.variables()
    }

    pub fn function_constants(&self) -> HashSet<String> {
        self.term.function_constants()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Comparison {
    pub term: GeneralTerm,
    pub guards: Vec<Guard>,
}

impl_node!(Comparison, Format, ComparisonParser);

impl Comparison {
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        let lhs = self.term.substitute(var.clone(), term.clone());

        let mut guards = Vec::new();
        for old_guard in self.guards {
            let new_guard = Guard {
                relation: old_guard.relation,
                term: old_guard.term.substitute(var.clone(), term.clone()),
            };
            guards.push(new_guard);
        }

        Comparison { term: lhs, guards }
    }

    pub fn equality_comparison(&self) -> bool {
        let guards = &self.guards;
        let first = &guards[0];
        if guards.len() == 1 && first.relation == Relation::Equal {
            return true;
        } else {
            return false;
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AtomicFormula {
    Truth,
    Falsity,
    Atom(Atom),
    Comparison(Comparison),
}

impl_node!(AtomicFormula, Format, AtomicFormulaParser);

impl AtomicFormula {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => HashSet::new(),
            AtomicFormula::Atom(a) => {
                let mut vars = HashSet::new();
                for t in a.terms.iter() {
                    vars.extend(t.variables());
                }
                vars
            }
            AtomicFormula::Comparison(c) => {
                let mut vars = c.term.variables();
                for guard in c.guards.iter() {
                    vars.extend(guard.variables())
                }
                vars
            }
        }
    }

    pub fn predicates(&self) -> HashSet<Predicate> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth | AtomicFormula::Comparison(_) => {
                HashSet::new()
            }
            AtomicFormula::Atom(a) => HashSet::from([a.predicate()]),
        }
    }

    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            AtomicFormula::Falsity | AtomicFormula::Truth => HashSet::new(),
            AtomicFormula::Atom(a) => {
                let mut fns = HashSet::new();
                for t in a.terms.iter() {
                    fns.extend(t.function_constants());
                }
                fns
            }
            AtomicFormula::Comparison(c) => {
                let mut fns = c.term.function_constants();
                for guard in c.guards.iter() {
                    fns.extend(guard.function_constants())
                }
                fns
            }
        }
    }

    // TODO
    pub fn contains_variable(&self, v: &Variable) -> bool {
        self.variables().contains(v)
    }

    // TODO
    pub fn contains_free_variable(&self, v: &Variable) -> bool {
        self.contains_variable(v)
    }

    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            AtomicFormula::Atom(a) => AtomicFormula::Atom(a.substitute(var, term)),
            AtomicFormula::Comparison(c) => AtomicFormula::Comparison(c.substitute(var, term)),
            f => f,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryConnective {
    Negation,
}

impl_node!(UnaryConnective, Format, UnaryConnectiveParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

impl_node!(Quantifier, Format, QuantifierParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Quantification {
    pub quantifier: Quantifier,
    pub variables: Vec<Variable>,
}

impl_node!(Quantification, Format, QuantificationParser);

impl Quantification {
    pub fn occurs(&self, v: &Variable) -> bool {
        self.variables.contains(v)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Sort {
    Integer,
    General,
}

// TODO: Should Sort be a Node?

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Variable {
    pub name: String,
    pub sort: Sort,
}

impl_node!(Variable, Format, VariableParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryConnective {
    Conjunction,
    Disjunction,
    Implication,
    ReverseImplication,
    Equivalence,
}

impl_node!(BinaryConnective, Format, BinaryConnectiveParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Formula {
    AtomicFormula(AtomicFormula),
    UnaryFormula {
        connective: UnaryConnective,
        formula: Box<Formula>,
    },
    BinaryFormula {
        connective: BinaryConnective,
        lhs: Box<Formula>,
        rhs: Box<Formula>,
    },
    QuantifiedFormula {
        quantification: Quantification,
        formula: Box<Formula>,
    },
}

impl_node!(Formula, Format, FormulaParser);

impl Formula {
    /// Recursively turn a list of formulas into a conjunction tree
    pub fn conjoin(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        /*
         * One could also implement this recursively:
         *
         * Case 1: List of formulas is empty
         * -> Return #true
         *
         * Case 2: List of formulas contains a single formula
         * -> Return that formula
         *
         * Case 3: List of formulas contains more than a single formula
         * -> Return conjoin(formula[0..n-2]) and formula[n-1]
         */

        formulas
            .into_iter()
            .reduce(|acc, e| Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs: acc.into(),
                rhs: e.into(),
            })
            .unwrap_or_else(|| Formula::AtomicFormula(AtomicFormula::Truth))
    }

    // Inverse function to conjoin
    pub fn conjoin_invert(formula: Formula) -> Vec<Formula> {
        match formula {
            Formula::BinaryFormula {
                connective: BinaryConnective::Conjunction,
                lhs,
                rhs,
            } => {
                let mut formulas = Self::conjoin_invert(*lhs);
                formulas.append(&mut Self::conjoin_invert(*rhs));
                return formulas;
            }
            _ => {
                return vec![formula];
            }
        }
    }

    /// Recursively turn a list of formulas into a tree of disjunctions
    pub fn disjoin(formulas: impl IntoIterator<Item = Formula>) -> Formula {
        /*
         * One could also implement this recursively:
         *
         * Case 1: List of formulas is empty
         * -> Return #false
         *
         * Case 2: List of formulas contains a single formula
         * -> Return that formula
         *
         * Case 3: List of formulas contains more than a single formula
         * -> Return conjoin(formula[0..n-2]) or formula[n-1]
         */

        formulas
            .into_iter()
            .reduce(|acc, e| Formula::BinaryFormula {
                connective: BinaryConnective::Disjunction,
                lhs: acc.into(),
                rhs: e.into(),
            })
            .unwrap_or_else(|| Formula::AtomicFormula(AtomicFormula::Falsity))
    }

    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            Formula::AtomicFormula(f) => f.variables(),
            Formula::UnaryFormula { formula, .. } => formula.variables(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.variables(),
        }
    }

    pub fn free_variables(&self) -> HashSet<Variable> {
        match &self {
            Formula::AtomicFormula(f) => f.variables(),
            Formula::UnaryFormula { formula, .. } => formula.free_variables(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.free_variables();
                vars.extend(rhs.free_variables());
                vars
            }
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => {
                let mut vars = formula.free_variables();
                for var in &quantification.variables {
                    vars.remove(var);
                }
                vars
            }
        }
    }

    pub fn predicates(&self) -> HashSet<Predicate> {
        match &self {
            Formula::AtomicFormula(f) => f.predicates(),
            Formula::UnaryFormula { formula, .. } => formula.predicates(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut vars = lhs.predicates();
                vars.extend(rhs.predicates());
                vars
            }
            Formula::QuantifiedFormula { formula, .. } => formula.predicates(),
        }
    }

    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            Formula::AtomicFormula(f) => f.function_constants(),
            Formula::UnaryFormula { formula, .. } => formula.function_constants(),
            Formula::BinaryFormula { lhs, rhs, .. } => {
                let mut fns = lhs.function_constants();
                fns.extend(rhs.function_constants());
                fns
            }
            Formula::QuantifiedFormula { formula, .. } => formula.function_constants(),
        }
    }

    pub fn contains_free_variable(&self, v: &Variable) -> bool {
        match &self {
            Formula::AtomicFormula(a) => a.contains_free_variable(v),
            Formula::UnaryFormula {
                connective: _,
                formula: f,
            } => f.contains_free_variable(v),
            Formula::QuantifiedFormula {
                quantification: q,
                formula: f,
            } => f.contains_free_variable(v) && !q.occurs(v),
            Formula::BinaryFormula {
                connective: _,
                lhs: f1,
                rhs: f2,
            } => f1.contains_free_variable(v) || f2.contains_free_variable(v),
        }
    }

    // Replace all free occurences of var with term within the formula
    pub fn substitute(self, var: Variable, term: GeneralTerm) -> Self {
        match self {
            Formula::AtomicFormula(f) => Formula::AtomicFormula(f.substitute(var, term)),
            Formula::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula.substitute(var, term).into(),
            },
            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.substitute(var.clone(), term.clone()).into(),
                rhs: rhs.substitute(var, term).into(),
            },
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } if !quantification.variables.contains(&var) => Formula::QuantifiedFormula {
                quantification,
                formula: formula.substitute(var, term).into(),
            },
            f @ Formula::QuantifiedFormula {
                quantification: _,
                formula: _,
            } => f,
        }
    }

    // Replacing var with term within self is unsafe if self contains a subformula
    // of the form QxF, where var is free in F and a variable in term occurs in x
    pub fn unsafe_substitution(self, var: &Variable, term: &GeneralTerm) -> bool {
        match self {
            Formula::AtomicFormula(_) => false,
            Formula::UnaryFormula {
                formula,
                ..
            } => formula.unsafe_substitution(var, term),
            Formula::BinaryFormula {
                lhs,
                rhs,
                ..
            } => {
                lhs.unsafe_substitution(var, term) || rhs.unsafe_substitution(var, term)
            }
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => {
                let tvars = term.variables();
                let qvars = HashSet::from_iter(quantification.variables);
                let overlap: HashSet<&Variable> = tvars.intersection(&qvars).collect();
                formula.contains_free_variable(var) && !overlap.is_empty() 
            }
        }
    }

    pub fn rename_variables(self, count: usize) -> (Formula, usize) {
        match self {
            Formula::QuantifiedFormula {
                quantification: q,
                formula: f,
            } => {
                let mut fcount = count;
                let mut f1 = *f;
                let mut vars = vec![];
                for (i, var) in q.variables.iter().enumerate() {
                    let mut x = "X".to_owned();
                    x.push_str((count + i + 1).to_string().as_str());
                    let new_var = Variable {
                        name: x,
                        sort: var.clone().sort,
                    };
                    vars.push(new_var.clone());
                    let new_term = match var.sort {
                        Sort::General => GeneralTerm::GeneralVariable(new_var.name),
                        Sort::Integer => GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::IntegerVariable(new_var.clone().name),
                        )),
                    };
                    f1 = f1.substitute(var.clone(), new_term);
                    fcount = count + i + 1;
                }
                (
                    Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: q.quantifier,
                            variables: vars,
                        },
                        formula: f1.into(),
                    },
                    fcount,
                )
            }
            x => (x, count),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Theory {
    pub formulas: Vec<Formula>,
}

impl_node!(Theory, Format, TheoryParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Placeholder {
    pub name: String,
}

impl_node!(Placeholder, Format, PlaceholderParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Direction {
    Forward,
    Backward,
    Universal,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Lemma {
    pub direction: Direction,
    pub formula: Formula,
}

impl_node!(Lemma, Format, LemmaParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Spec {
    Input { predicates: Vec<Predicate> },
    Output { predicates: Vec<Predicate> },
    PlaceholderDeclaration { placeholders: Vec<Placeholder> },
    Assumption { formula: Formula },
    Conjecture { formula: Formula },
    Lemma(Lemma),
}

impl_node!(Spec, Format, SpecParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Specification {
    pub specs: Vec<Spec>,
}

impl_node!(Specification, Format, SpecificationParser);

#[cfg(test)]
mod tests {
    use super::{Formula, Variable, GeneralTerm};

    #[test]
    fn test_formula_conjoin() {
        for (src, target) in [
            (vec![], "#true"),
            (vec!["X = Y"], "X = Y"),
            (vec!["X = Y", "p(a)", "q(X)"], "(X = Y and p(a)) and q(X)"),
        ] {
            assert_eq!(
                Formula::conjoin(src.iter().map(|x| x.parse().unwrap())),
                target.parse().unwrap(),
            )
        }
    }

    #[test]
    fn test_conjoin_invert() {
        for src in [
            vec!["X = Y"],
            vec!["X = Y", "p(a)", "q(X)"],
            vec!["X < Y < 3", "exists Y (Y > 1)"],
        ] {
            let formulas: Vec<Formula> = src.iter().map(|x| x.parse().unwrap()).collect();
            assert_eq!(
                Formula::conjoin_invert(Formula::conjoin(formulas.clone())),
                formulas,
            )
        }
    }

    #[test]
    fn test_formula_disjoin() {
        for (src, target) in [
            (vec![], "#false"),
            (vec!["X = Y"], "X = Y"),
            (vec!["X = Y", "p(a)", "q(X)"], "(X = Y or p(a)) or q(X)"),
        ] {
            assert_eq!(
                Formula::disjoin(src.iter().map(|x| x.parse().unwrap())),
                target.parse().unwrap(),
            )
        }
    }

    #[test]
    fn test_rename_variables() {
        for (src, target) in [
            ("exists X Y (X = Y)", "exists X1 X2 (X1 = X2)"),
            (
                "exists N M (exists N (N = M and p(N)) or q(N))",
                "exists X1 X2 (exists N (N = X2 and p(N)) or q(X1))",
            ),
        ] {
            let src = src.parse::<Formula>().unwrap().rename_variables(0).0;
            let target = target.parse().unwrap();
            assert_eq!(src, target, "{src} != {target}")
        }
    }

    #[test]
    fn test_formula_free_variables() {
        for (src, target) in [
            ("forall X (X = Y)", vec!["Y"]),
            ("forall X (X = Y) and Y = Z", vec!["Y", "Z"]),
            ("forall X exists Y (X = Y)", vec![]),
        ] {
            assert_eq!(
                src.parse::<Formula>().unwrap().free_variables(),
                target.iter().map(|x| x.parse().unwrap()).collect(),
            )
        }
    }

    #[test]
    fn test_substitute_formula() {
        for (src, target) in [
            (vec!["p(X)", "X", "s"], "p(s)"),
            (vec!["p(X)", "X", "5"], "p(5)"),
            (
                vec!["prime(-X$i + 13)", "X$i", "3*Y$i"],
                "prime(-(3*Y$i) + 13)",
            ),
            (vec!["prime(X$i, X)", "X$i", "Y$i"], "prime(Y$i, X)"),
            (vec!["exists X (X = Y)", "Y", "3"], "exists X (X = 3)"),
            (
                vec!["exists X (X = Y)", "Y", "X$i + 3"],
                "exists X (X = (X$i + 3))",
            ),
            (
                vec!["forall X (q(Y) or exists Y (p(1,Y) and X > Y))", "Y", "a"],
                "forall X (q(a) or exists Y (p(1,Y) and X > Y))",
            ),
            (
                vec![
                    "forall X (q(Y$i) or exists Z (p(1,Z) and X > Y$i > Z))",
                    "Y$i",
                    "4",
                ],
                "forall X (q(4) or exists Z (p(1,Z) and X > 4 > Z))",
            ),
        ] {
            assert_eq!(
                src[0]
                    .parse::<Formula>()
                    .unwrap()
                    .substitute(src[1].parse().unwrap(), src[2].parse().unwrap()),
                target.parse().unwrap()
            )
        }
    }

    #[test]
    fn test_unsafe_substitution() {
        for (src, target) in [
            (vec!["exists X (p(X, V))", "V", "Y"], false),      // Safe
            (vec!["exists X (p(X, V))", "V", "X"], true),       // Unsafe
            (vec!["forall Y (q(Y)) and exists X (p(X) or X < V)", "V", "3"], false),
            (vec!["forall Y (q(Y)) and exists X (p(X) or X < V)", "V", "X"], true),
            (vec!["q(V) -> exists X Y$ Z$ (X = Y$ or Z$ < 1 and p(V))", "V", "(Y$+1)*3"], true),
            (vec!["q(V) -> exists X Z$ (X = Y$ or Z$ < 1 and p(V))", "V", "(Y$+1)*3"], false),
        ] {
            let f: Formula = src[0].parse().unwrap();
            let v: Variable = src[1].parse().unwrap();
            let t: GeneralTerm = src[2].parse().unwrap();
            assert_eq!(f.unsafe_substitution(&v, &t), target)
        }
    }
}
