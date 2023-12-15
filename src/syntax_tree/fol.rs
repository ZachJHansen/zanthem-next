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

    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            IntegerTerm::BasicIntegerTerm(_) => HashSet::new(),
            IntegerTerm::UnaryOperation { arg: t, .. } => t.function_constants(),
            IntegerTerm::BinaryOperation { lhs, rhs, .. } => {
                let mut fns = lhs.function_constants();
                fns.extend(rhs.function_constants());
                fns
            }
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
            GeneralTerm::GeneralVariable(v) => HashSet::new(),
            GeneralTerm::IntegerTerm(t) => t.function_constants(),
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
            },
            AtomicFormula::Comparison(c) => {
                let mut fns = c.term.function_constants();
                for guard in c.guards.iter() {
                    fns.extend(guard.function_constants())
                }
                fns
            },
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
    use super::Formula;

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
}
