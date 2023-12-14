use {
    crate::{
        formatting::asp::default::Format,
        parsing::asp::pest::{
            AtomParser, AtomicFormulaParser, BinaryOperatorParser, BodyParser, ComparisonParser,
            HeadParser, LiteralParser, PrecomputedTermParser, PredicateParser, ProgramParser,
            RelationParser, RuleParser, SignParser, TermParser, UnaryOperatorParser,
            VariableParser,
        },
        syntax_tree::{impl_node, Node},
    },
    std::collections::HashSet,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PrecomputedTerm {
    Infimum,
    Numeral(isize),
    Symbol(String),
    Supremum,
}

impl PrecomputedTerm {
    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            PrecomputedTerm::Infimum => HashSet::new(),
            PrecomputedTerm::Numeral(_) => HashSet::new(),
            PrecomputedTerm::Symbol(s) => HashSet::from([s.clone()]),
            PrecomputedTerm::Supremum => HashSet::new(),
        }
    }
}

impl_node!(PrecomputedTerm, Format, PrecomputedTermParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Variable(pub String);

impl_node!(Variable, Format, VariableParser);

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum UnaryOperator {
    Negative,
}

impl_node!(UnaryOperator, Format, UnaryOperatorParser);

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub enum BinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Interval,
}

impl_node!(BinaryOperator, Format, BinaryOperatorParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Term {
    PrecomputedTerm(PrecomputedTerm),
    Variable(Variable),
    UnaryOperation {
        op: UnaryOperator,
        arg: Box<Term>,
    },
    BinaryOperation {
        op: BinaryOperator,
        lhs: Box<Term>,
        rhs: Box<Term>,
    },
}

impl_node!(Term, Format, TermParser);

impl Term {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            Term::PrecomputedTerm(_) => HashSet::new(),
            Term::Variable(v) => HashSet::from([v.clone()]),
            Term::UnaryOperation { arg, .. } => arg.variables(),
            Term::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }

    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            Term::PrecomputedTerm(t) => t.function_constants(),
            Term::Variable(_) => HashSet::new(),
            Term::UnaryOperation { arg, .. } => arg.function_constants(),
            Term::BinaryOperation { lhs, rhs, .. } => {
                let mut functions = lhs.function_constants();
                functions.extend(rhs.function_constants());
                functions
            }
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
    pub terms: Vec<Term>,
}

impl_node!(Atom, Format, AtomParser);

impl Atom {
    pub fn predicate(&self) -> Predicate {
        Predicate {
            symbol: self.predicate_symbol.clone(),
            arity: self.terms.len(),
        }
    }

    pub fn variables(&self) -> HashSet<Variable> {
        let mut vars = HashSet::new();
        for term in self.terms.iter() {
            vars.extend(term.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> HashSet<String> {
        let mut functions = HashSet::new();
        for term in self.terms.iter() {
            functions.extend(term.function_constants())
        }
        functions
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Sign {
    NoSign,
    Negation,
    DoubleNegation,
}

impl_node!(Sign, Format, SignParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Literal {
    pub sign: Sign,
    pub atom: Atom,
}

impl_node!(Literal, Format, LiteralParser);

impl Literal {
    pub fn predicate(&self) -> Predicate {
        self.atom.predicate()
    }

    pub fn variables(&self) -> HashSet<Variable> {
        self.atom.variables()
    }

    pub fn function_constants(&self) -> HashSet<String> {
        self.atom.function_constants()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Relation {
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

impl_node!(Relation, Format, RelationParser);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Comparison {
    pub relation: Relation,
    pub lhs: Term,
    pub rhs: Term,
}

impl_node!(Comparison, Format, ComparisonParser);

impl Comparison {
    pub fn variables(&self) -> HashSet<Variable> {
        let mut vars = self.lhs.variables();
        vars.extend(self.rhs.variables());
        vars
    }

    pub fn function_constants(&self) -> HashSet<String> {
        let mut functions = self.lhs.function_constants();
        functions.extend(self.rhs.function_constants());
        functions
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum AtomicFormula {
    Literal(Literal),
    Comparison(Comparison),
}

impl_node!(AtomicFormula, Format, AtomicFormulaParser);

impl AtomicFormula {
    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            AtomicFormula::Literal(l) => l.variables(),
            AtomicFormula::Comparison(c) => c.variables(),
        }
    }

    pub fn predicates(&self) -> HashSet<Predicate> {
        match &self {
            AtomicFormula::Literal(l) => HashSet::from([l.predicate()]),
            AtomicFormula::Comparison(_) => HashSet::new(),
        }
    }

    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            AtomicFormula::Literal(l) => l.function_constants(),
            AtomicFormula::Comparison(c) => c.function_constants(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Head {
    Basic(Atom),
    Choice(Atom),
    Falsity,
}

impl_node!(Head, Format, HeadParser);

impl Head {
    pub fn predicate(&self) -> Option<Predicate> {
        match self {
            Head::Basic(a) => Some(a.predicate()),
            Head::Choice(a) => Some(a.predicate()),
            Head::Falsity => None,
        }
    }

    // TODO: Revisit these helper function; make sure they are symmetric with all the others.

    pub fn terms(&self) -> Option<&[Term]> {
        match self {
            Head::Basic(a) => Some(&a.terms),
            Head::Choice(a) => Some(&a.terms),
            Head::Falsity => None,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Head::Basic(a) => a.terms.len(),
            Head::Choice(a) => a.terms.len(),
            Head::Falsity => 0,
        }
    }

    pub fn variables(&self) -> HashSet<Variable> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.variables(),
            Head::Falsity => HashSet::new(),
        }
    }

    pub fn function_constants(&self) -> HashSet<String> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.function_constants(),
            Head::Falsity => HashSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Body {
    pub formulas: Vec<AtomicFormula>,
}

impl_node!(Body, Format, BodyParser);

impl Body {
    pub fn variables(&self) -> HashSet<Variable> {
        let mut vars = HashSet::new();
        for formula in self.formulas.iter() {
            vars.extend(formula.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> HashSet<String> {
        let mut functions = HashSet::new();
        for formula in self.formulas.iter() {
            functions.extend(formula.function_constants())
        }
        functions
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Rule {
    pub head: Head,
    pub body: Body,
}

impl_node!(Rule, Format, RuleParser);

impl Rule {
    pub fn variables(&self) -> HashSet<Variable> {
        let mut vars = self.head.variables();
        vars.extend(self.body.variables());
        vars
    }

    pub fn function_constants(&self) -> HashSet<String> {
        let mut functions = self.head.function_constants();
        functions.extend(self.body.function_constants());
        functions
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Program {
    pub rules: Vec<Rule>,
}

impl_node!(Program, Format, ProgramParser);

impl Program {
    pub fn variables(&self) -> HashSet<Variable> {
        let mut vars = HashSet::new();
        for rule in self.rules.iter() {
            vars.extend(rule.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> HashSet<String> {
        let mut functions = HashSet::new();
        for rule in self.rules.iter() {
            functions.extend(rule.function_constants());
        }
        functions
    }
}
