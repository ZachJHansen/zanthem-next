use {
    crate::{
        convenience::choose_fresh_variable_names,
        formatting::asp::default::Format,
        parsing::asp::pest::{
            AtomParser, AtomicFormulaParser, BinaryOperatorParser, BodyParser, ComparisonParser,
            HeadParser, LiteralParser, PrecomputedTermParser, PredicateParser, ProgramParser,
            RelationParser, RuleParser, SignParser, TermParser, UnaryOperatorParser,
            VariableParser,
        },
        syntax_tree::{impl_node, Node},
    },
    indexmap::IndexSet,
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PrecomputedTerm {
    Infimum,
    Numeral(isize),
    Symbol(String),
    Supremum,
}

impl PrecomputedTerm {
    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            PrecomputedTerm::Infimum => IndexSet::new(),
            PrecomputedTerm::Numeral(_) => IndexSet::new(),
            PrecomputedTerm::Symbol(s) => IndexSet::from([s.clone()]),
            PrecomputedTerm::Supremum => IndexSet::new(),
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
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            Term::PrecomputedTerm(_) => IndexSet::new(),
            Term::Variable(v) => IndexSet::from([v.clone()]),
            Term::UnaryOperation { arg, .. } => arg.variables(),
            Term::BinaryOperation { lhs, rhs, .. } => {
                let mut vars = lhs.variables();
                vars.extend(rhs.variables());
                vars
            }
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            Term::PrecomputedTerm(t) => t.function_constants(),
            Term::Variable(_) => IndexSet::new(),
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

impl Predicate {
    fn forget_successors(&self) -> Rule {
        let variables = choose_fresh_variable_names(&IndexSet::new(), "X", self.arity - 1);
        let mut terms: Vec<Term> = variables
            .into_iter()
            .map(|v| Term::Variable(Variable(v)))
            .collect();
        let head = Head::Basic(Atom {
            predicate_symbol: self.symbol.clone(),
            terms: terms.clone(),
        });

        terms.push(Term::Variable(Variable("N".to_string())));
        let body = Body {
            formulas: vec![AtomicFormula::Literal(Literal {
                sign: Sign::NoSign,
                atom: Atom {
                    predicate_symbol: self.symbol.clone(),
                    terms,
                },
            })],
        };

        Rule { head, body }
    }
}

impl_node!(Predicate, Format, PredicateParser);

impl From<crate::syntax_tree::fol::Predicate> for Predicate {
    fn from(value: crate::syntax_tree::fol::Predicate) -> Self {
        Predicate {
            symbol: value.symbol,
            arity: value.arity,
        }
    }
}

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

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for term in self.terms.iter() {
            vars.extend(term.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
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

    pub fn variables(&self) -> IndexSet<Variable> {
        self.atom.variables()
    }

    pub fn function_constants(&self) -> IndexSet<String> {
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
    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.lhs.variables();
        vars.extend(self.rhs.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
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
    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            AtomicFormula::Literal(l) => l.variables(),
            AtomicFormula::Comparison(c) => c.variables(),
        }
    }

    pub fn predicates(&self) -> IndexSet<Predicate> {
        match &self {
            AtomicFormula::Literal(l) => IndexSet::from([l.predicate()]),
            AtomicFormula::Comparison(_) => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
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

    pub fn variables(&self) -> IndexSet<Variable> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.variables(),
            Head::Falsity => IndexSet::new(),
        }
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        match &self {
            Head::Basic(a) | Head::Choice(a) => a.function_constants(),
            Head::Falsity => IndexSet::new(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Body {
    pub formulas: Vec<AtomicFormula>,
}

impl_node!(Body, Format, BodyParser);

impl Body {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for formula in self.formulas.iter() {
            predicates.extend(formula.predicates())
        }
        predicates
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for formula in self.formulas.iter() {
            vars.extend(formula.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for formula in self.formulas.iter() {
            functions.extend(formula.function_constants())
        }
        functions
    }

    fn tighten(self, variable: Variable) -> Body {
        let mut formulas = Vec::new();
        for formula in self.formulas {
            match formula {
                AtomicFormula::Literal(Literal {
                    sign: Sign::NoSign,
                    atom,
                }) => {
                    let mut terms = atom.terms;
                    terms.push(Term::Variable(variable.clone()));
                    let atom = Atom {
                        predicate_symbol: atom.predicate_symbol,
                        terms,
                    };
                    formulas.push(AtomicFormula::Literal(Literal {
                        sign: Sign::NoSign,
                        atom,
                    }));
                }
                x => formulas.push(x),
            }
        }
        Body { formulas }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Rule {
    pub head: Head,
    pub body: Body,
}

impl_node!(Rule, Format, RuleParser);

impl Rule {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        if let Some(predicate) = self.head.predicate() {
            predicates.insert(predicate);
        }
        predicates.extend(self.body.predicates());
        predicates
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = self.head.variables();
        vars.extend(self.body.variables());
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = self.head.function_constants();
        functions.extend(self.body.function_constants());
        functions
    }

    pub fn tighten(self, variable: Variable) -> Self {
        match self.head {
            Head::Basic(a) => {
                let mut terms = a.terms;
                let successor = Term::BinaryOperation {
                    op: BinaryOperator::Add,
                    lhs: Term::Variable(variable.clone()).into(),
                    rhs: Term::PrecomputedTerm(PrecomputedTerm::Numeral(1)).into(),
                };
                terms.push(successor);
                let head = Head::Basic(Atom {
                    predicate_symbol: a.predicate_symbol,
                    terms,
                });
                let body = self.body.tighten(variable);
                Rule { head, body }
            }
            Head::Choice(_) => todo!(), // special consideration for {p(X)} :- not q(X).?
            Head::Falsity => self,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Program {
    pub rules: Vec<Rule>,
}

impl_node!(Program, Format, ProgramParser);

impl Program {
    pub fn predicates(&self) -> IndexSet<Predicate> {
        let mut predicates = IndexSet::new();
        for rule in &self.rules {
            predicates.extend(rule.predicates())
        }
        predicates
    }

    pub fn head_predicates(&self) -> IndexSet<Predicate> {
        let mut result = IndexSet::new();
        for rule in &self.rules {
            if let Some(predicate) = rule.head.predicate() {
                result.insert(predicate.clone());
            }
        }
        result
    }

    pub fn variables(&self) -> IndexSet<Variable> {
        let mut vars = IndexSet::new();
        for rule in self.rules.iter() {
            vars.extend(rule.variables())
        }
        vars
    }

    pub fn function_constants(&self) -> IndexSet<String> {
        let mut functions = IndexSet::new();
        for rule in self.rules.iter() {
            functions.extend(rule.function_constants());
        }
        functions
    }

    pub fn tighten(self) -> Self {
        let predicates = self.predicates();
        let fresh_var = self.choose_fresh_variable("N");
        let mut rules: Vec<Rule> = self
            .rules
            .into_iter()
            .map(|r| r.tighten(fresh_var.clone()))
            .collect();
        let forgetting = predicates.into_iter().map(|p| p.forget_successors());
        rules.extend(forgetting);

        Program { rules }
    }

    /// Choose a fresh variable by incrementing `variant`, disjoint from `variables`
    pub fn choose_fresh_variable(&self, variant: &str) -> Variable {
        let mut taken_vars = Vec::<String>::new();
        for var in self.variables() {
            taken_vars.push(var.0.to_string());
        }

        let mut counter = 0;
        let mut candidate: String = variant.to_owned();
        candidate.push_str(&counter.to_string());
        while taken_vars.contains(&candidate) {
            variant.clone_into(&mut candidate);
            counter += 1;
            candidate.push_str(&counter.to_string());
        }

        Variable(candidate)
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{
            Atom, AtomicFormula, Body, Comparison, Head, PrecomputedTerm, Program, Relation, Rule,
            Term, Variable,
        },
        indexmap::IndexSet,
    };

    #[test]
    fn test_program_function_constants() {
        // p :- b != a.
        let program = Program {
            rules: vec![Rule {
                head: Head::Basic(Atom {
                    predicate_symbol: "p".into(),
                    terms: vec![],
                }),
                body: Body {
                    formulas: vec![AtomicFormula::Comparison(Comparison {
                        lhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("a".into())),
                        rhs: Term::PrecomputedTerm(PrecomputedTerm::Symbol("b".into())),
                        relation: Relation::NotEqual,
                    })],
                },
            }],
        };
        assert_eq!(
            program.function_constants(),
            IndexSet::from(["a".into(), "b".into()])
        )
    }

    #[test]
    fn test_choose_fresh_variable() {
        let p: Program = "p(X) :- q(X,N0+1). t :- N < Z.".parse().unwrap();
        let v = Variable("N1".to_string());
        assert_eq!(v, p.choose_fresh_variable("N"))
    }
}
