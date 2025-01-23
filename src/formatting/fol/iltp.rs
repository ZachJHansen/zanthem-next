use {
    crate::{
        formatting::{Associativity, Precedence},
        syntax_tree::{
            fol::{
                Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison, Formula,
                FunctionConstant, GeneralTerm, IntegerTerm, Quantification, Quantifier, Relation,
                Sort, SymbolicTerm, UnaryConnective, UnaryOperator, Variable,
            },
            Node,
        },
    },
    std::fmt::{self, Display, Formatter},
};

pub struct Format<'a, N: Node>(pub &'a N);

impl Display for Format<'_, UnaryOperator> {
    fn fmt(&self, _f: &mut Formatter<'_>) -> fmt::Result {
        panic!("unsupported language feature")
    }
}

impl Display for Format<'_, BinaryOperator> {
    fn fmt(&self, _f: &mut Formatter<'_>) -> fmt::Result {
        panic!("unsupported language feature")
    }
}

impl Display for Format<'_, IntegerTerm> {
    fn fmt(&self, _f: &mut Formatter<'_>) -> fmt::Result {
        panic!("unsupported language feature")
    }
}

impl Display for Format<'_, SymbolicTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            SymbolicTerm::Symbol(s) => write!(f, "{s}"),
            _ => panic!("unsupported language feature"),
        }
    }
}

impl Display for Format<'_, GeneralTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            GeneralTerm::SymbolicTerm(t) => write!(f, "{}", Format(t)),
            GeneralTerm::Variable(v) => write!(f, "{v}"),
            _ => panic!("unsupported language feature"),
        }
    }
}

impl Display for Format<'_, Atom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let predicate = &self.0.predicate_symbol;
        let terms = &self.0.terms;

        write!(f, "{predicate}")?;

        if !terms.is_empty() {
            let mut iter = terms.iter().map(Format);
            write!(f, "({}", iter.next().unwrap())?;
            for term in iter {
                write!(f, ", {term}")?;
            }
            write!(f, ")")?;
        }

        Ok(())
    }
}

impl Display for Format<'_, Relation> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Relation::Equal => write!(f, "="),
            Relation::NotEqual => write!(f, "!="),
            Relation::GreaterEqual => write!(f, "p__greater_equal__"),
            Relation::LessEqual => write!(f, "p__less_equal__"),
            Relation::Greater => write!(f, "p__greater__"),
            Relation::Less => write!(f, "p__less__"),
        }
    }
}

impl Display for Format<'_, Comparison> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let guards = &self.0.guards;

        let mut previous_term = &self.0.term;
        for (counter, g) in guards.iter().enumerate() {
            if counter > 0 {
                write!(f, " & ")?;
            }
            match g.relation {
                Relation::Equal | Relation::NotEqual => write!(
                    f,
                    "{} {} {}",
                    Format(previous_term),
                    Format(&g.relation),
                    Format(&g.term)
                ),
                _ => write!(
                    f,
                    "{}({}, {})",
                    Format(&g.relation),
                    Format(previous_term),
                    Format(&g.term)
                ),
            }?;
            previous_term = &g.term;
        }

        Ok(())
    }
}

impl Display for Format<'_, AtomicFormula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            AtomicFormula::Truth => write!(f, "$true"),
            AtomicFormula::Falsity => write!(f, "$false"),
            AtomicFormula::Atom(a) => Format(a).fmt(f),
            AtomicFormula::Comparison(c) => Format(c).fmt(f),
        }
    }
}

impl Display for Format<'_, Quantifier> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Quantifier::Forall => write!(f, "!"),
            Quantifier::Exists => write!(f, "?"),
        }
    }
}

impl Display for Format<'_, FunctionConstant> {
    fn fmt(&self, _f: &mut Formatter<'_>) -> fmt::Result {
        panic!("unsupported language feature")
    }
}

impl Display for Format<'_, Variable> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let sort = &self.0.sort;

        match sort {
            Sort::General => write!(f, "{name}"),
            _ => panic!("unsupported language feature"),
        }
    }
}

impl Display for Format<'_, Quantification> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let variables = &self.0.variables;

        write!(f, "{}[", Format(&self.0.quantifier))?;

        for (counter, var) in variables.iter().enumerate() {
            if counter > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", Format(var))?;
        }

        write!(f, "]")?;

        Ok(())
    }
}

impl Display for Format<'_, UnaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryConnective::Negation => write!(f, "~"),
        }
    }
}

impl Display for Format<'_, BinaryConnective> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryConnective::Equivalence => write!(f, "<=>"),
            BinaryConnective::Implication => write!(f, "=>"),
            BinaryConnective::ReverseImplication => write!(f, "<="),
            BinaryConnective::Conjunction => write!(f, "&"),
            BinaryConnective::Disjunction => write!(f, "|"),
        }
    }
}

impl Precedence for Format<'_, Formula> {
    fn precedence(&self) -> usize {
        match self.0 {
            Formula::AtomicFormula(_) => 0,
            Formula::UnaryFormula { .. } => 1,
            Formula::QuantifiedFormula { .. } => 2,
            Formula::BinaryFormula { .. } => 3,
        }
    }

    fn associativity(&self) -> Associativity {
        Associativity::Left
    }

    fn fmt_operator(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::UnaryFormula { connective, .. } => write!(f, "{}", Format(connective)),
            Formula::BinaryFormula { connective, .. } => write!(f, " {} ", Format(connective)),
            Formula::QuantifiedFormula { quantification, .. } => {
                write!(f, "{}: ", Format(quantification))
            }
            Formula::AtomicFormula(_) => unreachable!(),
        }
    }
}

impl Display for Format<'_, Formula> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            Formula::AtomicFormula(a) => Format(a).fmt(f),
            Formula::UnaryFormula { formula, .. } => self.fmt_unary(Format(formula.as_ref()), f),
            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => {
                // no precedence formatting needed
                let connective = Format(quantification);
                let formula = Format(formula.as_ref());
                write!(f, "{connective}: ({formula})")
            }
            Formula::BinaryFormula { lhs, rhs, .. } => {
                self.fmt_binary(Format(lhs.as_ref()), Format(rhs.as_ref()), f)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        formatting::fol::iltp::Format,
        syntax_tree::fol::{
            Atom, AtomicFormula, BinaryConnective, Formula, GeneralTerm, Quantification,
            Quantifier, Sort, SymbolicTerm, Variable,
        },
    };

    #[test]
    fn format_symbolic_term() {
        assert_eq!(Format(&SymbolicTerm::Symbol("p".into())).to_string(), "p");
    }

    #[test]
    fn format_general_term() {
        assert_eq!(
            Format(&GeneralTerm::Variable("N1".into())).to_string(),
            "N1"
        );
        assert_eq!(
            Format(&GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("p".into()))).to_string(),
            "p"
        );
    }

    #[test]
    fn format_atom() {
        assert_eq!(
            Format(&Atom {
                predicate_symbol: "prime".into(),
                terms: vec![
                    GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("a".to_string())),
                    GeneralTerm::Variable("X".to_string()),
                ]
            })
            .to_string(),
            "prime(a, X)"
        )
    }

    #[test]
    fn format_quantification() {
        assert_eq!(
            Format(&Quantification {
                quantifier: Quantifier::Forall,
                variables: vec![
                    Variable {
                        name: "X1".into(),
                        sort: Sort::General,
                    },
                    Variable {
                        name: "N2".into(),
                        sort: Sort::General,
                    },
                ]
            })
            .to_string(),
            "![X1, N2]"
        );
    }

    #[test]
    fn format_formula() {
        assert_eq!(
            Format(&Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                predicate_symbol: "p".into(),
                terms: vec![]
            })))
            .to_string(),
            "p"
        );
        assert_eq!(
            Format(&Formula::BinaryFormula {
                connective: BinaryConnective::Implication,
                lhs: Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![]
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![]
                    }))
                    .into()
                }
                .into(),
                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                    predicate_symbol: "r".into(),
                    terms: vec![]
                }))
                .into(),
            })
            .to_string(),
            "p => q => r"
        );
        assert_eq!(
            Format(&Formula::QuantifiedFormula {
                quantification: Quantification {
                    quantifier: Quantifier::Forall,
                    variables: vec![
                        Variable {
                            name: "X".into(),
                            sort: Sort::General,
                        },
                        Variable {
                            name: "Y1".into(),
                            sort: Sort::General,
                        },
                    ]
                },
                formula: Formula::BinaryFormula {
                    connective: BinaryConnective::Conjunction,
                    lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    }))
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![],
                    }))
                    .into(),
                }
                .into()
            })
            .to_string(),
            "![X, Y1]: (p & q)"
        );
    }
}
