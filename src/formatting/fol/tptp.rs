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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            UnaryOperator::Negative => write!(f, "$uminus"),
        }
    }
}

impl Display for Format<'_, BinaryOperator> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            BinaryOperator::Add => write!(f, "$sum"),
            BinaryOperator::Subtract => write!(f, "$difference"),
            BinaryOperator::Multiply => write!(f, "$product"),
        }
    }
}

impl Display for Format<'_, IntegerTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            IntegerTerm::Numeral(n) => {
                if *n < 0 {
                    let m = n.abs();
                    write!(f, "$uminus({m})")?;
                } else {
                    write!(f, "{n}")?;
                }

                Ok(())
            }
            IntegerTerm::Variable(v) => write!(f, "{v}$i"),
            IntegerTerm::FunctionConstant(c) => write!(f, "{c}$i"),
            IntegerTerm::UnaryOperation { op, arg } => {
                let op = Format(op);
                let arg = Format(arg.as_ref());
                write!(f, "{op}({arg})")
            }
            IntegerTerm::BinaryOperation { op, lhs, rhs } => {
                let op = Format(op);
                let lhs = Format(lhs.as_ref());
                let rhs = Format(rhs.as_ref());
                write!(f, "{op}({lhs}, {rhs})")
            }
        }
    }
}

impl Display for Format<'_, SymbolicTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            SymbolicTerm::Symbol(s) => write!(f, "{s}"),
            SymbolicTerm::FunctionConstant(c) => write!(f, "{c}$s"),
            SymbolicTerm::Variable(v) => write!(f, "{v}$s"),
        }
    }
}

impl Display for Format<'_, GeneralTerm> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self.0 {
            GeneralTerm::Infimum => write!(f, "infimum"),
            GeneralTerm::Supremum => write!(f, "supremum"),
            GeneralTerm::FunctionConstant(c) => write!(f, "{c}$g"),
            GeneralTerm::Variable(v) => write!(f, "{v}"),
            GeneralTerm::IntegerTerm(t) => write!(f, "{}", Format(t)),
            GeneralTerm::SymbolicTerm(t) => write!(f, "{}", Format(t)),
        }
    }
}

fn cast_term(term: &GeneralTerm, needs_cast: bool) -> String {
    // only integer terms have to be cast
    match (matches!(term, GeneralTerm::IntegerTerm(_)) & needs_cast) {
        true => format!("to_general({})", Format(term)),
        false => format!("{}", Format(term)),
    }
}

impl Display for Format<'_, Atom> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let predicate = &self.0.predicate_symbol;
        let terms = &self.0.terms;

        write!(f, "{predicate}")?;

        if !terms.is_empty() {
            write!(f, "(")?;
            for (counter, t) in terms.iter().enumerate() {
                let term = cast_term(t, true);
                if counter == 0 {
                    write!(f, "{term}")?
                } else {
                    write!(f, ", {term}")?
                }
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
            Relation::GreaterEqual => write!(f, "greatereq"),
            Relation::LessEqual => write!(f, "lesseq"),
            Relation::Greater => write!(f, "greater"),
            Relation::Less => write!(f, "less"),
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

            // check if left and right term are ints
            let left_is_int = matches!(previous_term, GeneralTerm::IntegerTerm(_));
            let right_is_int = matches!(g.term, GeneralTerm::IntegerTerm(_));
            // if the types don't match a cast is necessary
            let needs_cast = left_is_int != right_is_int;
            // if both are ints using the integer comparison in necessary
            let needs_int_comparison = left_is_int & right_is_int;

            // cast terms if needed
            let lhs_string = cast_term(previous_term, needs_cast);
            let rhs_string = cast_term(&g.term, needs_cast);

            match g.relation {
                Relation::Equal | Relation::NotEqual => {
                    write!(f, "{} {} {}", lhs_string, Format(&g.relation), rhs_string)
                }
                // for other relations need to use the correct version (int or general)
                _ => match needs_int_comparison {
                    true => write!(
                        f,
                        "${}({}, {})",
                        Format(&g.relation),
                        lhs_string,
                        rhs_string
                    ),
                    false => write!(f, "{}({}, {})", Format(&g.relation), lhs_string, rhs_string),
                },
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
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let sort = &self.0.sort;

        match sort {
            Sort::General => write!(f, "{name}$g"),
            Sort::Integer => write!(f, "{name}$i"),
            Sort::Symbol => write!(f, "{name}$s"),
        }
    }
}

impl Display for Format<'_, Variable> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let sort = &self.0.sort;

        match sort {
            Sort::General => write!(f, "{name}"),
            Sort::Integer => write!(f, "{name}$i"),
            Sort::Symbol => write!(f, "{name}$s"),
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
            match var.sort {
                Sort::General => write!(f, "{}: general", Format(var)),
                Sort::Integer => write!(f, "{}: $int", Format(var)),
                Sort::Symbol => write!(f, "{}: symbol", Format(var)),
            }?;
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
        formatting::fol::tptp::Format,
        syntax_tree::fol::{
            Atom, AtomicFormula, BinaryConnective, BinaryOperator, Comparison, Formula,
            GeneralTerm, Guard, IntegerTerm, Quantification, Quantifier, Relation, Sort,
            SymbolicTerm, UnaryOperator, Variable,
        },
    };

    #[test]
    fn format_integer_term() {
        assert_eq!(Format(&IntegerTerm::Numeral(0)).to_string(), "0");
        assert_eq!(Format(&IntegerTerm::Numeral(42)).to_string(), "42");
        assert_eq!(
            Format(&IntegerTerm::Numeral(-42)).to_string(),
            "$uminus(42)"
        );
        assert_eq!(
            Format(&IntegerTerm::Variable("A".into())).to_string(),
            "A$i"
        );
        assert_eq!(
            Format(&IntegerTerm::BinaryOperation {
                op: BinaryOperator::Multiply,
                lhs: IntegerTerm::Numeral(1).into(),
                rhs: IntegerTerm::Numeral(5).into(),
            })
            .to_string(),
            "$product(1, 5)"
        );
        assert_eq!(
            Format(&IntegerTerm::BinaryOperation {
                op: BinaryOperator::Add,
                lhs: IntegerTerm::Numeral(10).into(),
                rhs: IntegerTerm::Variable("N".into()).into(),
            })
            .to_string(),
            "$sum(10, N$i)"
        );
        assert_eq!(
            Format(&IntegerTerm::BinaryOperation {
                op: BinaryOperator::Subtract,
                lhs: IntegerTerm::Numeral(-195).into(),
                rhs: IntegerTerm::UnaryOperation {
                    op: UnaryOperator::Negative,
                    arg: IntegerTerm::Variable("N".into()).into(),
                }
                .into(),
            })
            .to_string(),
            "$difference($uminus(195), $uminus(N$i))"
        );
    }

    #[test]
    fn format_symbolic_term() {
        assert_eq!(Format(&SymbolicTerm::Symbol("p".into())).to_string(), "p");
        assert_eq!(
            Format(&SymbolicTerm::Variable("X".into())).to_string(),
            "X$s"
        )
    }

    #[test]
    fn format_general_term() {
        assert_eq!(Format(&GeneralTerm::Infimum).to_string(), "infimum");
        assert_eq!(Format(&GeneralTerm::Supremum).to_string(), "supremum");
        assert_eq!(
            Format(&GeneralTerm::Variable("N1".into())).to_string(),
            "N1"
        );
        assert_eq!(
            Format(&GeneralTerm::SymbolicTerm(SymbolicTerm::Symbol("p".into()))).to_string(),
            "p"
        );
        assert_eq!(
            Format(&GeneralTerm::IntegerTerm(IntegerTerm::Numeral(1))).to_string(),
            "1"
        )
    }

    #[test]
    fn format_atom() {
        assert_eq!(
            Format(&Atom {
                predicate_symbol: "prime".into(),
                terms: vec![
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::Variable("N1".into()).into(),
                        rhs: IntegerTerm::Numeral(3).into(),
                    }),
                    GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                ]
            })
            .to_string(),
            "prime(to_general($sum(N1$i, 3)), to_general(5))"
        )
    }

    #[test]
    fn format_comparison() {
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![Guard {
                    relation: Relation::Equal,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                }]
            })
            .to_string(),
            "5 = 3"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![Guard {
                    relation: Relation::NotEqual,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                }]
            })
            .to_string(),
            "5 != 3"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![Guard {
                    relation: Relation::LessEqual,
                    term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                }]
            })
            .to_string(),
            "$lesseq(5, 3)"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![
                    Guard {
                        relation: Relation::LessEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                    },
                    Guard {
                        relation: Relation::Equal,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(4)),
                    }
                ]
            })
            .to_string(),
            "$lesseq(5, 3) & 3 = 4"
        );
        assert_eq!(
            Format(&Comparison {
                term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                guards: vec![
                    Guard {
                        relation: Relation::LessEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(3)),
                    },
                    Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(6)),
                    },
                    Guard {
                        relation: Relation::NotEqual,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::Numeral(5)),
                    }
                ]
            })
            .to_string(),
            "$lesseq(5, 3) & $less(3, 6) & 6 != 5"
        );
    }

    #[test]
    fn format_quantification() {
        assert_eq!(
            Format(&Quantification {
                quantifier: Quantifier::Forall,
                variables: vec![
                    Variable {
                        name: "X1".into(),
                        sort: Sort::Integer,
                    },
                    Variable {
                        name: "N2".into(),
                        sort: Sort::General,
                    },
                ]
            })
            .to_string(),
            "![X1$i: $int, N2: general]"
        );
        assert_eq!(
            Format(&Quantification {
                quantifier: Quantifier::Exists,
                variables: vec![Variable {
                    name: "X1".into(),
                    sort: Sort::Symbol,
                },]
            })
            .to_string(),
            "?[X1$s: symbol]"
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
                            sort: Sort::Integer,
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
            "![X$i: $int, Y1: general]: (p & q)"
        );
    }
}
