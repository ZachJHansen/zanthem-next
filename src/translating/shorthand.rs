use crate::syntax_tree::{
    asp::{self, BodyLiteral, Program, Rule},
    fol::{self, Formula, Theory},
};

pub fn translate_term(term: asp::Term) -> fol::GeneralTerm {
    match term {
        asp::Term::PrecomputedTerm(t) => match t {
            asp::PrecomputedTerm::Symbol(s) => {
                fol::GeneralTerm::SymbolicTerm(fol::SymbolicTerm::Symbol(s))
            }
            _ => panic!("unsupported by shorthand translation"),
        },
        asp::Term::Variable(v) => fol::GeneralTerm::Variable(v.0),
        asp::Term::UnaryOperation { .. } | asp::Term::BinaryOperation { .. } => {
            panic!("unsupported by shorthand translation")
        }
    }
}

pub fn translate_atom(atom: asp::Atom) -> Formula {
    let mut terms = Vec::new();
    for term in atom.terms {
        let fol_term = translate_term(term);
        terms.push(fol_term);
    }
    Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: atom.predicate_symbol,
        terms,
    }))
}

pub fn translate_comparison(comparison: asp::Comparison) -> Formula {
    let relation = match comparison.relation {
        asp::Relation::Equal => fol::Relation::Equal,
        asp::Relation::NotEqual => fol::Relation::NotEqual,
        asp::Relation::Less => fol::Relation::Less,
        asp::Relation::LessEqual => fol::Relation::LessEqual,
        asp::Relation::Greater => fol::Relation::Greater,
        asp::Relation::GreaterEqual => fol::Relation::GreaterEqual,
    };
    let guard = fol::Guard {
        relation,
        term: translate_term(comparison.rhs),
    };

    Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: translate_term(comparison.lhs),
        guards: vec![guard],
    }))
}

pub fn body_translate(body: asp::Body) -> Formula {
    let mut atomic_formulas = Vec::new();

    for literal in body.formulas {
        match literal {
            BodyLiteral::ConditionalLiteral(literal) => {
                if literal.basic() {
                    let formula = match literal.head {
                        asp::ConditionalHead::Falsity => {
                            Formula::AtomicFormula(fol::AtomicFormula::Falsity)
                        }
                        asp::ConditionalHead::AtomicFormula(f) => match f {
                            asp::AtomicFormula::Literal(l) => match l.sign {
                                asp::Sign::NoSign => translate_atom(l.atom),
                                asp::Sign::Negation => Formula::UnaryFormula {
                                    connective: fol::UnaryConnective::Negation,
                                    formula: translate_atom(l.atom).into(),
                                },
                                asp::Sign::DoubleNegation => Formula::UnaryFormula {
                                    connective: fol::UnaryConnective::Negation,
                                    formula: Formula::UnaryFormula {
                                        connective: fol::UnaryConnective::Negation,
                                        formula: translate_atom(l.atom).into(),
                                    }
                                    .into(),
                                },
                            },
                            asp::AtomicFormula::Comparison(c) => translate_comparison(c),
                        },
                    };
                    atomic_formulas.push(formula);
                } else {
                    todo!("unimplemented");
                }
            }
            _ => todo!("unimplemented"),
        }
    }

    Formula::conjoin(atomic_formulas)
}

pub fn choice_body_translate(body: asp::Body, head: asp::Atom) -> Formula {
    let body = body_translate(body);
    Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: body.into(),
        rhs: Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: translate_atom(head).into(),
            }
            .into(),
        }
        .into(),
    }
}

pub fn shorthand_rule(rule: Rule) -> Formula {
    let (head, body) = match rule.head {
        asp::Head::Basic(a) => (translate_atom(a), body_translate(rule.body)),
        asp::Head::Choice(a) => (
            translate_atom(a.clone()),
            choice_body_translate(rule.body, a),
        ),
        asp::Head::Falsity => (
            Formula::AtomicFormula(fol::AtomicFormula::Falsity),
            body_translate(rule.body),
        ),
    };

    Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: body.into(),
        rhs: head.into(),
    }
    .universal_closure()
}

// For each rule, H :- B1 & ... & Bn
// produce a formula: forall V ( B1 & ... Bn -> H )
// where V is all variables from the original rule.
pub fn shorthand(p: Program) -> Theory {
    let mut formulas = Vec::new();
    for r in p.rules {
        let rule_translation = shorthand_rule(r);
        let formula = match rule_translation.clone() {
            Formula::BinaryFormula {
                connective: fol::BinaryConnective::Implication,
                lhs,
                rhs,
            } => match *lhs {
                Formula::AtomicFormula(fol::AtomicFormula::Truth) => *rhs,
                _ => rule_translation,
            },
            x => x,
        };
        formulas.push(formula);
    }
    Theory { formulas }
}

#[cfg(test)]
mod tests {
    use super::shorthand;

    #[test]
    fn test_shorthand() {
        for (src, target) in [
            ("a:- b. a :- c.", "b -> a. c -> a."),
            (
                "p(a). p(b). q(X, Y) :- p(X), p(Y).",
                "p(a). p(b). forall X Y (p(X) and p(Y) -> q(X,Y)).",
            ),
            ("p.", "p."),
            ("q :- not p.", "not p -> q."),
            (
                "{q(X)} :- p(X).",
                "forall X (p(X) and not not q(X) -> q(X)).",
            ),
            (":- p.", "p -> #false."),
            ("{p} :- q.", "q and not not p -> p."),
            ("{p}.", "#true and not not p -> p."),
            ("p. q.", "p. q."),
            (
                "{ra(X,a)} :- ta(X). ra(b,a).",
                "forall X ( ta(X) and not not ra(X,a) -> ra(X,a) ). ra(b,a).",
            ),
        ] {
            let left = shorthand(src.parse().unwrap());
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }
}
