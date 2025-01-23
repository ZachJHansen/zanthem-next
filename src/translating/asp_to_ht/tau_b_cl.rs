use crate::{
    syntax_tree::{
        asp::{self, ConditionalHead},
        fol::{self, Guard},
    },
    translating::asp_to_ht::basics::choose_fresh_variable_names,
};

use super::{val_agc, val_original, Version};

use indexmap::IndexSet;

// Translate a first-order body literal
fn tau_b_first_order_literal(
    l: asp::Literal,
    v: Version,
    taken_vars: &mut IndexSet<fol::Variable>,
) -> fol::Formula {
    let atom = l.atom;
    let terms = atom.terms;
    let arity = terms.len();
    let varnames = choose_fresh_variable_names(taken_vars, "Z", arity);

    // Compute val_t1(Z1) & val_t2(Z2) & ... & val_tk(Zk)
    let mut var_terms: Vec<fol::GeneralTerm> = Vec::with_capacity(arity);
    let mut var_vars: Vec<fol::Variable> = Vec::with_capacity(arity);
    let mut valtz_vec: Vec<fol::Formula> = Vec::with_capacity(arity);
    for (i, t) in terms.iter().enumerate() {
        let var = fol::Variable {
            sort: fol::Sort::General,
            name: varnames[i].clone(),
        };
        var_terms.push(fol::GeneralTerm::Variable(varnames[i].clone()));
        var_vars.push(var.clone());
        match v {
            Version::Original => valtz_vec.push(val_original::val(t.clone(), var)),
            Version::AbstractGringoCompliant => {
                valtz_vec.push(val_agc::val(t.clone(), var, taken_vars.clone()))
            }
        }
    }
    let valtz = fol::Formula::conjoin(valtz_vec);

    // Compute p(Z1, Z2, ..., Zk)
    let p_zk = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: atom.predicate_symbol,
        terms: var_terms,
    }));

    // Compute tau^b(B)
    match l.sign {
        asp::Sign::NoSign => fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Exists,
                variables: var_vars,
            },
            formula: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: valtz.into(),
                rhs: p_zk.into(),
            }
            .into(),
        },
        asp::Sign::Negation => fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Exists,
                variables: var_vars,
            },
            formula: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: valtz.into(),
                rhs: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: p_zk.into(),
                }
                .into(),
            }
            .into(),
        },
        asp::Sign::DoubleNegation => fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Exists,
                variables: var_vars,
            },
            formula: fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: valtz.into(),
                rhs: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: fol::Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: p_zk.into(),
                    }
                    .into(),
                }
                .into(),
            }
            .into(),
        },
    }
}

// Translate a propositional body literal
fn tau_b_propositional_literal(l: asp::Literal) -> fol::Formula {
    let atom = l.atom;
    match l.sign {
        asp::Sign::NoSign => fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
            predicate_symbol: atom.predicate_symbol,

            terms: vec![],
        })),
        asp::Sign::Negation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                predicate_symbol: atom.predicate_symbol,
                terms: vec![],
            }))
            .into(),
        },
        asp::Sign::DoubleNegation => fol::Formula::UnaryFormula {
            connective: fol::UnaryConnective::Negation,
            formula: fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
                    predicate_symbol: atom.predicate_symbol,
                    terms: vec![],
                }))
                .into(),
            }
            .into(),
        },
    }
}

// Translate a body comparison
fn tau_b_comparison(
    c: asp::Comparison,
    v: Version,
    taken_vars: &mut IndexSet<fol::Variable>,
) -> fol::Formula {
    let varnames = choose_fresh_variable_names(taken_vars, "Z", 2);

    // Compute val_t1(Z1) & val_t2(Z2)
    let term_z1 = fol::GeneralTerm::Variable(varnames[0].clone());
    let term_z2 = fol::GeneralTerm::Variable(varnames[1].clone());
    let var_z1 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[0].clone(),
    };
    let var_z2 = fol::Variable {
        sort: fol::Sort::General,
        name: varnames[1].clone(),
    };

    let valtz = match v {
        Version::Original => fol::Formula::conjoin(vec![
            val_original::val(c.lhs, var_z1.clone()),
            val_original::val(c.rhs, var_z2.clone()),
        ]),
        Version::AbstractGringoCompliant => fol::Formula::conjoin(vec![
            val_agc::val(c.lhs, var_z1.clone(), taken_vars.clone()),
            val_agc::val(c.rhs, var_z2.clone(), taken_vars.clone()),
        ]),
    };

    // Compute Z1 rel Z2
    let z1_rel_z2 = fol::Formula::AtomicFormula(fol::AtomicFormula::Comparison(fol::Comparison {
        term: term_z1,
        guards: vec![Guard {
            relation: fol::Relation::from(c.relation),
            term: term_z2,
        }],
    }));

    fol::Formula::QuantifiedFormula {
        quantification: fol::Quantification {
            quantifier: fol::Quantifier::Exists,
            variables: vec![var_z1, var_z2],
        },
        formula: fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Conjunction,
            lhs: valtz.into(),
            rhs: z1_rel_z2.into(),
        }
        .into(),
    }
}

// Translate a body literal or comparison
fn tau_b(f: asp::AtomicFormula, v: Version) -> fol::Formula {
    let mut taken_vars = IndexSet::<fol::Variable>::new();
    for var in f.variables().iter() {
        taken_vars.insert(fol::Variable {
            name: var.to_string(),
            sort: fol::Sort::General,
        });
    }
    match f {
        asp::AtomicFormula::Literal(l) => {
            let arity = l.atom.terms.len();
            if arity > 0 {
                tau_b_first_order_literal(l, v, &mut taken_vars)
            } else {
                tau_b_propositional_literal(l)
            }
        }
        asp::AtomicFormula::Comparison(c) => tau_b_comparison(c, v, &mut taken_vars),
    }
}

// Translate a conditional literal l with global variables z
fn tau_b_cl(l: asp::ConditionalLiteral, v: Version, z: &IndexSet<asp::Variable>) -> fol::Formula {
    let head = l.head;
    let conditions = l.conditions.formulas;

    let mut local_vars = head.variables();
    local_vars.retain(|v| !z.contains(v));

    let consequent = match head {
        ConditionalHead::AtomicFormula(a) => tau_b(a.clone(), v),
        ConditionalHead::Falsity => fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity),
    };

    let mut formulas = vec![];
    for c in conditions.iter() {
        formulas.push(tau_b(c.clone(), v));
    }
    let antecedent = fol::Formula::conjoin(formulas);

    let inner_formula = match antecedent {
        fol::Formula::AtomicFormula(fol::AtomicFormula::Truth) => consequent,
        _ => fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: antecedent.into(),
            rhs: consequent.into(),
        },
    };

    if local_vars.is_empty() {
        inner_formula
    } else {
        let mut variables = vec![];
        for v in local_vars.iter() {
            variables.push(fol::Variable {
                name: v.0.clone(),
                sort: fol::Sort::General,
            });
        }
        fol::Formula::QuantifiedFormula {
            quantification: fol::Quantification {
                quantifier: fol::Quantifier::Forall,
                variables,
            },
            formula: inner_formula.into(),
        }
    }
}

// Translate a rule body
pub(crate) fn tau_body(b: asp::Body, v: Version, z: IndexSet<asp::Variable>) -> fol::Formula {
    let mut formulas = Vec::<fol::Formula>::new();
    for f in b.formulas.iter() {
        formulas.push(tau_b_cl(f.clone(), v, &z));
    }
    fol::Formula::conjoin(formulas)
}

#[cfg(test)]
mod tests {
    use indexmap::IndexSet;

    use super::{tau_b, tau_b_cl};
    use crate::{syntax_tree::asp, translating::asp_to_ht::Version};

    #[test]
    fn test_tau_b_original() {
        for (src, target) in [
        ("p(t)", "exists Z (Z = t and p(Z))"),
        ("not p(t)", "exists Z (Z = t and not p(Z))"),
        ("X < 1..5", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and Z < Z1)"),
        ("not not p(t)", "exists Z (Z = t and not not p(Z))"),
        ("not not x", "not not x"),
        ("not p(X,5)", "exists Z Z1 (Z = X and Z1 = 5 and not p(Z,Z1))"),
        ("not p(X,0-5)", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and J$i = 5) and not p(Z,Z1))"),
        ("p(X,-1..5)", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = -1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and p(Z,Z1))"),
        ("p(X,-(1..5))", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and exists I$i J1$i K$i (I$i = 1 and J1$i = 5  and J$i = K$i and I$i <= K$i <= J1$i)) and p(Z,Z1))"),
        ("p(1/0)", "exists Z (exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = 1 and J$i = 0) and (J$i != 0 and R$i >= 0 and R$i < J$i) and Z$g = Q$i) and p(Z))"),
    ] {
        let left = tau_b(src.parse().unwrap(), Version::Original);
        let right = target.parse().unwrap();

        assert!(
            left == right,
            "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
        );
    }
    }

    #[test]
    fn test_tau_b_agc() {
        for (src, target) in [
            ("p(t)", "exists Z (Z = t and p(Z))"),
            ("not p(t)", "exists Z (Z = t and not p(Z))"),
            ("X < 1..5", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = 1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and Z < Z1)"),
            ("not not p(t)", "exists Z (Z = t and not not p(Z))"),
            ("not not x", "not not x"),
            ("not p(X,5)", "exists Z Z1 (Z = X and Z1 = 5 and not p(Z,Z1))"),
            ("not p(X,0-5)", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and J$i = 5) and not p(Z,Z1))"),
            ("p(X,-1..5)", "exists Z Z1 (Z = X and exists I$i J$i K$i (I$i = -1 and J$i = 5 and Z1 = K$i and I$i <= K$i <= J$i) and p(Z,Z1))"),
            ("p(X,-(1..5))", "exists Z Z1 (Z = X and exists I$i J$i (Z1 = I$i - J$i and I$i = 0 and exists I1$i J1$i K1$i (I1$i = 1 and J1$i = 5  and J$i = K1$i and I1$i <= K1$i <= J1$i)) and p(Z,Z1))"),
            ("p(1/0)", "exists Z (exists I$i J$i K$i (I$i = 1 and J$i = 0 and (K$i * |J$i| <= |I$i| < (K$i+1) * |J$i|) and ((I$i * J$i >= 0 and Z = K$i) or (I$i*J$i < 0 and Z = -K$i)) ) and p(Z))"),
        ] {
            let left = tau_b(src.parse().unwrap(), Version::AbstractGringoCompliant);
            let right = target.parse().unwrap();

            assert!(
                left == right,
                "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
            );
        }
    }

    #[test]
    fn test_tau_b_cl_original() {
        for (src, target) in [
            (("q(X)", IndexSet::from_iter(vec![asp::Variable("X".to_string())])), "exists Z (Z = X and q(Z))"),
            (("not asg(V,I) : color(I)", IndexSet::from_iter(vec![asp::Variable("V".to_string())])), "forall I (exists Z (Z = I and color(Z)) -> exists Z Z1 (Z = V and Z1 = I and not asg(Z, Z1)))"),
            (("#false : p(X,Y), q(Y)", IndexSet::from_iter(vec![asp::Variable("X".to_string()), asp::Variable("Y".to_string()),])), "(exists Z Z1 (Z = X and Z1 = Y and p(Z,Z1)) and exists Z (Z = Y and q(Z))) -> #false"),
        ] {
            let src = tau_b_cl(src.0.parse().unwrap(), Version::Original, &src.1);
            let target = target.parse().unwrap();
            assert_eq!(
                src,
                target,
                "{src} != {target}"
            )
        }

        for (src, target) in [
            (("p(X,Y) : not q(X/Y)", IndexSet::from_iter(vec![asp::Variable("X".to_string())])), "forall Y (exists Z (exists I$i J$i K$i (I$i = X and J$i = Y and (K$i * |J$i| <= |I$i| < (K$i+1) * |J$i|) and ((I$i * J$i >= 0 and Z = K$i) or (I$i*J$i < 0 and Z = -K$i)) ) and not q(Z)) -> exists Z Z1 (Z = X and Z1 = Y and p(Z, Z1)))"),
        ] {
            let src = tau_b_cl(src.0.parse().unwrap(), Version::AbstractGringoCompliant, &src.1);
            let target = target.parse().unwrap();
            assert_eq!(
                src,
                target,
                "{src} != {target}"
            )
        }
    }
}
