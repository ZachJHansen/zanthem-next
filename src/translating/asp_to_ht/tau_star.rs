use crate::{
    syntax_tree::{asp, fol},
    translating::asp_to_ht::{
        basics::choose_fresh_global_variables, tau_b_cl::tau_body, val_agc, val_original, Version,
    },
};

// Handles the case when we have a rule with a first-order atom or choice atom in the head
fn tau_star_fo_head_rule(r: &asp::Rule, v: Version, globals: &[String]) -> fol::Formula {
    let fol_head_predicate = fol::Predicate::from(r.head.predicate().unwrap());
    let fvars = &globals[0..r.head.arity()]; // V, |V| = n
    let head_terms = r.head.terms().unwrap(); // Transform p(t) into p(V)

    let mut new_terms = Vec::<fol::GeneralTerm>::new();
    let mut fo_vars = Vec::<fol::Variable>::new();
    for (i, _) in head_terms.iter().enumerate() {
        let fol_var = fol::Variable {
            name: fvars[i].to_string(),
            sort: fol::Sort::General,
        };
        let fol_term = fol::GeneralTerm::Variable(fvars[i].to_string());
        fo_vars.push(fol_var);
        new_terms.push(fol_term);
    }
    let valtz = match v {
        Version::Original => val_original::valtz(head_terms.to_vec(), fo_vars), // val_t(V)
        Version::AbstractGringoCompliant => val_agc::valtz(head_terms.to_vec(), fo_vars),
    };

    let new_head = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: fol_head_predicate.symbol,
        terms: new_terms,
    })); // p(V)
    let core_lhs = fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Conjunction,
        lhs: valtz.into(),
        rhs: tau_body(r.body.clone(), v, r.global_variables()).into(),
    };

    let new_body = match r.head {
        asp::Head::Basic(_) => core_lhs, // val_t(V) & tau^B(Body)
        asp::Head::Choice(_) => fol::Formula::BinaryFormula {
            // val_t(V) & tau^B(Body) & ~~p(V)
            connective: fol::BinaryConnective::Conjunction,
            lhs: core_lhs.into(),
            rhs: fol::Formula::UnaryFormula {
                connective: fol::UnaryConnective::Negation,
                formula: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: new_head.clone().into(),
                }
                .into(),
            }
            .into(),
        },
        _ => unreachable!("only atoms and choice rules are supported in this function constructor"),
    };

    fol::Formula::BinaryFormula {
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    }
    .universal_closure()
    // forall G V ( val_t(V) & tau^B(Body) -> p(V) ) OR forall G V ( val_t(V) & tau^B(Body) -> p(V) )
}

// Handles the case when we have a rule with a propositional atom or choice atom in the head
fn tau_star_prop_head_rule(r: &asp::Rule, v: Version) -> fol::Formula {
    let fol_head_predicate = fol::Predicate::from(r.head.predicate().unwrap());
    let new_head = fol::Formula::AtomicFormula(fol::AtomicFormula::Atom(fol::Atom {
        predicate_symbol: fol_head_predicate.symbol,
        terms: vec![],
    }));
    let core_lhs = tau_body(r.body.clone(), v, r.global_variables());
    let new_body = match &r.head {
        asp::Head::Basic(_) => {
            // tau^B(Body)
            core_lhs
        }
        asp::Head::Choice(_) => {
            // tau^B(Body) & ~~p
            fol::Formula::BinaryFormula {
                connective: fol::BinaryConnective::Conjunction,
                lhs: core_lhs.into(),
                rhs: fol::Formula::UnaryFormula {
                    connective: fol::UnaryConnective::Negation,
                    formula: fol::Formula::UnaryFormula {
                        connective: fol::UnaryConnective::Negation,
                        formula: new_head.clone().into(),
                    }
                    .into(),
                }
                .into(),
            }
        }
        asp::Head::Falsity => {
            unreachable!("a constraint head is not permitted in this formula constructor")
        }
    };

    fol::Formula::BinaryFormula {
        // tau^B(Body) -> p OR tau^B(Body) & ~~p -> p
        connective: fol::BinaryConnective::Implication,
        lhs: new_body.into(),
        rhs: new_head.into(),
    }
    .universal_closure()
    // forall G ( tau^B(Body) -> p ) OR forall G ( tau^B(Body) & ~~p -> p )
}

// Translate a rule using a pre-defined list of global variables
fn tau_star_rule(r: &asp::Rule, v: Version, globals: &[String]) -> fol::Formula {
    match r.head.predicate() {
        Some(_) => {
            if r.head.arity() > 0 {
                // First-order head
                tau_star_fo_head_rule(r, v, globals)
            } else {
                // Propositional head
                tau_star_prop_head_rule(r, v)
            }
        }
        // Handles the case when we have a rule with an empty head
        None => fol::Formula::BinaryFormula {
            connective: fol::BinaryConnective::Implication,
            lhs: tau_body(r.body.clone(), v, r.global_variables()).into(),
            rhs: fol::Formula::AtomicFormula(fol::AtomicFormula::Falsity).into(),
        }
        .universal_closure(),
    }
}

// For each rule, produce a formula: forall G V ( val_t(V) & tau_body(Body) -> p(V) )
// Where G is all variables from the original rule
// and V is the set of fresh variables replacing t within p
pub fn tau_star(p: asp::Program, v: Version) -> fol::Theory {
    let globals = choose_fresh_global_variables(&p);
    let mut formulas: Vec<fol::Formula> = vec![]; // { forall G V ( val_t(V) & tau^B(Body) -> p(V) ), ... }
    for r in p.rules.iter() {
        formulas.push(tau_star_rule(r, v, &globals));
    }
    fol::Theory { formulas }
}

#[cfg(test)]
mod tests {

    use crate::syntax_tree::{asp, fol};

    use super::{tau_star, tau_star_rule, Version};

    #[test]
    fn test_tau_star_rule_original() {
        for (src, target) in [
        (("p(X) :- q(X,Y) : t(Y).", vec!["V".to_string()]), "forall V X (V = X and forall Y (exists Z (Z = Y and t(Z)) -> exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1))) -> p(V))"),
        (("p(X) :- q(X,Y) : t(Y), 1 < X; t(X).", vec!["V".to_string()]), "forall V X (V = X and (forall Y (exists Z (Z = Y and t(Z)) and exists Z Z1 (Z = 1 and Z1 = X and Z < Z1) -> exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1))) and exists Z (Z = X and t(Z))) -> p(V))"),
        (("p(X) :- q(X,Y) : t(Y), 1 < X, t(X).",vec!["V".to_string()]), "forall V X (V = X and (forall Y (exists Z (Z = Y and t(Z)) and exists Z Z1 (Z = 1 and Z1 = X and Z < Z1) and exists Z (Z = X and t(Z)) -> exists Z Z1 (Z = X and Z1 = Y and q(Z, Z1)))) -> p(V))"),
        (("p(X) :- q(X), t(X).",vec!["V".to_string()]), "forall V X (V = X and (exists Z (Z = X and q(Z)) and exists Z (Z = X and t(Z))) -> p(V))"),
        (("p(X) :- q(X); t(X).",vec!["V".to_string()]), "forall V X (V = X and (exists Z (Z = X and q(Z)) and exists Z (Z = X and t(Z))) -> p(V))"),      
        (("p :- q(X).", vec![]), "forall X ( exists Z (Z = X and q(Z)) -> p)"), 
        (("p :- q : t; r.", vec![]), "((t -> q) and r) -> p"),  
        (("p :- q : t, r.", vec![]), "(t and r -> q) -> p"),  
        (("p :- s, q : t, r.", vec![]), "(s and (t and r -> q)) -> p"),
        (("p :- s; q : t, r.", vec![]), "(s and (t and r -> q)) -> p"),
        (("p :- s; not not q : t, not r.", vec![]), "(s and (t and not r -> not not q)) -> p"),
        (
            ("sort(X,Y) :- p(X); p(Y); not p(Z) : p(Z), X < Z, Z < Y.", vec!["V1".to_string(), "V2".to_string()]), 
            "forall V1 V2 X Y ( (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z)) and forall Z ((exists Z1 (Z1 = Z and p(Z1)) and exists Z1 Z2 (Z1 = X and Z2 = Z and Z1 < Z2) and exists Z1 Z2 (Z1 = Z and Z2 = Y and Z1 < Z2)) -> exists Z1 (Z1 = Z and not p(Z1)) ))) -> sort(V1,V2))"
        ),
    ] {
        let rule: asp::Rule = src.0.parse().unwrap();
        let src = fol::Theory { formulas: vec![tau_star_rule(&rule, Version::Original, &src.1)] };
        let target = fol::Theory { formulas: vec![target.parse().unwrap()] };
        assert_eq!(
            src,
            target,
            "{src} != {target}"
        )
    }
    }

    #[test]
    fn test_tau_star_original() {
        for (src, target) in [
        ("a:- b. a :- c.", "b -> a. c -> a."),
        ("p(a). p(b). q(X, Y) :- p(X), p(Y).", "forall V1 (V1 = a and #true -> p(V1)). forall V1 (V1 = b and #true -> p(V1)). forall V1 V2 X Y (V1 = X and V2 = Y and (exists Z (Z = X and p(Z)) and exists Z (Z = Y and p(Z))) -> q(V1,V2))."),
        ("p.", "#true -> p."),
        ("q :- not p.", "not p -> q."),
        ("{q(X)} :- p(X).", "forall V1 X (V1 = X and exists Z (Z = X and p(Z)) and not not q(V1) -> q(V1))."),
        ("{q(V)} :- p(V).", "forall V V1 (V1 = V and exists Z (Z = V and p(Z)) and not not q(V1) -> q(V1))."),
        ("{q(V+1)} :- p(V), not q(X).", "forall V V1 X (exists I$i J$i (V1 = I$i + J$i and I$i = V and J$i = 1) and (exists Z (Z = V and p(Z)) and exists Z (Z = X and not q(Z))) and not not q(V1) -> q(V1))."),
        (":- p(X,3), not q(X,a).", "forall X (exists Z Z1 (Z = X and Z1 = 3 and p(Z,Z1)) and exists Z Z1 (Z = X and Z1 = a and not q(Z,Z1)) -> #false)."),
        (":- p.", "p -> #false."),
        ("{p} :- q.", "q and not not p -> p."),
        ("{p}.", "#true and not not p -> p."),
        ("{p(5)}.", "forall V1 (V1 = 5 and #true and not not p(V1) -> p(V1))."),
        ("p. q.", "#true -> p. #true -> q."),
        ("{ra(X,a)} :- ta(X). ra(5,a).", "forall V1 V2 X (V1 = X and V2 = a and exists Z (Z = X and ta(Z)) and not not ra(V1, V2) -> ra(V1, V2)). forall V1 V2 (V1 = 5 and V2 = a and #true -> ra(V1, V2))."),
        ("p(X/2) :- X=4.", "forall V1 X (exists I$i J$i Q$i R$i (I$i = J$i * Q$i + R$i and (I$i = X and J$i = 2) and (J$i != 0 and R$i >= 0 and R$i < J$i) and V1 = Q$i) and exists Z Z1 (Z = X and Z1 = 4 and Z = Z1) -> p(V1))."),
    ] {
        let left = tau_star(src.parse().unwrap(), Version::Original,);
        let right = target.parse().unwrap();

        assert!(
            left == right,
            "assertion `left == right` failed:\n left:\n{left}\n right:\n{right}"
        );
    }
    }
}
