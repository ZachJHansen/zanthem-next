pub mod apply;
pub mod unbox;

use {crate::syntax_tree::fol, std::collections::HashSet};

/// True if v1 is subsorteq to v2 and False otherwise
pub fn subsort(v1: &fol::Variable, v2: &fol::Variable) -> bool {
    match v1.sort {
        fol::Sort::General => {
            match v2.sort {
                fol::Sort::General => true,
                fol::Sort::Integer => false,
            }
        },
        fol::Sort::Integer => {
            match v2.sort {
                fol::Sort::General => true,
                fol::Sort::Integer => true,
            }
        },
    }
}

/// Choose `arity` variable names by incrementing `variant`, disjoint from `variables`
pub fn choose_fresh_variable_names(
    variables: &HashSet<fol::Variable>,
    variant: &str,
    arity: usize,
) -> Vec<String> {
    let mut taken_vars = Vec::<String>::new();
    for var in variables.iter() {
        taken_vars.push(var.name.to_string());
    }
    let mut fresh_vars = Vec::<String>::new();
    let arity_bound = match taken_vars.contains(&variant.to_string()) {
        true => arity + 1,
        false => {
            fresh_vars.push(variant.to_string());
            arity
        }
    };
    for n in 1..arity_bound {
        let mut candidate: String = variant.to_owned();
        let number: &str = &n.to_string();
        candidate.push_str(number);
        let mut m = n;
        while taken_vars.contains(&candidate) || fresh_vars.contains(&candidate) {
            candidate = variant.to_owned();
            m += 1;
            let number = &m.to_string();
            candidate.push_str(number);
        }
        fresh_vars.push(candidate.to_string());
    }
    fresh_vars
}
