use crate::syntax_tree::fol::Theory;

pub fn simplify(theory: Theory) -> Theory {
    crate::simplifying::fol::ht::simplify_shallow(theory)
    // TODO: Add classic simplifications
}
