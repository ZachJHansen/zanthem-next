use crate::syntax_tree::fol::Formula;

pub trait Apply {
    fn apply(self, f: &mut impl FnMut(Self) -> Self) -> Self
    where
        Self: Sized;
}

impl Apply for Formula {
    fn apply(self, f: &mut impl FnMut(Self) -> Self) -> Self
    where
        Self: Sized,
    {
        let inner = match self {
            x @ Formula::AtomicFormula(_) => x,

            Formula::UnaryFormula {
                connective,
                formula,
            } => Formula::UnaryFormula {
                connective,
                formula: formula.apply(f).into(),
            },

            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => Formula::BinaryFormula {
                connective,
                lhs: lhs.apply(f).into(),
                rhs: rhs.apply(f).into(),
            },

            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => Formula::QuantifiedFormula {
                quantification,
                formula: formula.apply(f).into(),
            },
        };
        f(inner)
    }
}

pub trait ApplyCount {
    fn apply_count(self, f: &mut impl FnMut(Self, usize) -> (Self, usize)) -> (Self, usize)
    where
        Self: Sized;
}

impl ApplyCount for Formula {
    fn apply_count(self, f: &mut impl FnMut(Self, usize) -> (Self, usize)) -> (Self, usize)
    where
        Self: Sized,
    {
        let mut count = 0;
        let inner = match self {
            x @ Formula::AtomicFormula(_) => x,

            Formula::UnaryFormula {
                connective,
                formula,
            } => {
                let result = formula.apply_count(f);
                count = count + result.1;
                Formula::UnaryFormula {
                    connective,
                    formula: result.0.into(),
                }
            }

            Formula::BinaryFormula {
                connective,
                lhs,
                rhs,
            } => {
                let result1 = lhs.apply_count(f);
                count = count + result1.1;
                let result2 = rhs.apply_count(f);
                count = count + result2.1;
                Formula::BinaryFormula {
                    connective,
                    lhs: result1.0.into(),
                    rhs: result2.0.into(),
                }
            }

            Formula::QuantifiedFormula {
                quantification,
                formula,
            } => {
                let result = formula.apply_count(f);
                count = count + result.1;
                Formula::QuantifiedFormula {
                    quantification,
                    formula: result.0.into(),
                }
            }
        };
        f(inner, count)
    }
}
