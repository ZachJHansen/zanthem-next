pub mod external_equivalence;
pub mod strong_equivalence;

use {crate::verifying::problem::Problem, std::fmt::Display};

pub trait Task: Display {
    fn decompose(&self) -> Vec<Problem>;
}