use {
    clap::{Parser, Subcommand, ValueEnum},
    std::path::PathBuf,
};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
pub struct Arguments {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Debug, Subcommand)]
pub enum Command {
    /// Analyze a property of a given answer set program or first-order theory
    Analyze {
        /// The property to analyze
        #[arg(long, value_enum)]
        property: Property,

        /// The file to analyze
        input: Option<PathBuf>,
    },

    /// Sequentially derive a series of lemmas from a set of assumptions
    Derive {
        /// The proof outline file (lemmas and definitions)
        outline: PathBuf,

        /// The user guide defining placeholders and assumptions
        user_guide: PathBuf,

        /// The decomposition strategy to use
        #[arg(long, value_enum, default_value_t)]
        task_decomposition: TaskDecomposition,

        /// Omit simplifications
        #[arg(long, action)]
        no_simplify: bool,

        /// Omit breaking equivalences
        #[arg(long, action)]
        no_eq_break: bool,

        /// The time limit in seconds to prove each conjecture passed to Vampire
        #[arg(long, short, default_value_t = 30)]
        time_limit: usize,

        /// Omit proof search and just create problem files
        #[arg(long, action)]
        no_proof_search: bool,

        /// The number of prover instances to spawn
        #[arg(long, short = 'n', default_value_t = 1)]
        prover_instances: usize,

        /// The number of threads each prover may use
        #[arg(long, short = 'm', default_value_t = 1)]
        prover_cores: usize,

        /// Omit timing information
        #[arg(long, action)]
        no_timing: bool,

        /// The destination directory for the problem files
        #[arg(long)]
        out_dir: Option<PathBuf>,
    },

    /// Simplify a first-order theory
    Simplify {
        /// The translation to use
        #[arg(long, value_enum, default_value_t)]
        with: Simplification,

        /// The file to translate
        input: Option<PathBuf>,
    },

    /// Translate a given answer set program or first-order theory
    Translate {
        /// The translation to use
        #[arg(long, value_enum)]
        with: Translation,

        /// The file to translate
        input: Option<PathBuf>,
    },

    /// Create and optionally verify a set of problem files from a claim about answer set programs or first-order theories
    Verify {
        /// The equivalence theory used to proof the claim
        #[arg(long, value_enum)]
        equivalence: Equivalence,

        /// The ASP-to-HT translation to use
        #[arg(long, value_enum)]
        formula_representation: FormulaRepresentation,

        /// The decomposition strategy to use
        #[arg(long, value_enum, default_value_t)]
        task_decomposition: TaskDecomposition,

        /// The direction of the proof
        #[arg(long, value_enum, default_value_t)]
        direction: Direction,

        /// Bypass the tightness checks during verification of external equivalence
        #[arg(long, action)]
        bypass_tightness: bool,

        /// Omit simplifications
        #[arg(long, action)]
        no_simplify: bool,

        /// Omit breaking equivalences
        #[arg(long, action)]
        no_eq_break: bool,

        /// Omit proof search and just create problem files
        #[arg(long, action)]
        no_proof_search: bool,

        /// Omit display of system runtimes
        #[arg(long, action)]
        no_timing: bool,

        /// The time limit in seconds to prove each problem passed to a prover
        #[arg(long, short, default_value_t = 60)]
        time_limit: usize,

        /// The number of prover instances to spawn
        #[arg(long, short = 'n', default_value_t = 1)]
        prover_instances: usize,

        /// The number of threads each prover may use
        #[arg(long, short = 'm', default_value_t = 1)]
        prover_cores: usize,

        /// The destination directory for the problem files
        #[arg(long)]
        save_problems: Option<PathBuf>,

        /// A set of files from which to construct the claim, including
        ///
        ///   - a specification of intended behavior,
        ///   - a program about which the claim is constructed, and
        ///   - additional knowledge used to construct the claim (e.g., user guide, proof outline).
        #[arg(verbatim_doc_comment)]
        files: Vec<PathBuf>,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Property {
    Tightness,
    CnfPdg,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Simplification {
    #[default]
    CompleteHT,
    ShallowHT,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Translation {
    Completion,
    Gamma,
    TauStarV1,
    TauStarV2,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum FormulaRepresentation {
    TauStarV1,
    TauStarV2,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Equivalence {
    Strong,
    External,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum TaskDecomposition {
    #[default]
    Independent,
    Sequential,
}

pub use crate::syntax_tree::fol::Direction;

#[cfg(test)]
mod tests {
    use super::Arguments;

    #[test]
    fn verify() {
        use clap::CommandFactory as _;
        Arguments::command().debug_assert()
    }
}
