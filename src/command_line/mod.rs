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
    /// Translate a given answer set program or first-order theory
    Translate {
        /// The translation to use
        #[arg(long, value_enum)]
        with: Translation,

        /// The file to translate
        input: PathBuf,

        /// Simplify
        #[clap(long, short, action)]
        simplify: bool,
    },
    Verify {
        #[arg(long, value_enum, default_value_t = Verification::Sequential)]
        with: Verification,

        specification: PathBuf,

        program: PathBuf,

        user_guide: PathBuf,

        lemmas: Option<PathBuf>,

        #[arg(long, value_enum, default_value_t = Direction::Both)]
        direction: Direction,

        #[arg(long, default_value_t = 4)]
        cores: u16,

        #[clap(long, action)]
        no_break: bool,

        #[clap(long, short, action)]
        parallel: bool,

        #[clap(long,  action)]
        no_simplify: bool,
    },
    VerifyAlt {
        #[arg(long, value_enum, default_value_t = Verification::Sequential)]
        with: Verification,

        directory: PathBuf,

        #[arg(long, value_enum, default_value_t = Direction::Both)]
        direction: Direction,

        #[arg(long, default_value_t = 4)]
        cores: u16,

        #[clap(long, action)]
        no_break: bool,

        #[clap(long, short, action)]
        parallel: bool,

        #[clap(long, action)]
        no_simplify: bool,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Translation {
    Gamma,
    TauStar,
    Completion,
    Simplify,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Verification {
    Default,
    Sequential,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Direction {
    Forward,
    Backward,
    Both,
}

#[cfg(test)]
mod tests {
    use super::Arguments;

    #[test]
    fn verify() {
        use clap::CommandFactory as _;
        Arguments::command().debug_assert()
    }
}
