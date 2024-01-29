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
    },
    Verify {
        #[arg(long, value_enum)]
        with: Verification,

        program: PathBuf,

        specification: PathBuf,

        user_guide: PathBuf,

        lemmas: Option<PathBuf>,

        #[arg(long, default_value_t = 4)]
        cores: u16,

        #[clap(long, short, action)]
        break_equivalences: bool,

        #[clap(long, short, action)]
        parallel: bool,
    },
    VerifyAlt {
        #[arg(long, value_enum)]
        with: Verification,

        directory: PathBuf,

        #[arg(long, default_value_t = 4)]
        cores: u16,

        #[clap(long, short, action)]
        break_equivalences: bool,

        #[clap(long, short, action)]
        parallel: bool,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Translation {
    TauStar,
    Completion,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Verification {
    Default,
    Sequential,
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
