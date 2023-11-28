pub mod convenience;
pub mod simplifying;
pub mod formatting;
pub mod parsing;
pub mod syntax_tree;
pub mod translating;

use {
    crate::syntax_tree::{asp, fol},
    anyhow::{Context, Error, Result},
    clap::{Parser, Subcommand, ValueEnum},
    std::{fs::read_to_string, path::PathBuf},
};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    Translate {
        #[arg(long, value_enum)]
        with: Translation,

        input: PathBuf,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Translation {
    TauStar,
    Completion,
}

fn try_main() -> Result<()> {
    match Cli::parse().command {
        Commands::Translate { with, input } => match with {
            Translation::TauStar => {
                let program: asp::Program = read_to_string(&input)
                    .with_context(|| format!("failed to read '{}'", &input.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &input.display()))?;

                let theory = translating::tau_star::tau_star_program(program);
                println!("{theory}")
            }
            Translation::Completion => {
                let program: asp::Program = read_to_string(&input)
                    .with_context(|| format!("failed to read '{}'", &input.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &input.display()))?;

                let theory = translating::tau_star::tau_star_program(program);
                match translating::completion::completion(&theory) {
                    Some(completion) => {
                        println!("{completion}")
                    }
                    None => {
                        println!("Not a completable theory.")
                    }
                }
            }
        },
    }
    Ok(())
}

fn main() {
    if let Err(err) = try_main() {
        handle_error(err);
    }
}

fn handle_error(err: Error) {
    eprintln!("error: {:?}", err);
}