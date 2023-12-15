pub mod convenience;
pub mod formatting;
pub mod parsing;
pub mod proof_search;
pub mod simplifying;
pub mod syntax_tree;
pub mod translating;

use {
    crate::{
        proof_search::{problem, vampire},
        syntax_tree::{asp, fol},
    },
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
    Verify {
        #[arg(long, value_enum)]
        with: Verification,

        program: PathBuf,

        specification: PathBuf,

        user_guide: PathBuf,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Translation {
    TauStar,
    Completion,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Verification {
    Default,
}

fn try_main() -> Result<()> {
    match Cli::parse().command {
        Commands::Translate { with, input } => match with {
            Translation::TauStar => {
                let test: fol::GeneralTerm = "a+1".parse().unwrap();
                let program: asp::Program = read_to_string(&input)
                    .with_context(|| format!("failed to read '{}'", &input.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &input.display()))?;

                let theory = translating::tau_star::tau_star(program);
                println!("{theory}")
            }
            Translation::Completion => {
                let program: asp::Program = read_to_string(&input)
                    .with_context(|| format!("failed to read '{}'", &input.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &input.display()))?;

                let theory = translating::tau_star::tau_star(program);
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
        Commands::Verify {
            with,
            program,
            specification,
            user_guide,
        } => match with {
            Verification::Default => {
                let spec = match specification.extension() {
                    Some(extension) => match extension.to_str() {
                        Some(ext) => match ext {
                            "lp" => {
                                let prog2: asp::Program = read_to_string(&specification)
                                    .with_context(|| {
                                        format!("failed to read '{}'", &specification.display())
                                    })?
                                    .parse()
                                    .with_context(|| {
                                        format!("failed to parse '{}'", &specification.display())
                                    })?;
                                problem::FileType::MiniGringoProgram { program: prog2 }
                            }
                            "spec" => {
                                let specification: fol::Specification =
                                    read_to_string(&specification)
                                        .with_context(|| {
                                            format!("failed to read '{}'", &specification.display())
                                        })?
                                        .parse()
                                        .with_context(|| {
                                            format!(
                                                "failed to parse '{}'",
                                                &specification.display()
                                            )
                                        })?;

                                problem::FileType::FirstOrderSpecification { specification }
                            }
                            _ => {
                                todo!()
                            }
                        },
                        None => todo!(),
                    },
                    None => {
                        todo!()
                    }
                };
                let prog: asp::Program = read_to_string(&program)
                    .with_context(|| format!("failed to read '{}'", &program.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &program.display()))?;

                let ug: fol::Specification = read_to_string(&user_guide)
                    .with_context(|| format!("failed to read '{}'", &user_guide.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &user_guide.display()))?;

                vampire::default_verification(&prog, &spec, &ug);
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
