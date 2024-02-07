pub mod command_line;
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

        #[clap(long, short, action)]
        simplify: bool,
    },
    Verify {
        #[arg(long, value_enum)]
        with: Verification,

        program: PathBuf,

        specification: PathBuf,

        user_guide: PathBuf,

        lemmas: Option<PathBuf>,

        #[clap(long, short, action)]
        simplify: bool,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Translation {
    TauStar,
    Completion,
    Test,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Verification {
    Default,
    Sequential,
}

fn try_main() -> Result<()> {
    match Cli::parse().command {
        Commands::Translate {
            with,
            input,
            simplify,
        } => match with {
            Translation::TauStar => {
                let program: asp::Program = read_to_string(&input)
                    .with_context(|| format!("failed to read '{}'", &input.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &input.display()))?;

                let theory = if simplify {
                    simplifying::fol::ht::simplify_theory(translating::tau_star::tau_star(program))
                } else {
                    translating::tau_star::tau_star(program)
                };
                println!("{theory}")
            }
            Translation::Test => {
                let theory: fol::Formula = read_to_string(&input)
                    .with_context(|| format!("failed to read '{}'", &input.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &input.display()))?;

                let simplified = simplifying::fol::ht::simplify(theory);
                println!("{simplified}");
            }
            Translation::Completion => {
                let program: asp::Program = read_to_string(&input)
                    .with_context(|| format!("failed to read '{}'", &input.display()))?
                    .parse()
                    .with_context(|| format!("failed to parse '{}'", &input.display()))?;

                let theory = translating::tau_star::tau_star(program);
                match translating::completion::completion(&theory) {
                    Some(completion) => {
                        let theory = if simplify {
                            simplifying::fol::ht::simplify_theory(completion)
                        } else {
                            completion
                        };
                        println!("{theory}")
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
            lemmas,
            simplify,
        } => {
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
                            let specification: fol::Specification = read_to_string(&specification)
                                .with_context(|| {
                                    format!("failed to read '{}'", &specification.display())
                                })?
                                .parse()
                                .with_context(|| {
                                    format!("failed to parse '{}'", &specification.display())
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

            let lem = match lemmas {
                Some(l) => {
                    let lem: fol::Specification = read_to_string(&l)
                        .with_context(|| format!("failed to read '{}'", &l.display()))?
                        .parse()
                        .with_context(|| format!("failed to parse '{}'", &l.display()))?;
                    Some(lem)
                }
                None => None,
            };

            match with {
                Verification::Default => {
                    vampire::default_verification(&prog, &spec, &ug, lem, simplify);
                }
                Verification::Sequential => {
                    vampire::sequential_verification(&prog, &spec, &ug, lem, simplify);
                }
            }
        }
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
