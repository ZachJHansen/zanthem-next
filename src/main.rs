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
        command_line::{Arguments, Command, Translation, Verification},
        proof_search::{problem, vampire},
        syntax_tree::{asp, fol},
        translating::completion::completion,
        translating::tau_star::tau_star,
    },
    anyhow::{Context, Result},
    clap::Parser as _,
    std::{
        fs::{read_dir, read_to_string},
        io,
        path::PathBuf,
    },
};

fn verify(
    with: Verification,
    program: PathBuf,
    specification: PathBuf,
    user_guide: PathBuf,
    lemmas: Option<PathBuf>,
    cores: u16,
    break_equivalences: bool,
    parallelize: bool,
) -> Result<()> {
    let spec = match specification.extension() {
        Some(extension) => match extension.to_str() {
            Some(ext) => match ext {
                "lp" => {
                    let prog2: asp::Program = read_to_string(&specification)
                        .with_context(|| format!("failed to read '{}'", &specification.display()))?
                        .parse()
                        .with_context(|| {
                            format!("failed to parse '{}'", &specification.display())
                        })?;
                    problem::FileType::MiniGringoProgram { program: prog2 }
                }
                "spec" => {
                    let specification: fol::Specification = read_to_string(&specification)
                        .with_context(|| format!("failed to read '{}'", &specification.display()))?
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
            vampire::default_verification(
                &prog,
                &spec,
                &ug,
                lem,
                cores,
                break_equivalences,
                parallelize,
            );
        }
        Verification::Sequential => {
            vampire::sequential_verification(
                &prog,
                &spec,
                &ug,
                lem,
                cores,
                break_equivalences,
                parallelize,
            );
        }
    }
    Ok(())
}

fn collect_files(dir: PathBuf) -> io::Result<Vec<PathBuf>> {
    let mut files = vec![];
    if dir.is_dir() {
        for entry in read_dir(dir)? {
            let entry = entry?;
            let meta = entry.metadata()?;
            if meta.is_file() {
                files.push(entry.path());
            }
        }
    }
    core::result::Result::Ok(files)
}

fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Translate { with, input } => {
            let content = read_to_string(&input)
                .with_context(|| format!("could not read file `{}`", input.display()))?;

            match with {
                Translation::TauStar => {
                    let program: asp::Program = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let theory = tau_star(program);

                    println!("{theory}")
                }
                Translation::Completion => {
                    let program: asp::Program = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let theory = tau_star(program);

                    match completion(&theory) {
                        Some(completion) => {
                            println!("{completion}")
                        }
                        None => {
                            println!("Not a completable theory.")
                        }
                    }
                }
            }

            Ok(())
        }
        Command::Verify {
            with,
            program,
            specification,
            user_guide,
            lemmas,
            cores,
            break_equivalences,
            parallel,
        } => {
            verify(
                with,
                program,
                specification,
                user_guide,
                lemmas,
                cores,
                break_equivalences,
                parallel,
            )?;
            Ok(())
        }
        Command::VerifyAlt {
            with,
            directory,
            cores,
            break_equivalences,
            parallel,
        } => {
            let mut programs: Vec<&PathBuf> = vec![];
            let mut specs: Vec<&PathBuf> = vec![];
            let mut user_guides: Vec<&PathBuf> = vec![];
            let mut lemmas: Vec<&PathBuf> = vec![];

            // TODO - unpack and handle errors in files result
            let files = match collect_files(directory) {
                core::result::Result::Ok(f) => f,
                Err(e) => {
                    println!("Error! {e}");
                    vec![]
                }
            };
            for f in files.iter() {
                match f.clone().into_os_string().into_string().unwrap().as_str() {
                    "program.lp" => {
                        programs.push(f);
                    }
                    "specification.lp" | "specification.spec" => {
                        specs.push(f);
                    }
                    "user_guide.ug" => {
                        user_guides.push(f);
                    }
                    "help.spec" => lemmas.push(f),
                    _ => {
                        println!(
                            "Unexpected file! Ignoring {}",
                            f.clone().into_os_string().into_string().unwrap().as_str()
                        );
                    }
                }
            }
            assert!(programs.len() == 1);
            assert!(specs.len() == 1);
            assert!(user_guides.len() == 1);
            assert!(lemmas.len() < 2);
            if lemmas.len() > 0 {
                verify(
                    with,
                    programs[0].to_path_buf(),
                    specs[0].to_path_buf(),
                    user_guides[0].to_path_buf(),
                    Some(lemmas[0].to_path_buf()),
                    cores,
                    break_equivalences,
                    parallel,
                )?;
            } else {
                verify(
                    with,
                    programs[0].to_path_buf(),
                    specs[0].to_path_buf(),
                    user_guides[0].to_path_buf(),
                    None,
                    cores,
                    break_equivalences,
                    parallel,
                )?;
            }
            Ok(())
        }
    }
}
