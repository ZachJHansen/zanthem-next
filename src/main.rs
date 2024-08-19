pub mod command_line;
pub mod convenience;
pub mod formatting;
pub mod parsing;
pub mod simplifying;
pub mod syntax_tree;
pub mod translating;
pub mod verifying;

use {
    crate::{
        command_line::{Arguments, Command, Equivalence, Simplification, Translation},
        syntax_tree::{asp, fol, Node as _},
        translating::{completion::completion, gamma::gamma, tau_star::tau_star},
        verifying::{
            proof::vampire::verify,
            task::{
                derivation::DerivationTask, external_equivalence::ExternalEquivalenceTask,
                strong_equivalence::StrongEquivalenceTask, Task,
            },
        },
    },
    anyhow::{Context, Result},
    clap::Parser as _,
    either::Either,
    lazy_static::lazy_static,
    log::info,
    regex::Regex,
    simplifying::fol::classic::simplify,
    std::{ffi::OsStr, fs::read_dir, io, path::PathBuf, time::Instant},
    verifying::task::external_equivalence::ReplacePlaceholders,
};

lazy_static! {
    static ref HELP: Regex = Regex::new(r"\.help\.spec$").unwrap();
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
    env_logger::init();

    let now = Instant::now();

    match Arguments::parse().command {
        Command::Translate { with, input } => {
            match with {
                Translation::Completion => {
                    let theory = fol::Theory::from_file(input)?;
                    let completed_theory =
                        completion(theory).context("the given theory is not completable")?;
                    print!("{completed_theory}")
                }

                Translation::Gamma => {
                    let theory = fol::Theory::from_file(input)?;
                    let gamma_theory = gamma(theory);
                    print!("{gamma_theory}")
                }

                Translation::TauStar => {
                    let program = asp::Program::from_file(input)?;
                    let theory = tau_star(program);
                    print!("{theory}")
                }
            }
            info!("System runtime: {} milliseconds", now.elapsed().as_millis());

            Ok(())
        }

        Command::Simplify { with, input } => {
            match with {
                Simplification::CompleteHT => {
                    let theory = fol::Theory::from_file(input)?;
                    let simplified_theory = simplify(theory, true);
                    println!("{simplified_theory}");
                }
            }
            info!("System runtime: {} milliseconds", now.elapsed().as_millis());

            Ok(())
        }

        Command::Derive {
            input,
            no_simplify,
            no_eq_break,
            time_limit,
            no_proof_search,
            out_dir,
            no_timing,
        } => {
            let specification = fol::Specification::from_file(input)?;

            let problems = DerivationTask {
                specification,
                simplify: !no_simplify,
                break_equivalences: !no_eq_break,
            }
            .decompose()?;

            if let Some(out_dir) = out_dir {
                for problem in problems.clone().into_iter() {
                    problem.summarize();
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            if !no_proof_search {
                verify(problems, time_limit, no_timing);
            }

            info!("System runtime: {} milliseconds", now.elapsed().as_millis());

            if !no_timing {
                println!("System runtime: {} milliseconds", now.elapsed().as_millis());
            }

            Ok(())
        }

        Command::Verify {
            equivalence,
            decomposition,
            direction,
            no_simplify,
            no_eq_break,
            no_proof_search,
            out_dir,
            left,
            right,
            aux,
            time_limit,
            no_timing,
        } => {
            let problems = match equivalence {
                Equivalence::Strong => StrongEquivalenceTask {
                    left: asp::Program::from_file(left)?,
                    right: asp::Program::from_file(right)?,
                    decomposition,
                    direction,
                    simplify: !no_simplify,
                    break_equivalences: !no_eq_break,
                }
                .decompose()?,

                Equivalence::External => {
                    let specification: Either<asp::Program, fol::Specification> = match left
                        .extension()
                        .map(OsStr::to_str)
                    {
                        Some(Some("lp")) => Either::Left(asp::Program::from_file(left)?),
                        Some(Some("spec")) => Either::Right(fol::Specification::from_file(left)?),
                        Some(Some(_x)) => todo!(),
                        Some(None) => todo!(),
                        None => todo!(),
                    };

                    let program: asp::Program = match right.extension().map(|x| x.to_str()) {
                        Some(Some("lp")) => asp::Program::from_file(right)?,
                        Some(Some(_x)) => todo!(),
                        Some(None) => todo!(),
                        None => todo!(),
                    };

                    let user_guide: fol::UserGuide = match aux
                        .first()
                        .with_context(|| "no user guide was provided")?
                        .extension()
                        .map(OsStr::to_str)
                    {
                        Some(Some("ug")) => fol::UserGuide::from_file(aux.first().unwrap())?,
                        Some(Some(_x)) => todo!(),
                        Some(None) => todo!(),
                        None => todo!(),
                    };

                    let proof_outline = match aux.get(1) {
                        Some(path) => match path.extension().map(OsStr::to_str) {
                            Some(Some("spec")) => {
                                fol::Specification::from_file(aux.get(1).unwrap())?
                            }
                            Some(Some(_x)) => todo!(),
                            Some(None) => todo!(),
                            None => todo!(),
                        },
                        None => fol::Specification::empty(),
                    };

                    ExternalEquivalenceTask {
                        specification,
                        user_guide,
                        program,
                        proof_outline,
                        decomposition,
                        direction,
                        simplify: !no_simplify,
                        break_equivalences: !no_eq_break,
                    }
                    .decompose()?
                }
            };

            if let Some(out_dir) = out_dir {
                for problem in problems.clone().into_iter() {
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            if !no_proof_search {
                verify(problems, time_limit, no_timing);
            }

            info!("System runtime: {} milliseconds", now.elapsed().as_millis());

            if !no_timing {
                println!("System runtime: {} milliseconds", now.elapsed().as_millis());
            }

            Ok(())
        }

        Command::VerifyAlt {
            equivalence,
            decomposition,
            direction,
            no_simplify,
            no_eq_break,
            no_proof_search,
            out_dir,
            problem_dir,
            time_limit,
            no_timing,
        } => {
            let mut programs: Vec<&PathBuf> = vec![];
            let mut specs: Vec<&PathBuf> = vec![];
            let mut user_guides: Vec<&PathBuf> = vec![];
            let mut lemmas: Vec<&PathBuf> = vec![];

            // TODO - unpack and handle errors in files result
            let files = match collect_files(problem_dir) {
                core::result::Result::Ok(f) => f,
                Err(e) => {
                    println!("Error! {e}");
                    vec![]
                }
            };
            for f in files.iter() {
                match f.extension() {
                    Some(extension) => match extension.to_str().unwrap() {
                        "lp" => {
                            if programs.is_empty() {
                                programs.push(f);
                            } else {
                                specs.push(programs.pop().unwrap());
                                programs.push(f);
                            }
                        }
                        "spec" => {
                            if HELP.is_match(&f.clone().into_os_string().into_string().unwrap()) {
                                lemmas.push(f);
                            } else {
                                specs.push(f);
                            }
                        }
                        "ug" => {
                            user_guides.push(f);
                        }
                        _ => {
                            println!("Unexpected file! Ignoring {:?}", f);
                        }
                    },
                    None => {
                        println!("Encountered a file with an unexpected extension: {:?}", f);
                    }
                }
            }

            assert!(programs.len() == 1);
            assert!(specs.len() == 1);
            assert!(user_guides.len() == 1);
            assert!(lemmas.len() < 2);

            info!("Treating {:?} as the specification...", specs[0]);
            info!("Treating {:?} as the program...", programs[0]);
            info!("Treating {:?} as the user guide...", user_guides[0]);
            if !lemmas.is_empty() {
                info!("Treating {:?} as the lemmas...", lemmas[0]);
            }

            let left = specs[0];
            let right = programs[0];
            let ug = user_guides[0];

            let problems = match equivalence {
                Equivalence::Strong => todo!(),

                Equivalence::External => {
                    let specification: Either<asp::Program, fol::Specification> = match left
                        .extension()
                        .map(OsStr::to_str)
                    {
                        Some(Some("lp")) => Either::Left(asp::Program::from_file(left)?),
                        Some(Some("spec")) => Either::Right(fol::Specification::from_file(left)?),
                        Some(Some(_x)) => todo!(),
                        Some(None) => todo!(),
                        None => todo!(),
                    };

                    let program: asp::Program = match right.extension().map(|x| x.to_str()) {
                        Some(Some("lp")) => asp::Program::from_file(right)?,
                        Some(Some(_x)) => todo!(),
                        Some(None) => todo!(),
                        None => todo!(),
                    };

                    let user_guide: fol::UserGuide = match ug.extension().map(OsStr::to_str) {
                        Some(Some("ug")) => fol::UserGuide::from_file(ug)?,
                        Some(Some(_x)) => todo!(),
                        Some(None) => todo!(),
                        None => todo!(),
                    };

                    let proof_outline = match lemmas.first() {
                        Some(path) => match path.extension().map(OsStr::to_str) {
                            Some(Some("spec")) => {
                                fol::Specification::from_file(lemmas.first().unwrap())?
                            }
                            Some(Some(_x)) => todo!(),
                            Some(None) => todo!(),
                            None => todo!(),
                        },
                        None => fol::Specification::empty(),
                    };

                    ExternalEquivalenceTask {
                        specification,
                        user_guide,
                        program,
                        proof_outline,
                        decomposition,
                        direction,
                        simplify: !no_simplify,
                        break_equivalences: !no_eq_break,
                    }
                    .decompose()?
                }
            };

            if let Some(out_dir) = out_dir {
                for problem in problems.clone().into_iter() {
                    problem.summarize();
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            // TODO: Run proof search
            if !no_proof_search {
                verify(problems, time_limit, no_timing);
            }

            info!("System runtime: {} milliseconds", now.elapsed().as_millis());

            if !no_timing {
                println!("System runtime: {} milliseconds", now.elapsed().as_millis());
            }

            Ok(())
        }

        Command::Valuate { using, input } => {
            let theory = fol::Theory::from_file(input)?;
            let user_guide = fol::UserGuide::from_file(using)?;
            let placeholder = user_guide
                .placeholders()
                .into_iter()
                .map(|p| (p.name.clone(), p))
                .collect();
            let valuation = theory.replace_placeholders(&placeholder);
            println!("{valuation}");

            Ok(())
        }

        Command::Tighten { input } => {
            let program = asp::Program::from_file(input)?;
            let tightened = program.tighten();
            println!("{tightened}");

            Ok(())
        }
    }
}
