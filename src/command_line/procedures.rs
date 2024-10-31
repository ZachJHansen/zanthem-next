use {
    crate::{
        analyzing::tightness::Tightness,
        command_line::{
            arguments::{Arguments, Command, Equivalence, Property, Simplification, Translation},
            files::Files,
        },
        simplifying::fol::ht::{simplify, simplify_shallow},
        syntax_tree::{asp, fol, Node as _},
        translating::{
            completion::completion,
            gamma::gamma,
            tau_star::{tau_star, Version},
        },
        verifying::{
            prover::{vampire::Vampire, Prover, Report, Status, Success},
            task::{
                derivation::DerivationTask, external_equivalence::ExternalEquivalenceTask,
                strong_equivalence::StrongEquivalenceTask, Task,
            },
        },
    },
    anyhow::{anyhow, Context, Result},
    clap::Parser as _,
    either::Either,
    std::time::Instant,
};

pub fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Analyze { property, input } => {
            match property {
                Property::Tightness => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let is_tight = program.is_tight();
                    println!("{is_tight}");
                }
            }

            let func: asp::Term = "#abs(1)".parse().unwrap();
            println!("{func}");

            Ok(())
        }

        Command::Derive {
            outline,
            user_guide,
            task_decomposition,
            no_simplify,
            no_eq_break,
            time_limit,
            no_proof_search,
            no_timing,
            out_dir,
            prover_instances,
            prover_cores,
        } => {
            let start_time = if !no_timing {
                Some(Instant::now())
            } else {
                None
            };

            println!(
                "WARNING: Do not specify directions (forward, backward) in any annotated formulas!"
            );

            let proof_outline = fol::Specification::from_file(outline)?;
            let user_guide = fol::UserGuide::from_file(user_guide)?;

            let problems = DerivationTask {
                proof_outline,
                user_guide,
                task_decomposition,
                simplify: !no_simplify,
                break_equivalences: !no_eq_break,
            }
            .decompose()?
            .report_warnings();

            if let Some(out_dir) = out_dir {
                for problem in &problems {
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            if !no_proof_search {
                let prover = Vampire {
                    time_limit,
                    time_execution: !no_timing,
                    instances: prover_instances,
                    cores: prover_cores,
                };

                let problems = problems.into_iter().inspect(|problem| {
                    println!("> Proving {}...", problem.name);
                    println!("Axioms:");
                    for axiom in problem.axioms() {
                        println!("    {}", axiom.formula);
                    }
                    println!();
                    println!("Conjectures:");
                    for conjecture in problem.conjectures() {
                        println!("    {}", conjecture.formula);
                    }
                    println!();
                });

                let mut success = true;
                for result in prover.prove_all(problems) {
                    match result {
                        Ok(report) => match report.status() {
                            Ok(status) => {
                                println!(
                                    "> Proving {} ended with a SZS status",
                                    report.problem.name
                                );

                                match report.start_time {
                                    Some(start) => println!(
                                        "Status: {status} ({} ms)",
                                        start.elapsed().as_millis()
                                    ),
                                    None => println!("Status: {status}"),
                                }

                                if !matches!(status, Status::Success(Success::Theorem)) {
                                    success = false;
                                }
                            }
                            Err(error) => {
                                match report.start_time {
                                    Some(start) => println!(
                                        "> Proving {} ended without a SZS status ({} ms)",
                                        report.problem.name,
                                        start.elapsed().as_millis()
                                    ),
                                    None => println!(
                                        "> Proving {} ended without a SZS status",
                                        report.problem.name
                                    ),
                                }

                                println!("Output/stdout:");
                                println!("{}", report.output.stdout);
                                println!("Output/stderr:");
                                println!("{}", report.output.stderr);
                                println!("Error: {error}");
                                success = false;
                            }
                        },
                        Err(error) => {
                            println!("> Proving <a problem> ended with an error"); // TODO: Get the name of the problem
                            println!("Error: {error}");
                            success = false;
                        }
                    }
                    println!();
                }

                if success {
                    print!("> Success! Anthem proved every lemma.")
                } else {
                    print!("> Failure! Anthem was unable to prove every lemma.")
                }
            }

            match start_time {
                Some(start) => println!(" ({} ms)", start.elapsed().as_millis()),
                None => println!(),
            }

            Ok(())
        }

        Command::Simplify { with, input } => {
            let theory = input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
            match with {
                Simplification::CompleteHT => {
                    let simplified_theory = simplify(theory);
                    println!("{simplified_theory}");
                }
                Simplification::ShallowHT => {
                    let simplified_theory = simplify_shallow(theory);
                    println!("{simplified_theory}");
                }
            }

            Ok(())
        }

        Command::Translate { with, input } => {
            match with {
                Translation::Completion => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let completed_theory =
                        completion(theory).context("the given theory is not completable")?;
                    print!("{completed_theory}")
                }

                Translation::Gamma => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let gamma_theory = gamma(theory);
                    print!("{gamma_theory}")
                }

                Translation::TauStarV1 | Translation::TauStarV2 => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let theory = match with {
                        Translation::TauStarV1 => tau_star::tau_star(program, Version::Original),
                        Translation::TauStarV2 => {
                            tau_star::tau_star(program, Version::AbstractGringoCompliant)
                        }
                        _ => unreachable!(),
                    };
                    print!("{theory}")
                }
            }

            Ok(())
        }

        Command::Verify {
            equivalence,
            formula_representation,
            task_decomposition,
            direction,
            bypass_tightness,
            no_simplify,
            no_eq_break,
            no_proof_search,
            no_timing,
            time_limit,
            prover_instances,
            prover_cores,
            save_problems: out_dir,
            files,
        } => {
            let start_time = if !no_timing {
                Some(Instant::now())
            } else {
                None
            };

            let files =
                Files::sort(files).context("unable to sort the given files by their function")?;

            let problems = match equivalence {
                Equivalence::Strong => StrongEquivalenceTask {
                    left: asp::Program::from_file(
                        files
                            .left()
                            .ok_or(anyhow!("no left program was provided"))?,
                    )?,
                    right: asp::Program::from_file(
                        files
                            .right()
                            .ok_or(anyhow!("no right program was provided"))?,
                    )?,
                    task_decomposition,
                    direction,
                    formula_representation,
                    simplify: !no_simplify,
                    break_equivalences: !no_eq_break,
                }
                .decompose()?
                .report_warnings(),
                Equivalence::External => ExternalEquivalenceTask {
                    specification: match files
                        .specification()
                        .ok_or(anyhow!("no specification was provided"))?
                    {
                        Either::Left(program) => Either::Left(asp::Program::from_file(program)?),
                        Either::Right(specification) => {
                            Either::Right(fol::Specification::from_file(specification)?)
                        }
                    },
                    program: asp::Program::from_file(
                        files.program().ok_or(anyhow!("no program was provided"))?,
                    )?,
                    user_guide: fol::UserGuide::from_file(
                        files
                            .user_guide()
                            .ok_or(anyhow!("no user guide was provided"))?,
                    )?,
                    proof_outline: files
                        .proof_outline()
                        .map(fol::Specification::from_file)
                        .unwrap_or_else(|| Ok(fol::Specification::empty()))?,
                    formula_representation,
                    task_decomposition,
                    direction,
                    bypass_tightness,
                    simplify: !no_simplify,
                    break_equivalences: !no_eq_break,
                }
                .decompose()?
                .report_warnings(),
            };

            if let Some(out_dir) = out_dir {
                for problem in &problems {
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            if !no_proof_search {
                let prover = Vampire {
                    time_limit,
                    time_execution: !no_timing,
                    instances: prover_instances,
                    cores: prover_cores,
                };

                let problems = problems.into_iter().inspect(|problem| {
                    println!("> Proving {}...", problem.name);
                    println!("Axioms:");
                    for axiom in problem.axioms() {
                        println!("    {}", axiom.formula);
                    }
                    println!();
                    println!("Conjectures:");
                    for conjecture in problem.conjectures() {
                        println!("    {}", conjecture.formula);
                    }
                    println!();
                });

                let mut success = true;
                for result in prover.prove_all(problems) {
                    match result {
                        Ok(report) => match report.status() {
                            Ok(status) => {
                                println!(
                                    "> Proving {} ended with a SZS status",
                                    report.problem.name
                                );

                                match report.start_time {
                                    Some(start) => println!(
                                        "Status: {status} ({} ms)",
                                        start.elapsed().as_millis()
                                    ),
                                    None => println!("Status: {status}"),
                                }

                                if !matches!(status, Status::Success(Success::Theorem)) {
                                    success = false;
                                }
                            }
                            Err(error) => {
                                match report.start_time {
                                    Some(start) => println!(
                                        "> Proving {} ended without a SZS status ({} ms)",
                                        report.problem.name,
                                        start.elapsed().as_millis()
                                    ),
                                    None => println!(
                                        "> Proving {} ended without a SZS status",
                                        report.problem.name
                                    ),
                                }

                                println!("Output/stdout:");
                                println!("{}", report.output.stdout);
                                println!("Output/stderr:");
                                println!("{}", report.output.stderr);
                                println!("Error: {error}");
                                success = false;
                            }
                        },
                        Err(error) => {
                            println!("> Proving <a problem> ended with an error"); // TODO: Get the name of the problem
                            println!("Error: {error}");
                            success = false;
                        }
                    }
                    println!();
                }

                if success {
                    print!("> Success! Anthem found a proof of equivalence.")
                } else {
                    print!("> Failure! Anthem was unable to find a proof of equivalence.")
                }

                match start_time {
                    Some(start) => println!(" ({} ms)", start.elapsed().as_millis()),
                    None => println!(),
                }
            }

            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {

    use crate::syntax_tree::{asp, fol};

    #[test]
    fn asp_program_parse_and_format() {
        for string in [
            "p(X) :- q(X).\n",
            "p(Y) :- Y = 1..|-5 + 3|.\n",
            "q :- p, not not q.\n",
            "p(|Y + 1|) :- src(Y), Y < -|-1|.\n",
        ] {
            let program: asp::Program = string.parse().unwrap();
            assert_eq!(
                string,
                format!("{program}"),
                "assertion `left == right` failed:\n left:\n{string}\n right:\n{program}"
            );
        }
    }

    #[test]
    fn fol_formula_parse_and_format() {
        for string in [
            "forall X (p(X) <-> exists N$i (q(N$i) and |N$i| = X))",
            "p(|1 + |3 - 5||)",
            "p(||3 - 5||)",
            "p(|-|3 - 5||)",
        ] {
            let formula: fol::Formula = string.parse().unwrap();
            assert_eq!(
                string,
                format!("{formula}"),
                "assertion `left == right` failed:\n left:\n{string}\n right:\n{formula}"
            );
        }
    }
}
