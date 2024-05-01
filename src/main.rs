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
        command_line::{Arguments, Command, Equivalence, Translation},
        syntax_tree::{asp, fol, Node as _},
        translating::{completion::completion, gamma::gamma, tau_star::tau_star},
        verifying::task::{external_equivalence::ExternalEquivalenceTask, Task},
    },
    anyhow::{Context, Result},
    clap::Parser as _,
    either::Either,
    std::ffi::OsStr,
};

fn main() -> Result<()> {
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

            Ok(())
        }

        Command::Verify {
            equivalence: Equivalence::External,
            decomposition,
            direction,
            no_simplify,
            no_eq_break,
            // no_proof_search,
            // out_dir,
            left,
            right,
            aux,
            ..
        } => {
            let specification: Either<asp::Program, fol::Specification> =
                match left.extension().map(OsStr::to_str) {
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
                    Some(Some("spec")) => fol::Specification::from_file(&aux[1])?,
                    Some(Some(_x)) => todo!(),
                    Some(None) => todo!(),
                    None => todo!(),
                },
                None => fol::Specification::empty(),
            };

            let task = ExternalEquivalenceTask {
                specification,
                user_guide,
                program,
                proof_outline,
                decomposition,
                direction,
                simplify: !no_simplify,
                break_equivalences: !no_eq_break,
            };

            let problems = task.decompose()?;

            // TODO
            for (i, problem) in problems.into_iter().enumerate() {
                println!("# problem {i}");
                println!("{problem}");
            }

            Ok(())
        }

        Command::Verify {
            equivalence: Equivalence::Strong,
            ..
        } => {
            let thing: fol::AnnotatedFormula = "lemma: 2 > 1".parse().unwrap();
            println!("{:?}", thing);
            Ok(())
        },
    }
}
