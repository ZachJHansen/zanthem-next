use std::thread;

use {
    crate::{
        proof_search::problem::{FileType, ProblemHandler, ProblemStatus},
        syntax_tree::{asp, fol},
    },
    anyhow::anyhow,
    lazy_static::lazy_static,
    regex::Regex,
    std::process,
};

lazy_static! {
    static ref THRM: Regex = Regex::new(r"% SZS status Theorem").unwrap();
    static ref TIME: Regex = Regex::new(r"% \(\d+\)Success in time (\d+(?:\.\d+)?) s").unwrap();
    static ref NTFD: Regex = Regex::new(r"% \(\d+\)Proof not found in time").unwrap();
}

// TODO - at the end of a session, the problem handler should save all the proven claims as .spec files
// How should the memory work? It could operate similarly to memcached - given a claim, hash it to see if it has been saved
// in the memory of proven results, if it has then return the result otherwise ask vampire to prove it
// The interactivity could be handled similarly to a web session - instead of forcing the user to remain
// in an interaction e.g. via a while loop, each verification call is like a web request, and intermediate results are stored like cookies
pub fn default_verification(
    program: &asp::Program,
    specification: &FileType,
    user_guide: &fol::Specification,
    lemmas: Option<fol::Specification>,
    break_equivalences: bool,
) {
    let mut h = ProblemHandler::new(program, specification, user_guide);
    match lemmas {
        Some(l) => {
            println!("Warning - adding lemmas to default verification is useless. Try --with sequential.");
            h.add_lemmas(l);
        }
        None => (),
    }
    h.default_decomposition(break_equivalences);
    //h.display();
    h.generate_problem_files();
    verify_with_vampire(h);
}

pub fn sequential_verification(
    program: &asp::Program,
    specification: &FileType,
    user_guide: &fol::Specification,
    lemmas: Option<fol::Specification>,
    break_equivalences: bool,
) {
    let mut h = ProblemHandler::new(program, specification, user_guide);
    match lemmas {
        Some(l) => {
            h.add_lemmas(l);
        }
        None => (),
    }
    h.sequential_decomposition(break_equivalences);
    h.generate_problem_files();
    verify_with_vampire(h);
}

pub fn verify_with_vampire(handler: ProblemHandler) {
    let mut task_status = ProblemStatus::Unknown;
    let mut thread_handles = vec![];
    for (c, p) in handler.goals.iter() {
        let claim = c.clone();
        let problems = p.clone();
        let handle = thread::spawn(move || {
            let mut claim_status = ProblemStatus::Unknown;
            println!("Proving Claim... \n%%%%%%%%%%\n{}", claim.display());
            for p in problems.iter() {
                let result = run_vampire(
                    &p.display(true),
                    Some(&[
                        "--proof",
                        "off",
                        "--mode",
                        "casc",
                        "--cores",
                        "4",
                        "--time_limit",
                        "300",
                    ]),
                );
                match result {
                    Ok(status) => match status {
                        ProblemStatus::Theorem => {
                            println!("Conjecture: {} \n\t| Status: Proven", p.conjecture);
                        }
                        _ => {
                            claim_status = ProblemStatus::Timeout; // TODO - Differentiate between different vampire errors/non-theorem results
                            println!("Conjecture: {} \n\t| Status: Not Proven", p.conjecture);
                            break;
                        }
                    },
                    Err(e) => {
                        claim_status = ProblemStatus::Error;
                        println!("{e}");
                        break;
                    }
                }
                claim_status = ProblemStatus::Theorem;
            }
            let task_status = match claim_status {
                ProblemStatus::Theorem => {
                    println!("\n%%%%% Claim status: Theorem %%%%%\n");
                    ProblemStatus::Unknown
                },
                _ => {
                    println!("\n%%%%% Claim status: Not a Theorem %%%%%\n");
                    ProblemStatus::Timeout
                },
            };
            task_status
        });
        thread_handles.push(handle);
    }

    for handle in thread_handles {
        let claim_failure = handle.join().unwrap();
        match claim_failure {
            ProblemStatus::Timeout => {
                task_status = ProblemStatus::Timeout;
            },
            _ => {},
        }
    }

    match task_status {
        ProblemStatus::Unknown => {
            println!("\n%%%%% Task status: Successfully proved all claims. %%%%%\n")
        }
        _ => println!("\n%%%%% Task status: Failed to prove some claims. %%%%%\n"),
    }
}

fn run_vampire<I, S>(input: &str, arguments: Option<I>) -> Result<ProblemStatus, anyhow::Error>
where
    I: IntoIterator<Item = S>,
    S: AsRef<std::ffi::OsStr>,
{
    let mut vampire = process::Command::new("vampire");

    let vampire = match arguments {
        Some(arguments) => vampire.args(arguments),
        None => &mut vampire,
    };

    let mut vampire = vampire
        .stdin(process::Stdio::piped())
        .stdout(process::Stdio::piped())
        .stderr(process::Stdio::piped())
        .spawn()?;

    {
        use std::io::Write as _;

        let vampire_stdin = vampire.stdin.as_mut().unwrap();
        vampire_stdin.write_all(input.as_bytes())?;
    }

    let output = vampire.wait_with_output()?;

    let stdout = std::str::from_utf8(&output.stdout)?;

    let stderr = std::str::from_utf8(&output.stderr)?;

    if !output.status.success() {
        if NTFD.is_match(stdout) {
            return Ok(ProblemStatus::Timeout);
        }

        let exit_code = output.status.code().unwrap();
        return Err(anyhow!("Vampire exited with error code {}\n%%%%%% Vampire stdout %%%%%%\n{}\n%%%%%% Vampire stderr %%%%%%\n{}%%%%%%\n",
            exit_code, stdout.to_string(), stderr.to_string()
        ));
    }

    let _proof_time = TIME
        .captures(stdout)
        .map(|captures| captures.get(1).unwrap().as_str().parse::<f32>().ok())
        .unwrap_or(None);

    if THRM.is_match(stdout) {
        return Ok(ProblemStatus::Theorem);
    }

    return Err(anyhow!("Unknown failure\n%%%%%% Vampire stdout %%%%%%\n{}\n%%%%%% Vampire stderr %%%%%%\n{}%%%%%%\n",
            stdout.to_string(), stderr.to_string()
        ));

    // TODO: support disproven result
}
