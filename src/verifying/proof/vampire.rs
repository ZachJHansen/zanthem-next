use {
    crate::verifying::problem::Problem,
    anyhow::anyhow,
    lazy_static::lazy_static,
    log::info,
    regex::Regex,
    std::{process, time::Instant},
};

lazy_static! {
    static ref THRM: Regex = Regex::new(r"% SZS status Theorem").unwrap();
    static ref TIME: Regex = Regex::new(r"% \(\d+\)Success in time (\d+(?:\.\d+)?) s").unwrap();
    static ref NTFD: Regex = Regex::new(r"% \(\d+\)Proof not found in time").unwrap();
}

// Reflects the SZS ontology
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ProblemStatus {
    Theorem,
    ContradictoryAxioms,
    CounterSatisfiable,
    Timeout,
    GaveUp,
    Error,
    Unknown,
}

// TODO - at the end of a session, the problem handler should save all the proven claims as .spec files
// How should the memory work? It could operate similarly to memcached - given a claim, hash it to see if it has been saved
// in the memory of proven results, if it has then return the result otherwise ask vampire to prove it
// The interactivity could be handled similarly to a web session - instead of forcing the user to remain
// in an interaction e.g. via a while loop, each verification call is like a web request, and intermediate results are stored like cookies
pub fn verify(problems: Vec<Problem>, time_limit: u16) {
    let cores = 4; // TODO: as argument
    let mut claim_status = ProblemStatus::Theorem;
    for problem in problems {
        let now = Instant::now();
        problem.summarize();
        let result = run_vampire(
            format!("{}", problem).as_str(),
            Some(&[
                "--proof",
                "off",
                "--mode",
                "casc",
                "--cores",
                &cores.to_string(),
                "--time_limit",
                &time_limit.to_string(),
            ]),
        );
        match result {
            Ok(status) => match status {
                ProblemStatus::Theorem => {
                    println!("\t| Status: Proven");
                    info!("Proven in {} milliseconds", now.elapsed().as_millis());
                }
                _ => {
                    claim_status = ProblemStatus::Timeout; // TODO - Differentiate between different vampire errors/non-theorem results
                    println!("\t| Status: Not Proven");
                    info!("Not proven in {} milliseconds", now.elapsed().as_millis());
                    break;
                }
            },
            Err(e) => {
                claim_status = ProblemStatus::Error;
                println!("{e}");
                break;
            }
        }
    }
    match claim_status {
        ProblemStatus::Theorem => {
            println!("\n%%%%% Claim status: Theorem %%%%%\n");
        }
        _ => {
            println!("\n%%%%% Claim status: Unproven %%%%%\n");
        }
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

    Err(anyhow!("Unknown failure\n%%%%%% Vampire stdout %%%%%%\n{}\n%%%%%% Vampire stderr %%%%%%\n{}%%%%%%\n",
            stdout.to_string(), stderr.to_string()
        ))

    // TODO: support disproven result
}
