use {
    crate::verifying::{
        problem::Problem,
        prover::{Prover, Report, Status, StatusExtractionError},
    },
    std::{
        fmt::{self, Display},
        io::Write as _,
        process::{Command, Output, Stdio},
        time::Instant,
    },
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum VampireError {
    #[error("unable to spawn vampire as a child process")]
    UnableToSpawn(#[source] std::io::Error),
    #[error("unable to write to vampire's stdin")]
    UnableToWrite(#[source] std::io::Error),
    #[error("unable to wait for vampire")]
    UnableToWait(#[source] std::io::Error),
    #[error("unable to convert output")]
    UnableToConvertOutput(#[source] std::string::FromUtf8Error),
}

#[derive(Debug, Clone)]
pub struct VampireOutput {
    pub stdout: String,
    pub stderr: String,
}

impl TryFrom<Output> for VampireOutput {
    type Error = VampireError;

    fn try_from(value: Output) -> Result<Self, Self::Error> {
        // TODO: Should we do something about the exit status?!
        Ok(VampireOutput {
            stdout: String::from_utf8(value.stdout).map_err(VampireError::UnableToConvertOutput)?,
            stderr: String::from_utf8(value.stderr).map_err(VampireError::UnableToConvertOutput)?,
        })
    }
}

#[derive(Debug, Clone)]
pub struct VampireReport {
    pub problem: Problem,
    pub output: VampireOutput,
    pub start_time: Option<Instant>,
}

impl Report for VampireReport {
    fn status(&self) -> Result<Status, StatusExtractionError> {
        self.output.stdout.parse()
    }
}

impl Display for VampireReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "???--- {} ---", self.problem.name)?;
        writeln!(f)?;

        writeln!(f, "axioms:")?;
        for axiom in self.problem.axioms() {
            writeln!(f, "    {}", axiom.formula)?;
        }
        writeln!(f)?;

        writeln!(f, "conjectures:")?;
        for conjecture in self.problem.conjectures() {
            writeln!(f, "    {}", conjecture.formula)?;
        }
        writeln!(f)?;

        match (self.status(), self.start_time) {
            (Ok(status), None) => writeln!(f, "status: {status}"),
            (Ok(status), Some(start)) => {
                writeln!(f, "status: {status} ({} ms)", start.elapsed().as_millis())
            }
            (Err(error), None) => writeln!(f, "error: {error}"),
            (Err(error), Some(start)) => {
                writeln!(f, "error: {error} ({} ms)", start.elapsed().as_millis())
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Vampire {
    pub time_limit: usize,
    pub time_execution: bool,
    pub instances: usize,
    pub cores: usize,
}

impl Prover for Vampire {
    type Error = VampireError;
    type Report = VampireReport;

    fn instances(&self) -> usize {
        if self.instances == 0 {
            std::cmp::max(num_cpus::get() / self.cores(), 1)
        } else {
            self.instances
        }
    }

    fn cores(&self) -> usize {
        if self.cores == 0 {
            num_cpus::get()
        } else {
            self.cores
        }
    }

    fn prove(&self, problem: Problem) -> Result<Self::Report, Self::Error> {
        let start_time = if self.time_execution {
            Some(Instant::now())
        } else {
            None
        };

        let mut child = Command::new("vampire")
            .args([
                "--mode",
                "casc",
                "--time_limit",
                &self.time_limit.to_string(),
                "--cores",
                &self.cores().to_string(),
            ])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(VampireError::UnableToSpawn)?;

        let mut stdin = child.stdin.take().unwrap();
        write!(stdin, "{problem}").map_err(VampireError::UnableToWrite)?;
        drop(stdin);

        let output = child
            .wait_with_output()
            .map_err(VampireError::UnableToWait)?
            .try_into()?;

        Ok(VampireReport {
            problem,
            output,
            start_time,
        })
    }
}
