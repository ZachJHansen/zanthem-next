use {
    crate::{
        command_line::arguments::TaskDecomposition,
        convenience::with_warnings::WithWarnings,
        syntax_tree::fol::{self, FunctionConstant},
        verifying::{
            outline::{ProofOutline, ProofOutlineError, ProofOutlineWarning},
            problem::Problem,
            task::Task,
        },
    },
    indexmap::{IndexMap, IndexSet},
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum DerivationTaskError {
    #[error("error")]
    ProofOutlineError(#[from] ProofOutlineError),
}

#[derive(Error, Debug, Eq, PartialEq)]
pub enum DerivationTaskWarning {
    #[error("warning")]
    DefinitionWithWarning(#[from] ProofOutlineWarning),
}

pub struct DerivationTask {
    pub proof_outline: fol::Specification,
    pub task_decomposition: TaskDecomposition,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl Task for DerivationTask {
    type Error = DerivationTaskError;

    type Warning = DerivationTaskWarning;

    fn decompose(
        self,
    ) -> crate::convenience::with_warnings::Result<
        Vec<crate::verifying::problem::Problem>,
        Self::Warning,
        Self::Error,
    > {
        let placeholders: IndexMap<String, FunctionConstant> = IndexMap::new();
        let taken_preds: IndexSet<fol::Predicate> = IndexSet::new();

        let mut warnings: Vec<DerivationTaskWarning> = Vec::new();
        let proof_outline_construction =
            ProofOutline::from_specification(self.proof_outline, taken_preds, &placeholders)?;
        warnings.extend(
            proof_outline_construction
                .warnings
                .into_iter()
                .map(DerivationTaskWarning::from),
        );

        let problems: Vec<Problem> = Vec::new();

        Ok(WithWarnings {
            data: problems
                .into_iter()
                .flat_map(|p: Problem| match self.task_decomposition {
                    TaskDecomposition::Independent => p.decompose_independent(),
                    TaskDecomposition::Sequential => p.decompose_sequential(),
                })
                .collect(),
            warnings,
        })
    }
}
