use {
    crate::{
        command_line::arguments::TaskDecomposition,
        convenience::with_warnings::WithWarnings,
        syntax_tree::fol,
        verifying::{
            outline::{ProofOutline, ProofOutlineError, ProofOutlineWarning},
            problem::{self, FormulaType, Interpretation, Problem},
            task::Task,
        },
    },
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
    pub user_guide: fol::UserGuide,
    pub task_decomposition: TaskDecomposition,
    pub simplify: bool,
    pub break_equivalences: bool,
}

// The derive task assumes proof outlines have been written correctly for this purpose, e.g.
// 1. all the assumptions are defined in the user guide,
// 2. none of the definitions, lemmas, etc. have a direction other than universal
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
        let placeholders = self
            .user_guide
            .placeholders()
            .into_iter()
            .map(|p| (p.name.clone(), p))
            .collect();

        let taken_predicates = self.user_guide.public_predicates();

        let mut warnings: Vec<DerivationTaskWarning> = Vec::new();

        let proof_outline_construction =
            ProofOutline::from_specification(self.proof_outline, taken_predicates, &placeholders)?;
        warnings.extend(
            proof_outline_construction
                .warnings
                .into_iter()
                .map(DerivationTaskWarning::from),
        );

        let mut problems: Vec<Problem> = Vec::new();

        let mut axioms = Vec::new();
        for formula in self.user_guide.formulas() {
            match formula.role {
                fol::Role::Assumption => {
                    let anf = formula.replace_placeholders(&placeholders);
                    axioms.push(anf.into_problem_formula(problem::Role::Axiom, FormulaType::Tff));
                }

                _ => todo!(), // user guides should only contain assumptions
            }
        }

        // All definitions are treated as starting axioms
        axioms.extend(
            proof_outline_construction
                .data
                .forward_definitions
                .into_iter()
                .map(|f| f.into_problem_formula(problem::Role::Axiom, FormulaType::Tff)),
        );

        axioms.extend(
            proof_outline_construction
                .data
                .backward_definitions
                .into_iter()
                .map(|f| f.into_problem_formula(problem::Role::Axiom, FormulaType::Tff)),
        );

        // All lemmas are derived sequentially, axiom set grows accordingly
        // forward_lemmas = backward_lemmas if proof outline was written correctly
        for (i, lemma) in proof_outline_construction
            .data
            .forward_lemmas
            .iter()
            .enumerate()
        {
            for (j, conjecture) in lemma.conjectures.iter().enumerate() {
                problems.push(
                    Problem::with_name(format!("outline_{i}_{j}"), Interpretation::Standard)
                        .add_annotated_formulas(axioms.clone())
                        .add_annotated_formulas(std::iter::once(conjecture.clone()))
                        .rename_conflicting_symbols(),
                );
            }
            axioms.append(&mut lemma.consequences.clone());
        }

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
