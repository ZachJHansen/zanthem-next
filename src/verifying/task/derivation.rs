use {
    crate::{
        syntax_tree::fol,
        verifying::{
            problem::{AnnotatedFormula, Problem, Role},
            task::Task,
        },
    },
    thiserror::Error,
};

#[derive(Error, Debug)]
pub enum DerivationTaskError {
    #[error("couldn't process lemma due to error `{0}`")]
    GeneralLemmaError(String),
}

pub struct DerivationTask {
    pub specification: fol::Specification,
    pub simplify: bool,
    pub break_equivalences: bool,
}

impl Task for DerivationTask {
    type Error = DerivationTaskError;

    // TODO - apply simplifications, equivalence breaking
    fn decompose(self) -> Result<Vec<Problem>, Self::Error> {
        let mut assumptions = Vec::new();
        let mut lemmas = Vec::new();
        for anf in self.specification.formulas {
            match anf.role {
                fol::Role::Assumption => {
                    let assumption = AnnotatedFormula::from((anf, Role::Axiom));
                    assumptions.push(assumption)
                }
                fol::Role::Lemma | fol::Role::InductiveLemma => match anf.general_lemma() {
                    Ok(lemma) => lemmas.push(lemma),
                    Err(err) => {
                        return Err(DerivationTaskError::GeneralLemmaError(err.to_string()))
                    }
                },
                _ => println!("Ignoring formula \n{anf}\n due to unexpected role"),
            }
        }

        let problems =
            Problem::from_derivation_components("derivation".to_string(), assumptions, lemmas);

        Ok(problems)
    }
}
