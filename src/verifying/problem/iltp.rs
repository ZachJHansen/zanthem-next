#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct IltpAnnotatedFormula(AnnotatedFormula);

impl IltpAnnotatedFormula {
    fn symbols(&self) -> IndexSet<String> {
        self.0.symbols()
    }
}

impl fmt::Display for IltpAnnotatedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = &self.0.name;
        let role = &self.0.role;
        let formula = crate::formatting::fol::iltp::Format(&self.0.formula);
        writeln!(f, "fof({name}, {role}, {formula}).")
    }
}

impl From<AnnotatedFormula> for IltpAnnotatedFormula {
    fn from(value: AnnotatedFormula) -> Self {
        IltpAnnotatedFormula(value)
    }
}

pub struct IltpProblem {
    pub name: String,
    pub formulas: Vec<IltpAnnotatedFormula>,
}

impl IltpProblem {
    pub fn symbols(&self) -> IndexSet<String> {
        let mut result = IndexSet::new();
        for formula in &self.formulas {
            result.extend(formula.symbols())
        }
        result
    }
}

impl fmt::Display for IltpProblem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut symbols = Vec::from_iter(self.symbols());
        symbols.sort_unstable();
        for (i, s) in symbols.windows(2).enumerate() {
            writeln!(
                f,
                "fof(symbol_order_{i}, axiom, p__less__({}, {})).",
                s[0], s[1]
            )?
        }

        for formula in &self.formulas {
            formula.fmt(f)?;
        }

        Ok(())
    }
}

impl From<Problem> for IltpProblem {
    fn from(value: Problem) -> Self {
        IltpProblem {
            name: value.name,
            formulas: value
                .formulas
                .into_iter()
                .map(IltpAnnotatedFormula::from)
                .collect(),
        }
    }
}
