use {
    crate::syntax_tree::fol::{Formula, FunctionConstant, Predicate, Sort},
    itertools::Itertools,
    std::{collections::HashSet, fmt, iter::repeat},
};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Interpretation {
    Standard,
}

impl fmt::Display for Interpretation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, include_str!("standard_interpretation.p"))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Role {
    Axiom,
    Conjecture,
}

impl fmt::Display for Role {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Role::Axiom => write!(f, "axiom"),
            Role::Conjecture => write!(f, "conjecture"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct AnnotatedFormula {
    pub name: String,
    pub role: Role,
    pub formula: Formula,
}

impl AnnotatedFormula {
    pub fn predicates(&self) -> HashSet<Predicate> {
        self.formula.predicates()
    }

    pub fn symbols(&self) -> HashSet<String> {
        self.formula.symbols()
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        self.formula.function_constants()
    }
}

impl fmt::Display for AnnotatedFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = &self.name;
        let role = &self.role;
        let formula = crate::formatting::fol::tptp::Format(&self.formula);
        writeln!(f, "tff({name}, {role}, {formula}).")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Problem {
    pub interpretation: Interpretation,
    pub formulas: Vec<AnnotatedFormula>,
}

impl Problem {
    // TODO Tobias: Implement getters for axioms and conjectures

    pub fn predicates(&self) -> HashSet<Predicate> {
        let mut result = HashSet::new();
        for formula in &self.formulas {
            result.extend(formula.predicates())
        }
        result
    }

    pub fn symbols(&self) -> HashSet<String> {
        let mut result = HashSet::new();
        for formula in &self.formulas {
            result.extend(formula.symbols())
        }
        result
    }

    pub fn function_constants(&self) -> HashSet<FunctionConstant> {
        let mut result = HashSet::new();
        for formula in &self.formulas {
            result.extend(formula.function_constants())
        }
        result
    }
}

impl fmt::Display for Problem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.interpretation)?;

        writeln!(f, "% predicate definitions")?;
        for (i, predicate) in self.predicates().into_iter().enumerate() {
            let symbol = predicate.symbol;
            let input: String =
                Itertools::intersperse(repeat("general").take(predicate.arity), " * ").collect();
            writeln!(f, "tff(predicate_{i}, type, {symbol}: ({input}) > $o).")?
        }

        writeln!(f, "% symbol definitions")?;
        for (i, symbol) in self.symbols().into_iter().enumerate() {
            writeln!(f, "tff(type_symbol_{i}, type, {symbol}: general).")?;
            writeln!(
                f,
                "tff(axiom_less_symbol_{i}, axiom, ![X: $int]: less(to_general(X),{symbol}))."
            )?
        }

        writeln!(f, "% function constant definitions")?;
        for (i, constant) in self.function_constants().into_iter().enumerate() {
            let name = crate::formatting::fol::tptp::Format(&constant);
            let sort = match constant.sort {
                Sort::General => "general",
                Sort::Integer => "$int",
                Sort::Symbol => "general",
            };
            writeln!(f, "tff(type_function_constant_{i}, type, {name}: {sort}).")?
        }

        writeln!(f, "% symbol order axioms")?;
        let mut symbols = Vec::from_iter(self.symbols());
        symbols.sort_unstable();
        for (i, s) in symbols.windows(2).enumerate() {
            writeln!(f, "tff(symbol_order_{i}, axiom, less({}, {})).", s[0], s[1])?
        }

        writeln!(f, "%formulas")?;
        for formula in &self.formulas {
            formula.fmt(f)?;
        }

        Ok(())
    }
}
