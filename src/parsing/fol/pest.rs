use crate::{
    parsing::PestParser, syntax_tree::fol::{
        Atom, AtomicFormula, BasicIntegerTerm, 
        BinaryConnective, BinaryOperator, Comparison, 
        Formula, FormulaName, GeneralTerm, Guard, IntegerTerm, 
        Placeholder, Predicate, Quantification, Quantifier, 
        Relation, Role, Sort, Spec, Specification, Theory, UnaryConnective, 
        UnaryOperator, Variable, AnnotatedFormula, UserGuide, Direction,
    }
};

mod internal {
    use pest::pratt_parser::PrattParser;

    #[derive(pest_derive::Parser)]
    #[grammar = "parsing/fol/grammar.pest"]
    pub struct Parser;

    lazy_static::lazy_static! {
        pub static ref TERM_PRATT_PARSER: PrattParser<Rule> = {
            use pest::pratt_parser::{Assoc::*, Op};
            use Rule::*;

            PrattParser::new()
                .op(Op::infix(add, Left) | Op::infix(subtract, Left))
                .op(Op::infix(multiply, Left))
                .op(Op::prefix(negative))
        };

        pub static ref FORMULA_PRATT_PARSER: PrattParser<Rule> = {
            use pest::pratt_parser::{Assoc::*, Op};
            use Rule::*;

            PrattParser::new()
                .op(Op::infix(equivalence, Right) | Op::infix(implication, Right) | Op::infix(reverse_implication, Left))
                .op(Op::infix(disjunction, Left))
                .op(Op::infix(conjunction, Left))
                .op(Op::prefix(negation) | Op::prefix(quantification))
        };
    }
}

pub struct BasicIntegerTermParser;

impl PestParser for BasicIntegerTermParser {
    type Node = BasicIntegerTerm;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::basic_integer_term;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::basic_integer_term => Self::translate_pairs(pair.into_inner()),
            internal::Rule::infimum => BasicIntegerTerm::Infimum,
            internal::Rule::supremum => BasicIntegerTerm::Supremum,
            internal::Rule::numeral => BasicIntegerTerm::Numeral(pair.as_str().parse().unwrap()),
            internal::Rule::integer_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => {
                    BasicIntegerTerm::IntegerVariable(pair.as_str().into())
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct UnaryOperatorParser;

impl PestParser for UnaryOperatorParser {
    type Node = UnaryOperator;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::unary_operator;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::negative => UnaryOperator::Negative,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct BinaryOperatorParser;

impl PestParser for BinaryOperatorParser {
    type Node = BinaryOperator;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::binary_operator;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::add => BinaryOperator::Add,
            internal::Rule::subtract => BinaryOperator::Subtract,
            internal::Rule::multiply => BinaryOperator::Multiply,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct IntegerTermParser;

impl PestParser for IntegerTermParser {
    type Node = IntegerTerm;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::integer_term;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        internal::TERM_PRATT_PARSER
            .map_primary(|primary| match primary.as_rule() {
                internal::Rule::integer_term => IntegerTermParser::translate_pair(primary),
                internal::Rule::basic_integer_term => {
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTermParser::translate_pair(primary))
                }
                _ => Self::report_unexpected_pair(primary),
            })
            .map_prefix(|op, arg| IntegerTerm::UnaryOperation {
                op: UnaryOperatorParser::translate_pair(op),
                arg: Box::new(arg),
            })
            .map_infix(|lhs, op, rhs| IntegerTerm::BinaryOperation {
                op: BinaryOperatorParser::translate_pair(op),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
            .parse(pair.into_inner())
    }
}

pub struct GeneralTermParser;

impl PestParser for GeneralTermParser {
    type Node = GeneralTerm;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::general_term;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::general_term => Self::translate_pairs(pair.into_inner()),
            internal::Rule::symbolic_constant => GeneralTerm::Symbol(pair.as_str().into()),
            internal::Rule::integer_term => {
                GeneralTerm::IntegerTerm(IntegerTermParser::translate_pair(pair))
            }
            internal::Rule::general_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => {
                    GeneralTerm::GeneralVariable(pair.as_str().into())
                }
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct PredicateParser;

impl PestParser for PredicateParser {
    type Node = Predicate;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::predicate;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::predicate {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();
        let symbol = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str()
            .into();
        let arity_string: &str = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str();
        let arity: usize = arity_string.parse().unwrap();

        Predicate { symbol, arity }
    }
}

pub struct AtomParser;

impl PestParser for AtomParser {
    type Node = Atom;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::atom;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::atom {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let predicate_symbol = pairs
            .next()
            .unwrap_or_else(|| Self::report_missing_pair())
            .as_str()
            .into();
        let terms: Vec<_> = pairs.map(GeneralTermParser::translate_pair).collect();

        Atom {
            predicate_symbol,
            terms,
        }
    }
}

pub struct RelationParser;

impl PestParser for RelationParser {
    type Node = Relation;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::relation;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::relation => Self::translate_pairs(pair.into_inner()),
            internal::Rule::greater_equal => Relation::GreaterEqual,
            internal::Rule::less_equal => Relation::LessEqual,
            internal::Rule::greater => Relation::Greater,
            internal::Rule::less => Relation::Less,
            internal::Rule::equal => Relation::Equal,
            internal::Rule::not_equal => Relation::NotEqual,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct GuardParser;

impl PestParser for GuardParser {
    type Node = Guard;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::guard;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::guard {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let relation = RelationParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );
        let term = GeneralTermParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );

        if let Some(pair) = pairs.next() {
            Self::report_unexpected_pair(pair)
        }

        Guard { relation, term }
    }
}

pub struct ComparisonParser;

impl PestParser for ComparisonParser {
    type Node = Comparison;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::comparison;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::comparison {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let term = GeneralTermParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );

        let guards: Vec<_> = pairs.map(GuardParser::translate_pair).collect();

        Comparison { term, guards }
    }
}

pub struct AtomicFormulaParser;

impl PestParser for AtomicFormulaParser {
    type Node = AtomicFormula;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::atomic_formula;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::atomic_formula => {
                AtomicFormulaParser::translate_pairs(pair.into_inner())
            }
            internal::Rule::truth => AtomicFormula::Truth,
            internal::Rule::falsity => AtomicFormula::Falsity,
            internal::Rule::atom => AtomicFormula::Atom(AtomParser::translate_pair(pair)),
            internal::Rule::comparison => {
                AtomicFormula::Comparison(ComparisonParser::translate_pair(pair))
            }
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct QuantifierParser;

impl PestParser for QuantifierParser {
    type Node = Quantifier;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::quantifier;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::quantifier => QuantifierParser::translate_pairs(pair.into_inner()),
            internal::Rule::forall => Quantifier::Forall,
            internal::Rule::exists => Quantifier::Exists,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct VariableParser;

impl PestParser for VariableParser {
    type Node = Variable;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::variable;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::variable => VariableParser::translate_pairs(pair.into_inner()),
            internal::Rule::integer_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => Variable {
                    name: pair.as_str().into(),
                    sort: Sort::Integer,
                },
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::general_variable => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::unsorted_variable => Variable {
                    name: pair.as_str().into(),
                    sort: Sort::General,
                },
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct QuantificationParser;

impl PestParser for QuantificationParser {
    type Node = Quantification;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::quantification;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::quantification {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let quantifier = QuantifierParser::translate_pair(
            pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
        );

        let variables: Vec<_> = pairs.map(VariableParser::translate_pair).collect();

        Quantification {
            quantifier,
            variables,
        }
    }
}

pub struct UnaryConnectiveParser;

impl PestParser for UnaryConnectiveParser {
    type Node = UnaryConnective;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::unary_connective;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::negation => UnaryConnective::Negation,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct BinaryConnectiveParser;

impl PestParser for BinaryConnectiveParser {
    type Node = BinaryConnective;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: internal::Rule = internal::Rule::binary_connective;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::binary_connective => Self::translate_pairs(pair.into_inner()),
            internal::Rule::equivalence => BinaryConnective::Equivalence,
            internal::Rule::implication => BinaryConnective::Implication,
            internal::Rule::reverse_implication => BinaryConnective::ReverseImplication,
            internal::Rule::conjunction => BinaryConnective::Conjunction,
            internal::Rule::disjunction => BinaryConnective::Disjunction,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct FormulaParser;

impl PestParser for FormulaParser {
    type Node = Formula;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::formula;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        internal::FORMULA_PRATT_PARSER
            .map_primary(|primary| match primary.as_rule() {
                internal::Rule::formula => FormulaParser::translate_pair(primary),
                internal::Rule::atomic_formula => {
                    Formula::AtomicFormula(AtomicFormulaParser::translate_pair(primary))
                }
                _ => Self::report_unexpected_pair(primary),
            })
            .map_prefix(|op, arg| match op.as_rule() {
                internal::Rule::quantification => Formula::QuantifiedFormula {
                    quantification: QuantificationParser::translate_pair(op),
                    formula: Box::new(arg),
                },
                internal::Rule::negation => Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: Box::new(arg),
                },
                _ => Self::report_unexpected_pair(op),
            })
            .map_infix(|lhs, op, rhs| Formula::BinaryFormula {
                connective: BinaryConnectiveParser::translate_pair(op),
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            })
            .parse(pair.into_inner())
    }
}

pub struct TheoryParser;

impl PestParser for TheoryParser {
    type Node = Theory;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::theory;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::theory {
            Self::report_unexpected_pair(pair)
        }
        Theory {
            formulas: pair
                .into_inner()
                .map(FormulaParser::translate_pair)
                .collect(),
        }
    }
}

pub struct PlaceholderParser;

impl PestParser for PlaceholderParser {
    type Node = Placeholder;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::placeholder;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::placeholder => PlaceholderParser::translate_pairs(pair.into_inner()),
            internal::Rule::integer_placeholder => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => Placeholder {
                    name: pair.as_str().into(),
                    sort: Sort::Integer,
                },
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            internal::Rule::general_placeholder => match pair.into_inner().next() {
                Some(pair) if pair.as_rule() == internal::Rule::symbolic_constant => Placeholder {
                    name: pair.as_str().into(),
                    sort: Sort::General,
                },
                Some(pair) => Self::report_unexpected_pair(pair),
                None => Self::report_missing_pair(),
            },
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct RoleParser;

impl PestParser for RoleParser {
    type Node = Role;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::role;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::role => {
                RoleParser::translate_pairs(pair.into_inner())
            }
            internal::Rule::assumption => Role::Assumption,
            internal::Rule::conjecture => Role::Conjecture,
            internal::Rule::lemma => Role::Lemma,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct DirectionParser;

impl PestParser for DirectionParser {
    type Node = Direction;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::direction;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::role => {
                DirectionParser::translate_pairs(pair.into_inner())
            }
            internal::Rule::forward => Direction::Forward,
            internal::Rule::backward => Direction::Backward,
            internal::Rule::universal => Direction::Universal,
            _ => Self::report_unexpected_pair(pair),
        }
    }
}


pub struct FormulaNameParser;

impl PestParser for FormulaNameParser {
    type Node = FormulaName;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::formula_name;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::formula_name {
            Self::report_unexpected_pair(pair)
        }

        let mut pairs = pair.into_inner();

        let name_candidate = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
        let name = match name_candidate.as_rule() {
            internal::Rule::symbolic_constant => Some(name_candidate.as_str().into()),
            _ => None,
        };

        FormulaName(name)
    }
}

pub struct AnnotatedFormulaParser;

impl PestParser for AnnotatedFormulaParser {
    type Node = AnnotatedFormula;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::annotated_formula;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::annotated_formula => {
                let mut pairs = pair.into_inner();
                
                let role = RoleParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                let direction;
                let formula_name;
                if pairs.len() > 2 {
                    let next_pair = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
                    match next_pair.as_rule() {
                        internal::Rule::direction => {
                            direction = DirectionParser::translate_pair(next_pair);
                            if pairs.len() > 3 {
                                let next_pair = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
                                match next_pair.as_rule() {
                                    internal::Rule::formula_name => formula_name = FormulaNameParser::translate_pair(next_pair),
                                    _ => Self::report_unexpected_pair(pair),
                                }
                            } else {
                                formula_name = FormulaName(None);
                            }
                        },
                        internal::Rule::formula_name => {
                            direction = Direction::Universal;
                            formula_name = FormulaNameParser::translate_pair(next_pair);
                        },
                        _ => Self::report_unexpected_pair(pair),
                    };
                }

                let formula = FormulaParser::translate_pair(
                    pairs.next().unwrap_or_else(|| Self::report_missing_pair()),
                );

                AnnotatedFormula {
                    role,
                    direction,
                    name: formula_name,
                    formula
                }
            },
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct SpecificationParser;

impl PestParser for SpecificationParser {
    type Node = Specification;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::specification;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::specification {
            Self::report_unexpected_pair(pair)
        }
        Specification {
            formulas: pair
                .into_inner()
                .map(AnnotatedFormulaParser::translate_pair)
                .collect(),
        }
    }
}

pub struct SpecParser;

impl PestParser for SpecParser {
    type Node = Spec;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::spec;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        match pair.as_rule() {
            internal::Rule::spec => SpecParser::translate_pairs(pair.into_inner()),

            internal::Rule::input => {
                if pair.as_rule() != internal::Rule::input {
                    Self::report_unexpected_pair(pair)
                }

                let mut pairs = pair.into_inner();

                let first_predicate = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
                let remaining_predicates: Vec<_> =
                    pairs.map(PredicateParser::translate_pair).collect();

                let mut predicates = vec![PredicateParser::translate_pair(first_predicate)];
                predicates.extend(remaining_predicates);

                Spec::Input { predicates }
            }
            internal::Rule::output => {
                if pair.as_rule() != internal::Rule::output {
                    Self::report_unexpected_pair(pair)
                }

                let mut pairs = pair.into_inner();

                let first_predicate = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
                let remaining_predicates: Vec<_> =
                    pairs.map(PredicateParser::translate_pair).collect();

                let mut predicates = vec![PredicateParser::translate_pair(first_predicate)];
                predicates.extend(remaining_predicates);

                Spec::Output { predicates }
            }
            internal::Rule::placeholder_declaration => {
                if pair.as_rule() != internal::Rule::placeholder_declaration {
                    Self::report_unexpected_pair(pair)
                }

                let mut pairs = pair.into_inner();

                let first_placeholder = pairs.next().unwrap_or_else(|| Self::report_missing_pair());
                let remaining_placeholders: Vec<_> =
                    pairs.map(PlaceholderParser::translate_pair).collect();

                let mut placeholders = vec![PlaceholderParser::translate_pair(first_placeholder)];
                placeholders.extend(remaining_placeholders);

                Spec::PlaceholderDeclaration { placeholders }
            }
            internal::Rule::annotated_formula => Spec::AnnotatedFormula(AnnotatedFormulaParser::translate_pair(pair)),
            _ => Self::report_unexpected_pair(pair),
        }
    }
}

pub struct UserGuideParser;

impl PestParser for UserGuideParser {
    type Node = UserGuide;

    type InternalParser = internal::Parser;
    type Rule = internal::Rule;
    const RULE: Self::Rule = internal::Rule::user_guide;

    fn translate_pair(pair: pest::iterators::Pair<'_, Self::Rule>) -> Self::Node {
        if pair.as_rule() != internal::Rule::user_guide {
            Self::report_unexpected_pair(pair)
        }

        let mut specs: Vec<Spec> = pair.into_inner().map(SpecParser::translate_pair).collect();

        let mut input_predicates = vec![];
        let mut output_predicates = vec![];
        let mut assumptions = vec![];
        let mut placeholders = vec![];
        for s in specs.drain(..) {
            match s {
                Spec::Input { predicates: mut predicates } => {
                    for p in predicates.drain(..) {
                        input_predicates.push(p);
                    }
                }
                Spec::Output { predicates: mut predicates } => {
                    for p in predicates.drain(..) {
                        output_predicates.push(p);
                    }
                }
                Spec::AnnotatedFormula(f) => assumptions.push(f),
                Spec::PlaceholderDeclaration { placeholders: mut spec_phs } => {
                    for p in spec_phs.drain(..) {
                        placeholders.push(p)
                    }
                }
            }
        }

        UserGuide {
            input_predicates,
            output_predicates,
            placeholders,
            assumptions,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use {
        super::{
            AtomParser, AtomicFormulaParser, BasicIntegerTermParser, BinaryConnectiveParser,
            BinaryOperatorParser, ComparisonParser, FormulaParser, GeneralTermParser, GuardParser,
            IntegerTermParser, PlaceholderParser, PredicateParser,
            QuantificationParser, QuantifierParser, RelationParser, SpecParser,
            SpecificationParser, TheoryParser, UnaryConnectiveParser, UnaryOperatorParser,
            VariableParser, 
        },
        crate::{
            parsing::TestedParser,
            syntax_tree::fol::{
                Atom, AtomicFormula, BasicIntegerTerm, BinaryConnective, BinaryOperator,
                Comparison, Direction, Formula, GeneralTerm, Guard, IntegerTerm,
                Placeholder, Predicate, Quantification, Quantifier, Relation, Sort, Spec,
                Specification, Theory, UnaryConnective, UnaryOperator, Variable,
            },
        },
    };

    #[test]
    fn parse_basic_integer_term() {
        BasicIntegerTermParser
            .should_parse_into([
                ("#inf", BasicIntegerTerm::Infimum),
                ("#sup", BasicIntegerTerm::Supremum),
                ("0", BasicIntegerTerm::Numeral(0)),
                ("1", BasicIntegerTerm::Numeral(1)),
                ("-1", BasicIntegerTerm::Numeral(-1)),
                ("-48", BasicIntegerTerm::Numeral(-48)),
                ("301", BasicIntegerTerm::Numeral(301)),
                ("A$i", BasicIntegerTerm::IntegerVariable("A".into())),
                ("Avar$", BasicIntegerTerm::IntegerVariable("Avar".into())),
            ])
            .should_reject(["00", "-0", "#", "#infi", "#supa", "_", "1_", "A"]);
    }

    #[test]
    fn parse_unary_operator() {
        UnaryOperatorParser.should_parse_into([("-", UnaryOperator::Negative)]);
    }

    #[test]
    fn parse_binary_operator() {
        BinaryOperatorParser.should_parse_into([
            ("+", BinaryOperator::Add),
            ("-", BinaryOperator::Subtract),
            ("*", BinaryOperator::Multiply),
        ]);
    }

    #[test]
    fn parse_integer_term() {
        IntegerTermParser
            .should_parse_into([
                (
                    "#inf",
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Infimum),
                ),
                (
                    "#sup",
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Supremum),
                ),
                (
                    "0",
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(0)),
                ),
                (
                    "1",
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)),
                ),
                (
                    "-1",
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(-1)),
                ),
                (
                    "(-48)",
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(-48)),
                ),
                (
                    "-X$i",
                    IntegerTerm::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(
                            "X".into(),
                        ))
                        .into(),
                    },
                ),
                (
                    "(301)",
                    IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(301)),
                ),
                (
                    "1 + 3 + 2",
                    IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Add,
                            lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                            rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(3)).into(),
                        }
                        .into(),
                        rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(2)).into(),
                    },
                ),
            ])
            .should_reject(["00", "#", "#infi", "#supa", "_", "1_", "(1", "X"]);
    }

    #[test]
    fn parse_general_term() {
        GeneralTermParser
            .should_parse_into([
                (
                    "#inf",
                    GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                        BasicIntegerTerm::Infimum,
                    )),
                ),
                (
                    "#sup",
                    GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                        BasicIntegerTerm::Supremum,
                    )),
                ),
                (
                    "1",
                    GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                        BasicIntegerTerm::Numeral(1),
                    )),
                ),
                (
                    "(1)",
                    GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                        BasicIntegerTerm::Numeral(1),
                    )),
                ),
                (
                    "-1",
                    GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                        BasicIntegerTerm::Numeral(-1),
                    )),
                ),
                (
                    "-(1)",
                    GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                    }),
                ),
                (
                    "--1",
                    GeneralTerm::IntegerTerm(IntegerTerm::UnaryOperation {
                        op: UnaryOperator::Negative,
                        arg: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(-1)).into(),
                    }),
                ),
                (
                    "1 + 2",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                        rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(2)).into(),
                    }),
                ),
                ("a", GeneralTerm::Symbol("a".into())),
                ("ca_12", GeneralTerm::Symbol("ca_12".into())),
                ("_b12A", GeneralTerm::Symbol("_b12A".into())),
                ("A", GeneralTerm::GeneralVariable("A".into())),
                (
                    "1 + A$i",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                        rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(
                            "A".into(),
                        ))
                        .into(),
                    }),
                ),
                (
                    "(1 + Nx$i) * (Y$i - B1$i)",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Multiply,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Add,
                            lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                            rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(
                                "Nx".into(),
                            ))
                            .into(),
                        }
                        .into(),
                        rhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Subtract,
                            lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(
                                "Y".into(),
                            ))
                            .into(),
                            rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::IntegerVariable(
                                "B1".into(),
                            ))
                            .into(),
                        }
                        .into(),
                    }),
                ),
                (
                    "((1 + 2) - -3) * 4",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Multiply,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Subtract,
                            lhs: IntegerTerm::BinaryOperation {
                                op: BinaryOperator::Add,
                                lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1))
                                    .into(),
                                rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(2))
                                    .into(),
                            }
                            .into(),
                            rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(-3))
                                .into(),
                        }
                        .into(),
                        rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(4)).into(),
                    }),
                ),
                (
                    "1 + 2 * 3",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                        rhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(2)).into(),
                            rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(3)).into(),
                        }
                        .into(),
                    }),
                ),
                (
                    "1 * 2 + 3",
                    GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                        op: BinaryOperator::Add,
                        lhs: IntegerTerm::BinaryOperation {
                            op: BinaryOperator::Multiply,
                            lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(1)).into(),
                            rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(2)).into(),
                        }
                        .into(),
                        rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(3)).into(),
                    }),
                ),
            ])
            .should_reject([
                "(a)",
                "-a",
                "(A)",
                "1 + A",
                "1 + a",
                "1-",
                "1 +",
                "+1",
                "+ 1",
                "1..",
                "..1",
                "(1 + a",
                "1 + a)",
                "(1 (+ a +) 1)",
            ]);
    }

    #[test]
    fn parse_predicate() {
        PredicateParser
            .should_parse_into([
                (
                    "p/1",
                    Predicate {
                        symbol: "p".into(),
                        arity: 1,
                    },
                ),
                (
                    "_p/1",
                    Predicate {
                        symbol: "_p".into(),
                        arity: 1,
                    },
                ),
                (
                    "p/0",
                    Predicate {
                        symbol: "p".to_string(),
                        arity: 0,
                    },
                ),
                (
                    "composite/3",
                    Predicate {
                        symbol: "composite".to_string(),
                        arity: 3,
                    },
                ),
            ])
            .should_reject(["p", "1/1", "p/00", "p/01", "_/1", "p/p"]);
    }

    #[test]
    fn parse_atom() {
        AtomParser
            .should_parse_into([
                (
                    "p",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                ),
                (
                    // Parsing "g" caused issues ealier because "g" is also a sort declaration.
                    "g",
                    Atom {
                        predicate_symbol: "g".into(),
                        terms: vec![],
                    },
                ),
                (
                    "p()",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    },
                ),
                (
                    "p(1)",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::Numeral(1),
                        ))],
                    },
                ),
                (
                    "p(1, 2)",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![
                            GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::Numeral(1),
                            )),
                            GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::Numeral(2),
                            )),
                        ],
                    },
                ),
                (
                    "p(X, a)",
                    Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![
                            GeneralTerm::GeneralVariable("X".into()),
                            GeneralTerm::Symbol("a".into()),
                        ],
                    },
                ),
            ])
            .should_reject(["p(1,)", "1", "P", "p("]);
    }

    #[test]
    fn parse_relation() {
        RelationParser
            .should_parse_into([
                ("<", Relation::Less),
                (">", Relation::Greater),
                ("<=", Relation::LessEqual),
                (">=", Relation::GreaterEqual),
                ("!=", Relation::NotEqual),
                ("=", Relation::Equal),
            ])
            .should_reject(["< =", "< =", "less"]);
    }

    #[test]
    fn parse_guard() {
        GuardParser
            .should_parse_into([(
                "< N$g",
                Guard {
                    relation: Relation::Less,
                    term: GeneralTerm::GeneralVariable("N".into()),
                },
            )])
            .should_reject(["< 3 =", "="]);
    }

    #[test]
    fn parse_binary_connective() {
        BinaryConnectiveParser
            .should_parse_into([
                ("and", BinaryConnective::Conjunction),
                ("or", BinaryConnective::Disjunction),
                ("->", BinaryConnective::Implication),
                ("<-", BinaryConnective::ReverseImplication),
                ("<->", BinaryConnective::Equivalence),
            ])
            .should_reject(["<=", "< ->", "<- >", "anda", "And", "o r"]);
    }

    #[test]
    fn parse_comparison() {
        ComparisonParser
            .should_parse_into([(
                "p < 5",
                Comparison {
                    term: GeneralTerm::Symbol("p".into()),
                    guards: vec![Guard {
                        relation: Relation::Less,
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::Numeral(5),
                        )),
                    }],
                },
            )])
            .should_reject(["A < B < "]);
    }

    #[test]
    fn parse_atomic_formula() {
        AtomicFormulaParser
            .should_parse_into([
                ("#true", AtomicFormula::Truth),
                ("#false", AtomicFormula::Falsity),
                (
                    "1 = N$g",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::Numeral(1),
                        )),
                        guards: vec![Guard {
                            relation: Relation::Equal,
                            term: GeneralTerm::GeneralVariable("N".into()),
                        }],
                    }),
                ),
                (
                    "1 = N$",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::Numeral(1),
                        )),
                        guards: vec![Guard {
                            relation: Relation::Equal,
                            term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::IntegerVariable("N".into()),
                            )),
                        }],
                    }),
                ),
                (
                    "n > 1",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::Symbol("n".to_string()),
                        guards: vec![Guard {
                            relation: Relation::Greater,
                            term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::Numeral(1),
                            )),
                        }],
                    }),
                ),
                (
                    "1 <= N$g > 3 < X$i",
                    AtomicFormula::Comparison(Comparison {
                        term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                            BasicIntegerTerm::Numeral(1),
                        )),
                        guards: vec![
                            Guard {
                                relation: Relation::LessEqual,
                                term: GeneralTerm::GeneralVariable("N".into()),
                            },
                            Guard {
                                relation: Relation::Greater,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                    BasicIntegerTerm::Numeral(3),
                                )),
                            },
                            Guard {
                                relation: Relation::Less,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                    BasicIntegerTerm::IntegerVariable("X".into()),
                                )),
                            },
                        ],
                    }),
                ),
                (
                    "p(N$i, 3*2)",
                    AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![
                            GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                BasicIntegerTerm::IntegerVariable("N".into()),
                            )),
                            GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                                op: BinaryOperator::Multiply,
                                lhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(3))
                                    .into(),
                                rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(2))
                                    .into(),
                            }),
                        ],
                    }),
                ),
            ])
            .should_reject(["p and b"]);
    }

    #[test]
    fn parse_unary_connective() {
        UnaryConnectiveParser
            .should_parse_into([("not", UnaryConnective::Negation)])
            .should_reject(["noto", "not(", "n ot"]);
    }

    #[test]
    fn parse_quantifier() {
        QuantifierParser
            .should_parse_into([
                ("forall", Quantifier::Forall),
                ("exists", Quantifier::Exists),
            ])
            .should_reject(["fora", "exis", "ex ists", "forall1", "exists("]);
    }

    #[test]
    fn parse_variable() {
        VariableParser
            .should_parse_into([
                (
                    "X",
                    Variable {
                        name: "X".into(),
                        sort: Sort::General,
                    },
                ),
                (
                    "G1",
                    Variable {
                        name: "G1".into(),
                        sort: Sort::General,
                    },
                ),
                (
                    "X$i",
                    Variable {
                        name: "X".into(),
                        sort: Sort::Integer,
                    },
                ),
                (
                    "X$",
                    Variable {
                        name: "X".into(),
                        sort: Sort::Integer,
                    },
                ),
                (
                    "Y$g",
                    Variable {
                        name: "Y".into(),
                        sort: Sort::General,
                    },
                ),
            ])
            .should_reject(["X$k", "X $i", "$i", "$g", "a$g"]);
    }

    #[test]
    fn parse_quantification() {
        QuantificationParser
            .should_parse_into([
                (
                    "exists X",
                    Quantification {
                        quantifier: Quantifier::Exists,
                        variables: vec![Variable {
                            name: "X".into(),
                            sort: Sort::General,
                        }],
                    },
                ),
                (
                    "forall X$i Y Z$g",
                    Quantification {
                        quantifier: Quantifier::Forall,
                        variables: vec![
                            Variable {
                                name: "X".into(),
                                sort: Sort::Integer,
                            },
                            Variable {
                                name: "Y".into(),
                                sort: Sort::General,
                            },
                            Variable {
                                name: "Z".into(),
                                sort: Sort::General,
                            },
                        ],
                    },
                ),
                (
                    "exists G1 G1$i",
                    Quantification {
                        quantifier: Quantifier::Exists,
                        variables: vec![
                            Variable {
                                name: "G1".into(),
                                sort: Sort::General,
                            },
                            Variable {
                                name: "G1".into(),
                                sort: Sort::Integer,
                            },
                        ],
                    },
                ),
            ])
            .should_reject([
                "forall",
                "exists ",
                "exists aA",
                "forall X$k",
                "exists X$i$g",
            ]);
    }

    #[test]
    fn parse_formula() {
        FormulaParser.should_parse_into([
            (
                "not p",
                Formula::UnaryFormula {
                    connective: UnaryConnective::Negation,
                    formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "p".into(),
                        terms: vec![],
                    }))
                    .into(),
                },
            ),
            (
                "forall A p(A) -> q",
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: Quantifier::Forall,
                            variables: vec![Variable {
                                name: "A".into(),
                                sort: Sort::General,
                            }],
                        },
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![GeneralTerm::GeneralVariable("A".into())],
                        }))
                        .into(),
                    }
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "q".into(),
                        terms: vec![],
                    }))
                    .into(),
                },
            ),
            (
                "forall A (p(A)) -> #false",
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: Quantifier::Forall,
                            variables: vec![Variable {
                                name: "A".into(),
                                sort: Sort::General,
                            }],
                        },
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![GeneralTerm::GeneralVariable("A".into())],
                        }))
                        .into(),
                    }
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
                },
            ),
            (
                "forall A (p(A)) -> #true",
                Formula::BinaryFormula {
                    connective: BinaryConnective::Implication,
                    lhs: Formula::QuantifiedFormula {
                        quantification: Quantification {
                            quantifier: Quantifier::Forall,
                            variables: vec![Variable {
                                name: "A".into(),
                                sort: Sort::General,
                            }],
                        },
                        formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![GeneralTerm::GeneralVariable("A".into())],
                        }))
                        .into(),
                    }
                    .into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Truth).into(),
                },
            ),
            (
                "#true or #false",
                Formula::BinaryFormula {
                    connective: BinaryConnective::Disjunction,
                    lhs: Formula::AtomicFormula(AtomicFormula::Truth).into(),
                    rhs: Formula::AtomicFormula(AtomicFormula::Falsity).into(),
                },
            ),
            (
                "forall V1 V2 (not not ra(V1, V2) -> ra(V1, V2))",
                Formula::QuantifiedFormula {
                    quantification: Quantification {
                        quantifier: Quantifier::Forall,
                        variables: vec![
                            Variable {
                                name: "V1".into(),
                                sort: Sort::General,
                            },
                            Variable {
                                name: "V2".into(),
                                sort: Sort::General,
                            },
                        ],
                    },
                    formula: Formula::BinaryFormula {
                        connective: BinaryConnective::Implication,
                        lhs: Formula::UnaryFormula {
                            connective: UnaryConnective::Negation,
                            formula: Formula::UnaryFormula {
                                connective: UnaryConnective::Negation,
                                formula: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "ra".to_string(),
                                    terms: vec![
                                        GeneralTerm::GeneralVariable("V1".into()),
                                        GeneralTerm::GeneralVariable("V2".into()),
                                    ],
                                }))
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                        rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "ra".to_string(),
                            terms: vec![
                                GeneralTerm::GeneralVariable("V1".into()),
                                GeneralTerm::GeneralVariable("V2".into()),
                            ],
                        }))
                        .into(),
                    }
                    .into(),
                },
            ),
            (
                "exists X$i G(p(G, X$i+30) <-> q or r and t)",
                Formula::QuantifiedFormula {
                    quantification: Quantification {
                        quantifier: Quantifier::Exists,
                        variables: vec![
                            Variable {
                                name: "X".into(),
                                sort: Sort::Integer,
                            },
                            Variable {
                                name: "G".into(),
                                sort: Sort::General,
                            },
                        ],
                    },
                    formula: Formula::BinaryFormula {
                        connective: BinaryConnective::Equivalence,
                        lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                            predicate_symbol: "p".into(),
                            terms: vec![
                                GeneralTerm::GeneralVariable("G".into()),
                                GeneralTerm::IntegerTerm(IntegerTerm::BinaryOperation {
                                    op: BinaryOperator::Add,
                                    lhs: IntegerTerm::BasicIntegerTerm(
                                        BasicIntegerTerm::IntegerVariable("X".into()),
                                    )
                                    .into(),
                                    rhs: IntegerTerm::BasicIntegerTerm(BasicIntegerTerm::Numeral(
                                        30,
                                    ))
                                    .into(),
                                }),
                            ],
                        }))
                        .into(),
                        rhs: Formula::BinaryFormula {
                            connective: BinaryConnective::Disjunction,
                            lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                predicate_symbol: "q".into(),
                                terms: vec![],
                            }))
                            .into(),
                            rhs: Formula::BinaryFormula {
                                connective: BinaryConnective::Conjunction,
                                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "r".into(),
                                    terms: vec![],
                                }))
                                .into(),
                                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "t".into(),
                                    terms: vec![],
                                }))
                                .into(),
                            }
                            .into(),
                        }
                        .into(),
                    }
                    .into(),
                },
            ),
        ]);
    }

    #[test]
    fn parse_theory() {
        TheoryParser.should_parse_into([
            ("", Theory { formulas: vec![] }),
            (
                "a.\n",
                Theory {
                    formulas: vec![Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "a".into(),
                        terms: vec![],
                    }))],
                },
            ),
            (
                "% First comment. \na. %%%% Second comment %%%%\n%Last comment",
                Theory {
                    formulas: vec![Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                        predicate_symbol: "a".into(),
                        terms: vec![],
                    }))],
                },
            ),
        ]);
    }

    #[test]
    fn parse_placeholder() {
        PlaceholderParser
            .should_parse_into([(
                "n -> integer",
                Placeholder {
                    name: "n".to_string(),
                    sort: Sort::Integer,
                },
            )])
            .should_reject(["n -> int"]);
    }

    #[test]
    fn parse_lemma() {
        LemmaParser
            .should_parse_into([
                (
                    "lemma: a > 1.",
                    Lemma {
                        origin: Origin {name: None, forget: false},
                        direction: Direction::Universal,
                        formula: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                            term: GeneralTerm::Symbol("a".to_string()),
                            guards: vec![Guard {
                                relation: Relation::Greater,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                    BasicIntegerTerm::Numeral(1),
                                )),
                            }],
                        })),
                    },
                ),
                (
                    "lemma(forward): a > 1.",
                    Lemma {
                        origin: Origin {name: None, forget: false},
                        direction: Direction::Forward,
                        formula: Formula::AtomicFormula(AtomicFormula::Comparison(Comparison {
                            term: GeneralTerm::Symbol("a".to_string()),
                            guards: vec![Guard {
                                relation: Relation::Greater,
                                term: GeneralTerm::IntegerTerm(IntegerTerm::BasicIntegerTerm(
                                    BasicIntegerTerm::Numeral(1),
                                )),
                            }],
                        })),
                    },
                ),
                (
                    "lemma(backward): #false.",
                    Lemma {
                        origin: Origin {name: None, forget: false},
                        direction: Direction::Backward,
                        formula: Formula::AtomicFormula(AtomicFormula::Falsity),
                    },
                ),
            ])
            .should_reject(["lemma: X", "lemma: a > 1"]);
    }

    #[test]
    fn parse_spec() {
        SpecParser
            .should_parse_into([
                (
                    "input: p/0.",
                    Spec::Input {
                        predicates: vec![Predicate {
                            symbol: "p".to_string(),
                            arity: 0,
                        }],
                    },
                ),
                (
                    "output: p/0, composite/3, prime/10.",
                    Spec::Output {
                        predicates: vec![
                            Predicate {
                                symbol: "p".to_string(),
                                arity: 0,
                            },
                            Predicate {
                                symbol: "composite".to_string(),
                                arity: 3,
                            },
                            Predicate {
                                symbol: "prime".to_string(),
                                arity: 10,
                            },
                        ],
                    },
                ),
                (
                    "input: a -> general, bar -> integer.",
                    Spec::PlaceholderDeclaration {
                        placeholders: vec![
                            Placeholder {
                                name: "a".to_string(),
                                sort: Sort::General,
                            },
                            Placeholder {
                                name: "bar".to_string(),
                                sort: Sort::Integer,
                            },
                        ],
                    },
                ),
                (
                    "assume: #false.",
                    Spec::Assumption {
                        formula: Formula::AtomicFormula(AtomicFormula::Falsity),
                    },
                ),
                (
                    "spec: forall X (p(X) <-> q(X)).",
                    Spec::Conjecture {
                        formula: Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Forall,
                                variables: vec![Variable {
                                    name: "X".to_string(),
                                    sort: Sort::General,
                                }],
                            },
                            formula: Formula::BinaryFormula {
                                connective: BinaryConnective::Equivalence,
                                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "p".to_string(),
                                    terms: vec![GeneralTerm::GeneralVariable("X".to_string())],
                                }))
                                .into(),
                                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "q".to_string(),
                                    terms: vec![GeneralTerm::GeneralVariable("X".to_string())],
                                }))
                                .into(),
                            }
                            .into(),
                        },
                    },
                ),
                (
                    "lemma: forall X (p(X) <-> q(X)).",
                    Spec::Lemma(Lemma {
                        origin: Origin {name: None, forget: false},
                        direction: Direction::Universal,
                        formula: Formula::QuantifiedFormula {
                            quantification: Quantification {
                                quantifier: Quantifier::Forall,
                                variables: vec![Variable {
                                    name: "X".to_string(),
                                    sort: Sort::General,
                                }],
                            },
                            formula: Formula::BinaryFormula {
                                connective: BinaryConnective::Equivalence,
                                lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "p".to_string(),
                                    terms: vec![GeneralTerm::GeneralVariable("X".to_string())],
                                }))
                                .into(),
                                rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                    predicate_symbol: "q".to_string(),
                                    terms: vec![GeneralTerm::GeneralVariable("X".to_string())],
                                }))
                                .into(),
                            }
                            .into(),
                        },
                    }),
                ),
            ])
            .should_reject(["p/0", "input: p/1 q/2."]);
    }

    #[test]
    fn parse_specification() {
        SpecificationParser
            .should_parse_into([
                (
                    "output: p/0. assume: #true.\ninput: n -> general.",
                    Specification {
                        specs: vec![
                            Spec::Output {
                                predicates: vec![Predicate {
                                    symbol: "p".to_string(),
                                    arity: 0,
                                }],
                            },
                            Spec::Assumption {
                                formula: Formula::AtomicFormula(AtomicFormula::Truth),
                            },
                            Spec::PlaceholderDeclaration {
                                placeholders: vec![Placeholder {
                                    name: "n".to_string(),
                                    sort: Sort::General,
                                }],
                            },
                        ],
                    },
                ),
                (
                    "input: n -> integer. output: prime/1. assume: n > 1.",
                    Specification {
                        specs: vec![
                            Spec::PlaceholderDeclaration {
                                placeholders: vec![Placeholder {
                                    name: "n".to_string(),
                                    sort: Sort::Integer,
                                }],
                            },
                            Spec::Output {
                                predicates: vec![Predicate {
                                    symbol: "prime".to_string(),
                                    arity: 1,
                                }],
                            },
                            Spec::Assumption {
                                formula: Formula::AtomicFormula(AtomicFormula::Comparison(
                                    Comparison {
                                        term: GeneralTerm::Symbol("n".to_string()),
                                        guards: vec![Guard {
                                            relation: Relation::Greater,
                                            term: GeneralTerm::IntegerTerm(
                                                IntegerTerm::BasicIntegerTerm(
                                                    BasicIntegerTerm::Numeral(1),
                                                ),
                                            ),
                                        }],
                                    },
                                )),
                            },
                        ],
                    },
                ),
                (
                    "lemma(forward): a > 1.",
                    Specification {
                        specs: vec![Spec::Lemma(Lemma {
                            origin: Origin {name: None, forget: false},
                            direction: Direction::Forward,
                            formula: Formula::AtomicFormula(AtomicFormula::Comparison(
                                Comparison {
                                    term: GeneralTerm::Symbol("a".to_string()),
                                    guards: vec![Guard {
                                        relation: Relation::Greater,
                                        term: GeneralTerm::IntegerTerm(
                                            IntegerTerm::BasicIntegerTerm(
                                                BasicIntegerTerm::Numeral(1),
                                            ),
                                        ),
                                    }],
                                },
                            )),
                        })],
                    },
                ),
                (
                    "lemma(forward)[positive_a]: a > 0.\nlemma(backward)[negative_b]: b < 0.\nlemma[c_equals_0]: c = 0.",
                    Specification {
                        specs: vec![
                            Spec::Lemma(Lemma {
                                origin: Origin {name: Some("positive_a".to_string()), forget: false},
                                direction: Direction::Forward,
                                formula: Formula::AtomicFormula(AtomicFormula::Comparison(
                                    Comparison {
                                        term: GeneralTerm::Symbol("a".to_string()),
                                        guards: vec![Guard {
                                            relation: Relation::Greater,
                                            term: GeneralTerm::IntegerTerm(
                                                IntegerTerm::BasicIntegerTerm(
                                                    BasicIntegerTerm::Numeral(0),
                                                ),
                                            ),
                                        }],
                                    },
                                )),
                            }),
                            Spec::Lemma(Lemma {
                                origin: Origin {name: Some("negative_b".to_string()), forget: false},
                                direction: Direction::Backward,
                                formula: Formula::AtomicFormula(AtomicFormula::Comparison(
                                    Comparison {
                                        term: GeneralTerm::Symbol("b".to_string()),
                                        guards: vec![Guard {
                                            relation: Relation::Less,
                                            term: GeneralTerm::IntegerTerm(
                                                IntegerTerm::BasicIntegerTerm(
                                                    BasicIntegerTerm::Numeral(0),
                                                ),
                                            ),
                                        }],
                                    },
                                )),
                            }),
                            Spec::Lemma(Lemma {
                                origin: Origin {name: Some("c_equals_0".to_string()), forget: false},
                                direction: Direction::Universal,
                                formula: Formula::AtomicFormula(AtomicFormula::Comparison(
                                    Comparison {
                                        term: GeneralTerm::Symbol("c".to_string()),
                                        guards: vec![Guard {
                                            relation: Relation::Equal,
                                            term: GeneralTerm::IntegerTerm(
                                                IntegerTerm::BasicIntegerTerm(
                                                    BasicIntegerTerm::Numeral(0),
                                                ),
                                            ),
                                        }],
                                    },
                                )),
                            }),
                        ],
                    },
                ),
                (
                    "assume: #true. lemma: forall X (p(X) <-> q(X)).",
                    Specification {
                        specs: vec![
                            Spec::Assumption {
                                formula: Formula::AtomicFormula(AtomicFormula::Truth),
                            },
                            Spec::Lemma(Lemma {
                                origin: Origin {name: None, forget: false},
                                direction: Direction::Universal,
                                formula: Formula::QuantifiedFormula {
                                    quantification: Quantification {
                                        quantifier: Quantifier::Forall,
                                        variables: vec![Variable {
                                            name: "X".to_string(),
                                            sort: Sort::General,
                                        }],
                                    },
                                    formula: Formula::BinaryFormula {
                                        connective: BinaryConnective::Equivalence,
                                        lhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                            predicate_symbol: "p".to_string(),
                                            terms: vec![GeneralTerm::GeneralVariable(
                                                "X".to_string(),
                                            )],
                                        }))
                                        .into(),
                                        rhs: Formula::AtomicFormula(AtomicFormula::Atom(Atom {
                                            predicate_symbol: "q".to_string(),
                                            terms: vec![GeneralTerm::GeneralVariable(
                                                "X".to_string(),
                                            )],
                                        }))
                                        .into(),
                                    }
                                    .into(),
                                },
                            }),
                        ],
                    },
                ),
            ])
            .should_reject(["output: p/0, assumption: #true."]);
    }
}
