// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Error types for Azure Policy JSON parsing.

use alloc::format;
use alloc::string::String;

use crate::lexer::Span;

/// Errors that can occur during Azure Policy JSON parsing.
#[derive(Debug)]
pub enum ParseError {
    /// Error from the lexer.
    Lexer(String),
    /// Unexpected token encountered.
    UnexpectedToken { span: Span, expected: &'static str },
    /// A required key is missing from a JSON object.
    MissingKey { span: Span, key: &'static str },
    /// An unrecognized key was found in a policy object.
    UnrecognizedKey { span: Span, key: String },
    /// Logical operator (`allOf`/`anyOf`/`not`) has extra keys.
    ExtraKeysInLogical { span: Span, operator: String },
    /// The `allOf`/`anyOf` value is not an array.
    LogicalOperatorNotArray { span: Span, operator: String },
    /// No operator specified in a condition.
    MissingOperator { span: Span },
    /// Multiple LHS operands (field + value, etc.).
    MultipleLhsOperands { span: Span },
    /// Missing LHS operand in a condition.
    MissingLhsOperand { span: Span },
    /// Error parsing an ARM template expression.
    ExprParse { span: Span, message: String },
    /// Both `field` and `value` in a count block.
    MultipleCountCollections { span: Span },
    /// Neither `field` nor `value` in a count block.
    MissingCountCollection { span: Span },
    /// `name` must be a string in count-value.
    InvalidCountName { span: Span },
    /// `name` used without `value` in count.
    MisplacedCountName { span: Span },
    /// Multiple operator keys in a single condition.
    MultipleOperators { span: Span },
    /// A duplicate key was found in a JSON object.
    DuplicateKey { span: Span, key: String },
    /// A custom error message (e.g., from sub-parsing).
    Custom { span: Span, message: String },
}

impl core::fmt::Display for ParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            ParseError::Lexer(ref msg) => write!(f, "{}", msg),
            ParseError::UnexpectedToken { ref span, expected } => {
                write!(f, "{}", span.error(&format!("expected {}", expected)))
            }
            ParseError::MissingKey { ref span, key } => {
                write!(
                    f,
                    "{}",
                    span.error(&format!("missing required key \"{}\"", key))
                )
            }
            ParseError::UnrecognizedKey { ref span, ref key } => {
                write!(
                    f,
                    "{}",
                    span.error(&format!("unrecognized key \"{}\"", key))
                )
            }
            ParseError::ExtraKeysInLogical {
                ref span,
                ref operator,
            } => write!(
                f,
                "{}",
                span.error(&format!(
                    "\"{}\" must be the only key in its object",
                    operator
                ))
            ),
            ParseError::LogicalOperatorNotArray {
                ref span,
                ref operator,
            } => {
                write!(
                    f,
                    "{}",
                    span.error(&format!("\"{}\" must be an array", operator))
                )
            }
            ParseError::MissingOperator { ref span } => {
                write!(f, "{}", span.error("no operator specified in condition"))
            }
            ParseError::MultipleLhsOperands { ref span } => {
                write!(
                    f,
                    "{}",
                    span.error("multiple LHS operands (field/value/count)")
                )
            }
            ParseError::MissingLhsOperand { ref span } => {
                write!(
                    f,
                    "{}",
                    span.error("missing LHS operand (field, value, or count)")
                )
            }
            ParseError::ExprParse {
                ref span,
                ref message,
            } => {
                write!(
                    f,
                    "{}\n  expression parse error: {}",
                    span.error("in template expression"),
                    message
                )
            }
            ParseError::MultipleCountCollections { ref span } => {
                write!(
                    f,
                    "{}",
                    span.error("both 'field' and 'value' specified in count")
                )
            }
            ParseError::MissingCountCollection { ref span } => {
                write!(
                    f,
                    "{}",
                    span.error("neither 'field' nor 'value' specified in count")
                )
            }
            ParseError::InvalidCountName { ref span } => {
                write!(f, "{}", span.error("'name' in count must be a string"))
            }
            ParseError::MisplacedCountName { ref span } => {
                write!(
                    f,
                    "{}",
                    span.error("'name' can only be used with count-value")
                )
            }
            ParseError::MultipleOperators { ref span } => {
                write!(
                    f,
                    "{}",
                    span.error("only one operator key allowed in a condition")
                )
            }
            ParseError::DuplicateKey { ref span, ref key } => {
                write!(f, "{}", span.error(&format!("duplicate key \"{}\"", key)))
            }
            ParseError::Custom {
                ref span,
                ref message,
            } => {
                write!(f, "{}", span.error(message))
            }
        }
    }
}
