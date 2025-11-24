// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::String;

#[derive(thiserror::Error, Debug)]
pub enum CompilerError {
    #[error("Not a builtin function: {name}")]
    NotBuiltinFunction { name: String },

    #[error("Unknown builtin function: {name}")]
    UnknownBuiltinFunction { name: String },

    #[error("internal: missing context for yield")]
    MissingYieldContext,

    #[error(
        "Direct access to 'data' root is not allowed. Use a specific path like 'data.package.rule'"
    )]
    DirectDataAccess,

    #[error("Not a simple reference chain")]
    NotSimpleReferenceChain,

    #[error("Missing binding plan for {context}")]
    MissingBindingPlan { context: String },

    #[error("Unexpected binding plan variant for {context}: {found}")]
    UnexpectedBindingPlan { context: String, found: String },

    #[error("Invalid destructuring pattern in assignment")]
    InvalidDestructuringPattern,

    #[error("Unsupported expression type in chained reference")]
    UnsupportedChainedExpression,

    #[error("internal: no rule type found for '{rule_path}'")]
    RuleTypeNotFound { rule_path: String },

    #[error("unary - can only be used with numeric literals")]
    InvalidUnaryMinus,

    #[error("Unknown function: '{name}'")]
    UnknownFunction { name: String },

    #[error("Undefined variable: '{name}'")]
    UndefinedVariable { name: String },

    #[error("SomeIn should have been hoisted as a loop")]
    SomeInNotHoisted,

    #[error("Invalid function expression")]
    InvalidFunctionExpression,

    #[error("Invalid function expression with package")]
    InvalidFunctionExpressionWithPackage,

    #[error("Compilation error: {message}")]
    General { message: String },
}

impl From<anyhow::Error> for CompilerError {
    fn from(err: anyhow::Error) -> Self {
        CompilerError::General {
            message: format!("{}", err),
        }
    }
}

pub type Result<T> = ::core::result::Result<T, CompilerError>;
