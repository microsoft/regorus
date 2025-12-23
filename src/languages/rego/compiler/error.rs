// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

use alloc::format;
use alloc::string::String;

use crate::lexer::Span;
use core::fmt;

#[derive(thiserror::Error, Debug)]
pub enum CompilerError {
    #[error("Not a builtin function: {name}")]
    NotBuiltinFunction { name: String },

    #[error("Unknown builtin function: {name}")]
    UnknownBuiltinFunction { name: String },

    #[error("the `with` keyword is not supported by the compiler yet")]
    WithKeywordUnsupported,

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

#[derive(Debug)]
pub struct SpannedCompilerError {
    pub error: CompilerError,
    pub span: Option<Span>,
}

impl SpannedCompilerError {
    pub fn new(error: CompilerError) -> Self {
        Self { error, span: None }
    }

    pub fn with_span(mut self, span: &Span) -> Self {
        if self.span.is_none() {
            self.span = Some(span.clone());
        }
        self
    }
}

impl fmt::Display for SpannedCompilerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(span) = &self.span {
            let msg = format!("{}", self.error);
            write!(f, "{}", span.message("error", &msg))
        } else {
            write!(f, "{}", self.error)
        }
    }
}

impl From<CompilerError> for SpannedCompilerError {
    fn from(error: CompilerError) -> Self {
        Self::new(error)
    }
}

impl core::error::Error for SpannedCompilerError {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl CompilerError {
    pub fn at(self, span: &Span) -> SpannedCompilerError {
        SpannedCompilerError::from(self).with_span(span)
    }
}

pub type Result<T> = ::core::result::Result<T, SpannedCompilerError>;
