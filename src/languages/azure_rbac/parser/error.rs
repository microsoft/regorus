// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;

/// Error types for condition expression parsing
#[derive(Debug, Clone)]
pub enum ConditionParseError {
    InvalidExpression(String),
    UnsupportedCondition(String),
}

impl core::fmt::Display for ConditionParseError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ConditionParseError::InvalidExpression(msg) => {
                write!(f, "Invalid expression: {}", msg)
            }
            ConditionParseError::UnsupportedCondition(expr) => {
                write!(f, "Unsupported condition expression: {}", expr)
            }
        }
    }
}
