// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;

/// Error returned during condition evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConditionEvalError {
    message: String,
}

impl ConditionEvalError {
    pub(crate) fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl core::fmt::Display for ConditionEvalError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.message)
    }
}
