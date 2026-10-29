// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::vm::VmError;
use alloc::string::String;
use thiserror::Error;

/// Errors produced while capturing or reporting explanations.
#[derive(Error, Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum ExplainError {
    /// A report was requested, but explanation capture was not enabled for
    /// the evaluation.
    #[error("explanations were not enabled for this evaluation")]
    NotEnabled,

    /// [`ExplanationScope::SingleEmission`](super::ExplanationScope::SingleEmission)
    /// selected an emission that the rule did not produce.
    #[error("emission index {index} is out of range for rule `{rule}` ({available} emissions)")]
    EmissionIndexOutOfRange {
        /// Fully qualified rule name.
        rule: String,
        /// The requested emission index.
        index: usize,
        /// Number of emissions the rule produced.
        available: usize,
    },

    /// The evaluation itself failed.
    #[error(transparent)]
    Vm(#[from] VmError),
}
