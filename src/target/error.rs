// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::{format, Rc};

type String = Rc<str>;

/// Error type for target parsing operations.
#[derive(Debug, Clone, thiserror::Error)]
pub enum TargetError {
    /// JSON parsing error
    #[error("JSON parse error: {0}")]
    JsonParseError(String),
    /// Target deserialization error
    #[error("Deserialization error: {0}")]
    DeserializationError(String),
    /// Duplicate constant value error
    #[error("Duplicate constant value: {0}")]
    DuplicateConstantValue(String),
    /// Multiple default resource schemas error
    #[error("Multiple default schemas: {0}")]
    MultipleDefaultSchemas(String),
    /// Empty resource schemas error
    #[error("Empty resource schemas: {0}")]
    EmptyResourceSchemas(String),
    /// Empty effect schemas error
    #[error("Empty effect schemas: {0}")]
    EmptyEffectSchemas(String),
}

impl From<serde_json::Error> for TargetError {
    fn from(error: serde_json::Error) -> Self {
        TargetError::JsonParseError(format!("{}", error).into())
    }
}
