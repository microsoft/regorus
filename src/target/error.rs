// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::{format, Rc};
use core::fmt;

type String = Rc<str>;

/// Error type for target parsing operations.
#[derive(Debug, Clone)]
pub enum TargetError {
    /// JSON parsing error
    JsonParseError(String),
    /// Target deserialization error
    DeserializationError(String),
    /// Duplicate constant value error
    DuplicateConstantValue(String),
    /// Multiple default resource schemas error
    MultipleDefaultSchemas(String),
    /// Empty resource schemas error
    EmptyResourceSchemas(String),
    /// Empty effect schemas error
    EmptyEffectSchemas(String),
}

impl fmt::Display for TargetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TargetError::*;

        let description = match self {
            JsonParseError(msg) => format!("JSON parse error: {}", msg),
            DeserializationError(msg) => format!("Deserialization error: {}", msg),
            DuplicateConstantValue(msg) => format!("Duplicate constant value: {}", msg),
            MultipleDefaultSchemas(msg) => format!("Multiple default schemas: {}", msg),
            EmptyResourceSchemas(msg) => format!("Empty resource schemas: {}", msg),
            EmptyEffectSchemas(msg) => format!("Empty effect schemas: {}", msg),
        };

        write!(f, "{}", description)
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TargetError {}

impl From<serde_json::Error> for TargetError {
    fn from(error: serde_json::Error) -> Self {
        TargetError::JsonParseError(format!("{}", error).into())
    }
}
