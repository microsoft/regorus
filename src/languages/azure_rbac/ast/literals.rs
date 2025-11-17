// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;
use serde::{Deserialize, Serialize};

use super::span::EmptySpan;

/// String literal value
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct StringLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
    pub value: String,
}

/// Number literal value (keeps raw representation)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NumberLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
    pub raw: String,
}

/// Boolean literal value
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct BooleanLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
    pub value: bool,
}

/// Null literal
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct NullLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
}

/// Date-time literal value (ISO-8601 formatted)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct DateTimeLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
    pub value: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalized: Option<String>,
}

/// Time literal value (HH:MM or HH:MM:SS)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TimeLiteral {
    #[serde(skip)]
    pub span: EmptySpan,
    pub value: String,
}
