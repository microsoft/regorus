// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};

use super::span::EmptySpan;

/// Attribute reference like @Request[namespace:attribute]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct AttributeReference {
    #[serde(skip)]
    pub span: EmptySpan,
    pub source: AttributeSource,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub namespace: Option<String>,
    pub attribute: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub path: Vec<AttributePathSegment>,
}

/// Source of an attribute reference
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AttributeSource {
    Request,
    Resource,
    Principal,
    Environment,
    Context,
}

/// A segment of an attribute path (e.g. metadata, 0, category)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AttributePathSegment {
    Key(String),
    Index(usize),
}
