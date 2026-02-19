#![allow(clippy::missing_const_for_fn, clippy::pattern_type_mismatch)]
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;
use serde::{Deserialize, Serialize};

/// Array operator descriptor (e.g. ANY, ForAnyOfAnyValues:StringEquals)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ArrayOperator {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub modifier: Option<String>,
}
