// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Entrypoint metadata captured during type analysis.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

/// Reachability information for requested entrypoints.
#[derive(Clone, Debug, Default)]
pub struct EntrypointSummary {
    pub requested: Vec<String>,
    pub reachable: BTreeSet<String>,
    pub included_defaults: BTreeSet<String>,
    pub dynamic_refs: Vec<DynamicLookupPattern>,
}

/// Pattern describing dynamic lookups discovered during analysis.
#[derive(Clone, Debug, Default)]
pub struct DynamicLookupPattern {
    pub static_prefix: Vec<String>,
    pub pattern: String,
}
