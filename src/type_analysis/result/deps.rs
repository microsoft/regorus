// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Rule dependency graph structures.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

/// Compact representation of the rule dependency graph produced by analysis.
#[derive(Clone, Debug, Default)]
pub struct DependencyGraph {
    pub edges: Vec<DependencyEdge>,
    pub sccs: Vec<Vec<String>>,
    pub recursive_rules: BTreeSet<String>,
}

/// Directed dependency between two rule paths.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DependencyEdge {
    pub source: String,
    pub target: String,
    pub kind: DependencyKind,
}

/// Classification of rule dependencies.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DependencyKind {
    StaticCall,
    DynamicCall,
    DefaultLink,
}
