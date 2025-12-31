// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use serde::{Deserialize, Serialize};

/// Represents either a literal index or a register number for path components
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LiteralOrRegister {
    /// Index into the program's literal table
    Literal(u16),
    /// Register number containing the value
    Register(u8),
}

/// Loop execution modes for different Rego iteration constructs
#[repr(C)]
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum LoopMode {
    /// Any quantification: some x in arr, x := arr[_], etc.
    /// Succeeds if ANY iteration succeeds, exits early on first success
    Any,

    /// Every quantification: every x in arr
    /// Succeeds only if ALL iterations succeed, exits early on first failure
    Every,

    /// ForEach processing: processes all elements without early exit
    /// Used for set membership rules (contains), object rules, and complete rules
    /// where all candidates must be evaluated. Determined by output constness.
    ForEach,
}

/// Comprehension execution modes for different comprehension types
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComprehensionMode {
    /// Set comprehension: {expr | condition}
    /// Collects unique successful iterations into a set
    Set,
    /// Array comprehension: [expr | condition]
    /// Collects successful iterations into an array (preserves order)
    Array,
    /// Object comprehension: {key: value | condition}
    /// Collects successful key-value pairs into an object
    Object,
}
