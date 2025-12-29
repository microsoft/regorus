// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
pub mod binary;
mod json;
pub mod value;

use serde::{Deserialize, Serialize};

use super::Program;

/// Versioned program wrapper for serialization compatibility
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VersionedProgram {
    /// Format version for compatibility checking
    pub version: u32,
    /// The actual program data
    pub program: Program,
}

/// Result of program deserialization that explicitly indicates completeness
#[derive(Debug, Clone)]
pub enum DeserializationResult {
    /// Full deserialization was successful - program is fully functional
    Complete(Program),
    /// Only artifact section was deserialized - extensible sections failed
    /// The program contains entry_points and sources but requires recompilation
    Partial(Program),
}
