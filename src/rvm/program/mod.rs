// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod core;
mod listing;
mod recompile;
mod rule_tree;
mod serialization;
mod types;

pub use core::Program;
pub use listing::{
    generate_assembly_listing, generate_tabular_assembly_listing, AssemblyListingConfig,
};
pub(crate) use serialization::value::{binaries_to_values, BinaryValue};
pub use serialization::{DeserializationResult, VersionedProgram};
pub use types::{
    BuiltinInfo, FunctionInfo, ProgramMetadata, RuleInfo, RuleType, SourceFile, SpanInfo,
};
