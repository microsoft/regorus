// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod core;
mod history;
mod listing;
mod metadata;
mod recompile;
mod rule_tree;
mod serialization;
mod types;

pub use core::Program;
pub use history::{
    HistoryField, HistoryHeadSource, HistoryPairSource, HistoryRegexSource, HistoryTermSource,
    HistoryTestSource,
};
pub use listing::{
    generate_assembly_listing, generate_tabular_assembly_listing, AssemblyListingConfig,
};
pub(crate) use serialization::value::{binaries_to_values, BinaryValue};
pub use serialization::{DeserializationResult, VersionedProgram};
pub use types::{
    BuiltinInfo, FunctionInfo, HistoryRuleMode, HistoryTable, HistoryTableRule, RuleInfo, RuleType,
    SourceFile, SpanInfo,
};

pub use metadata::ProgramMetadata;
