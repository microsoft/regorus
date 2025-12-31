// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use anyhow::Result as AnyResult;
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};

use super::types::{BuiltinInfo, ProgramMetadata, RuleInfo, SourceFile, SpanInfo};
use crate::builtins::BuiltinFcn;
use crate::rvm::instructions::InstructionData;
use crate::rvm::Instruction;
use crate::value::Value;

/// Complete compiled program containing all execution artifacts
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Program {
    /// Compiled bytecode instructions
    pub instructions: Vec<Instruction>,

    /// Literal value table (skipped in serde, serialized separately as JSON)
    #[serde(skip, default = "Vec::new")]
    pub literals: Vec<Value>,

    /// Complex instruction parameter data (for LoopStart, Call, etc.)
    pub instruction_data: InstructionData,

    /// Builtin function information table
    pub builtin_info_table: Vec<BuiltinInfo>,

    /// Entry points mapping with preserved insertion order (skipped in serde, serialized separately as JSON)
    #[serde(skip, default = "IndexMap::new")]
    pub entry_points: IndexMap<String, usize>,

    /// Source files table with content (skipped in serde, serialized separately as JSON)
    #[serde(skip, default = "Vec::new")]
    pub sources: Vec<SourceFile>,

    /// Rule metadata: rule_index -> rule information
    pub rule_infos: Vec<RuleInfo>,

    /// Span information for each instruction (for debugging)
    pub instruction_spans: Vec<Option<SpanInfo>>,

    /// Main program entry point
    pub main_entry_point: u32,

    /// Maximum register window size observed across all rule definitions
    pub max_rule_window_size: u8,

    /// Register window size needed for entry point dispatch
    pub dispatch_window_size: u8,

    /// Program metadata
    pub metadata: ProgramMetadata,

    /// Rule tree for efficient rule lookup (skipped in serde, serialized separately as JSON)
    /// Maps rule paths (e.g., "data.p1.r1") to rule indices
    /// Structure: {"p1": {"r1": rule_index}, "p2": {"p3": {"r2": rule_index}}}
    #[serde(skip, default = "Value::new_object")]
    pub rule_tree: Value,

    /// Resolved builtins - actual builtin function values fetched from interpreter's builtin map
    /// This field is skipped during serialization and reinitialized after deserialization
    #[serde(skip)]
    pub resolved_builtins: Vec<BuiltinFcn>,

    /// Flag indicating that VirtualDataDocumentLookup instruction was used and runtime recursion checking is needed
    pub needs_runtime_recursion_check: bool,

    /// Flag indicating that recompilation is needed due to partial deserialization failure
    /// This is set to true when the artifact section was successfully read but the extensible
    /// section failed to deserialize (e.g., due to version incompatibility)
    #[serde(default)]
    pub needs_recompilation: bool,

    /// Rego language version used for compilation (true for Rego v0, false for Rego v1)
    /// This must be preserved during recompilation to maintain policy semantics
    /// Serialized separately in the artifact section for guaranteed availability
    #[serde(skip, default)]
    pub rego_v0: bool,
}

impl Program {
    /// Current serialization format version
    pub const SERIALIZATION_VERSION: u32 = 3;
    /// Magic bytes to identify Regorus program files
    pub const MAGIC: [u8; 4] = *b"REGO";
    /// Maximum instructions supported (matches u16 jump targets)
    pub const MAX_INSTRUCTIONS: usize = 65_535; // u16::MAX
    /// Maximum literals supported (matches u16 literal indices)
    pub const MAX_LITERALS: usize = 65_535; // u16::MAX
    /// Generous cap for rules within a single policy bundle
    pub const MAX_RULES: usize = 4_000;
    /// Generous cap for exported entry points
    pub const MAX_ENTRY_POINTS: usize = 1_000;
    /// Generous cap for source/helper files
    pub const MAX_SOURCES: usize = 256;
    /// Generous cap for builtin declarations
    pub const MAX_BUILTINS: usize = 512;
    /// Maximum path depth for rule paths (e.g., data.a.b.c.d.rule)
    pub const MAX_PATH_DEPTH: usize = 32;

    /// Create a new empty program
    pub fn new() -> Self {
        Self {
            instructions: Vec::new(),
            literals: Vec::new(),
            instruction_data: InstructionData::new(),
            builtin_info_table: Vec::new(),
            entry_points: IndexMap::new(),
            sources: Vec::new(),
            rule_infos: Vec::new(),
            instruction_spans: Vec::new(),
            main_entry_point: 0,
            max_rule_window_size: 0,
            dispatch_window_size: 0,
            metadata: ProgramMetadata {
                compiler_version: env!("CARGO_PKG_VERSION").to_string(),
                compiled_at: "unknown".to_string(),
                source_info: "unknown".to_string(),
                optimization_level: 0,
            },
            rule_tree: Value::new_object(),
            resolved_builtins: Vec::new(),
            needs_runtime_recursion_check: false,
            needs_recompilation: false,
            rego_v0: false, // Default to Rego v1
        }
    }

    /// Validate that the program stays within supported bounds
    pub fn validate_limits(&self) -> Result<(), String> {
        if self.instructions.len() > Self::MAX_INSTRUCTIONS {
            return Err(format!(
                "Program exceeds max instructions ({} > {})",
                self.instructions.len(),
                Self::MAX_INSTRUCTIONS
            ));
        }

        if self.literals.len() > Self::MAX_LITERALS {
            return Err(format!(
                "Program exceeds max literals ({} > {})",
                self.literals.len(),
                Self::MAX_LITERALS
            ));
        }

        if self.rule_infos.len() > Self::MAX_RULES {
            return Err(format!(
                "Program exceeds max rules ({} > {})",
                self.rule_infos.len(),
                Self::MAX_RULES
            ));
        }

        if self.entry_points.len() > Self::MAX_ENTRY_POINTS {
            return Err(format!(
                "Program exceeds max entry points ({} > {})",
                self.entry_points.len(),
                Self::MAX_ENTRY_POINTS
            ));
        }

        if self.sources.len() > Self::MAX_SOURCES {
            return Err(format!(
                "Program exceeds max sources ({} > {})",
                self.sources.len(),
                Self::MAX_SOURCES
            ));
        }

        if self.builtin_info_table.len() > Self::MAX_BUILTINS {
            return Err(format!(
                "Program exceeds max builtins ({} > {})",
                self.builtin_info_table.len(),
                Self::MAX_BUILTINS
            ));
        }

        for params in &self.instruction_data.loop_params {
            let body_end = core::cmp::max(params.body_start, params.loop_end);
            if usize::from(body_end) > Self::MAX_INSTRUCTIONS {
                return Err("Loop offsets exceed supported instruction range".to_string());
            }
        }

        for params in &self.instruction_data.comprehension_begin_params {
            let body_end = core::cmp::max(params.body_start, params.comprehension_end);
            if usize::from(body_end) > Self::MAX_INSTRUCTIONS {
                return Err("Comprehension offsets exceed supported instruction range".to_string());
            }
        }

        for instr in &self.instructions {
            if let &crate::rvm::Instruction::LoopNext {
                body_start,
                loop_end,
            } = instr
            {
                let body_end = core::cmp::max(body_start, loop_end);
                if usize::from(body_end) > Self::MAX_INSTRUCTIONS {
                    return Err("LoopNext offsets exceed supported instruction range".to_string());
                }
            }
        }

        Ok(())
    }

    /// Add a source file and return its index
    pub fn add_source(&mut self, name: String, content: String) -> usize {
        let source_file = SourceFile::new(name.clone(), content);
        let index = self.sources.len();
        self.sources.push(source_file);
        index
    }

    /// Add loop parameters and return the index
    pub fn add_loop_params(&mut self, params: crate::rvm::instructions::LoopStartParams) -> u16 {
        self.instruction_data.add_loop_params(params)
    }

    /// Add comprehension begin parameters and return the index
    pub fn add_comprehension_begin_params(
        &mut self,
        params: crate::rvm::instructions::ComprehensionBeginParams,
    ) -> u16 {
        self.instruction_data.add_comprehension_begin_params(params)
    }

    /// Add builtin call parameters and return the index
    pub fn add_builtin_call_params(
        &mut self,
        params: crate::rvm::instructions::BuiltinCallParams,
    ) -> u16 {
        self.instruction_data.add_builtin_call_params(params)
    }

    /// Add function call parameters and return the index
    pub fn add_function_call_params(
        &mut self,
        params: crate::rvm::instructions::FunctionCallParams,
    ) -> u16 {
        self.instruction_data.add_function_call_params(params)
    }

    /// Add builtin info and return the index
    pub fn add_builtin_info(&mut self, builtin_info: BuiltinInfo) -> u16 {
        let index = self.builtin_info_table.len();
        self.builtin_info_table.push(builtin_info);
        u16::try_from(index).unwrap_or(u16::MAX)
    }

    /// Get builtin info by index
    pub fn get_builtin_info(&self, index: u16) -> Option<&BuiltinInfo> {
        self.builtin_info_table.get(usize::from(index))
    }

    /// Update loop parameters by index
    pub fn update_loop_params<F>(&mut self, params_index: u16, updater: F)
    where
        F: FnOnce(&mut crate::rvm::instructions::LoopStartParams),
    {
        if let Some(params) = self.instruction_data.get_loop_params_mut(params_index) {
            updater(params);
        }
    }

    /// Update comprehension begin parameters by index
    pub fn update_comprehension_begin_params<F>(&mut self, params_index: u16, updater: F)
    where
        F: FnOnce(&mut crate::rvm::instructions::ComprehensionBeginParams),
    {
        if let Some(params) = self
            .instruction_data
            .get_comprehension_begin_params_mut(params_index)
        {
            updater(params);
        }
    }

    /// Get detailed instruction display with parameter resolution
    pub fn display_instruction_with_params(&self, instruction: &Instruction) -> String {
        instruction.display_with_params(&self.instruction_data)
    }

    /// Add a source file directly and return its index
    pub fn add_source_file(&mut self, source_file: SourceFile) -> usize {
        for (i, existing) in self.sources.iter().enumerate() {
            if existing.name == source_file.name {
                return i;
            }
        }

        let index = self.sources.len();
        self.sources.push(source_file);
        index
    }

    /// Get source file by index
    pub fn get_source_file(&self, index: usize) -> Option<&SourceFile> {
        self.sources.get(index)
    }

    /// Get source content by index
    pub fn get_source(&self, index: usize) -> Option<&str> {
        self.sources.get(index).map(|s| s.content.as_str())
    }

    /// Get source name by index
    pub fn get_source_name(&self, index: usize) -> Option<&str> {
        self.sources.get(index).map(|s| s.name.as_str())
    }

    /// Get rule info by index
    pub fn get_rule_info(&self, rule_index: usize) -> Option<&RuleInfo> {
        self.rule_infos.get(rule_index)
    }

    /// Get span information for instruction
    pub fn get_instruction_span(&self, instruction_index: usize) -> Option<&SpanInfo> {
        self.instruction_spans
            .get(instruction_index)
            .and_then(|span| span.as_ref())
    }

    /// Add instruction with optional span
    pub fn add_instruction(&mut self, instruction: Instruction, span: Option<SpanInfo>) {
        self.instructions.push(instruction);
        self.instruction_spans.push(span);
    }

    /// Add literal value and return its index
    pub fn add_literal(&mut self, value: Value) -> usize {
        for (i, existing) in self.literals.iter().enumerate() {
            if existing == &value {
                return i;
            }
        }

        let index = self.literals.len();
        self.literals.push(value);
        index
    }

    /// Initialize resolved builtins directly from the BUILTINS HashMap
    /// This should be called after deserialization to populate the skipped field
    /// Returns an error if any required builtin is missing
    pub fn initialize_resolved_builtins(&mut self) -> AnyResult<()> {
        self.resolved_builtins.clear();
        self.resolved_builtins
            .reserve(self.builtin_info_table.len());

        for builtin_info in &self.builtin_info_table {
            if let Some(&builtin_fcn) = crate::builtins::BUILTINS.get(builtin_info.name.as_str()) {
                self.resolved_builtins.push(builtin_fcn);
            } else {
                return Err(anyhow::anyhow!(
                    "Missing builtin function: {}",
                    builtin_info.name
                ));
            }
        }

        Ok(())
    }

    /// Get resolved builtin function by index
    pub fn get_resolved_builtin(&self, index: u16) -> Option<&BuiltinFcn> {
        self.resolved_builtins.get(usize::from(index))
    }

    /// Check if resolved builtins are initialized
    pub fn has_resolved_builtins(&self) -> bool {
        !self.resolved_builtins.is_empty()
    }

    /// Add an entry point mapping from path to rule index
    pub fn add_entry_point(&mut self, path: String, rule_index: usize) {
        self.entry_points.insert(path, rule_index);
    }

    /// Get rule index for an entry point path
    pub fn get_entry_point(&self, path: &str) -> Option<usize> {
        self.entry_points.get(path).copied()
    }

    /// Get all entry points as IndexMap
    pub const fn get_entry_points(&self) -> &IndexMap<String, usize> {
        &self.entry_points
    }

    /// Check if recompilation is needed due to partial deserialization failure
    pub const fn needs_recompilation(&self) -> bool {
        self.needs_recompilation
    }

    /// Mark that recompilation is needed
    pub const fn set_needs_recompilation(&mut self, needs_recompilation: bool) {
        self.needs_recompilation = needs_recompilation;
    }

    /// Check if the program is fully functional (not needing recompilation)
    pub const fn is_fully_functional(&self) -> bool {
        !self.needs_recompilation
    }
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}
