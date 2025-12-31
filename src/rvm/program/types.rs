// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use alloc::string::String;
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};

/// Builtin function information stored in program's builtin info table
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuiltinInfo {
    /// Builtin function name
    pub name: String,
    /// Exact number of arguments required
    pub num_args: u16,
}

/// Span information for debugging and error reporting
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SpanInfo {
    /// Index into the source table
    pub source_index: usize,
    /// Line number (1-based)
    pub line: usize,
    /// Column number (1-based)
    pub column: usize,
    /// Length of the span
    pub length: usize,
}

impl SpanInfo {
    pub const fn new(source_index: usize, line: usize, column: usize, length: usize) -> Self {
        Self {
            source_index,
            line,
            column,
            length,
        }
    }

    /// Create SpanInfo from lexer Span with source table lookup
    pub fn from_lexer_span(span: &crate::lexer::Span, source_index: usize) -> Self {
        Self {
            source_index,
            line: span.line.try_into().unwrap_or(usize::MAX),
            column: span.col.try_into().unwrap_or(usize::MAX),
            length: span.text().len(),
        }
    }

    /// Get source information using the program's source table
    pub fn get_source<'a>(&self, source_table: &'a [SourceFile]) -> Option<&'a str> {
        source_table
            .get(self.source_index)
            .map(|s| s.content.as_str())
    }

    /// Get source name using the program's source table
    pub fn get_source_name<'a>(&self, source_table: &'a [SourceFile]) -> Option<&'a str> {
        source_table.get(self.source_index).map(|s| s.name.as_str())
    }
}

/// Rule type enumeration for different kinds of rules (complete, partial set, partial object)
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, PartialOrd, Eq, Ord)]
pub enum RuleType {
    Complete,
    PartialSet,
    PartialObject,
}

/// Information about function rules
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionInfo {
    /// Parameter names in order
    pub param_names: Vec<String>,
    /// Number of parameters
    pub num_params: u32,
}

/// Rule metadata for debugging and introspection
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuleInfo {
    /// Rule name (e.g., "data.package.rule_name")
    pub name: String,
    /// Rule type
    pub rule_type: RuleType,
    /// Definitions
    pub definitions: crate::Rc<Vec<Vec<u32>>>,
    /// Function-specific information (only present for function rules)
    pub function_info: Option<FunctionInfo>,
    /// Index into the program's literal table for default value (only for Complete rules)
    pub default_literal_index: Option<u16>,
    /// Register allocated for this rule's result accumulation
    pub result_reg: u8,
    /// Number of registers used by this rule (for register windowing)
    pub num_registers: u8,
    /// Optional destructuring block entry point per definition
    /// Index: definition_index → Some(entry_point) | None
    pub destructuring_blocks: Vec<Option<u32>>,
}

impl RuleInfo {
    pub fn new(
        name: String,
        rule_type: RuleType,
        definitions: crate::Rc<Vec<Vec<u32>>>,
        result_reg: u8,
        num_registers: u8,
    ) -> Self {
        let num_definitions = definitions.len();
        Self {
            name,
            rule_type,
            definitions,
            function_info: None,
            default_literal_index: None,
            result_reg,
            num_registers,
            destructuring_blocks: alloc::vec![None; num_definitions],
        }
    }

    /// Create a new function rule with parameter information
    pub fn new_function(
        name: String,
        rule_type: RuleType,
        definitions: crate::Rc<Vec<Vec<u32>>>,
        param_names: Vec<String>,
        result_reg: u8,
        num_registers: u8,
    ) -> Self {
        let num_params = u32::try_from(param_names.len()).unwrap_or(u32::MAX);
        let num_definitions = definitions.len();
        Self {
            name,
            rule_type,
            definitions,
            function_info: Some(FunctionInfo {
                param_names,
                num_params,
            }),
            default_literal_index: None,
            result_reg,
            num_registers,
            destructuring_blocks: alloc::vec![None; num_definitions],
        }
    }

    /// Set the default literal index for this rule
    pub const fn set_default_literal_index(&mut self, default_literal_index: u16) {
        self.default_literal_index = Some(default_literal_index);
    }
}

/// Source file information containing filename and contents
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SourceFile {
    /// Source file identifier/path
    pub name: String,
    /// The actual source code content
    pub content: String,
}

impl SourceFile {
    pub const fn new(name: String, content: String) -> Self {
        Self { name, content }
    }
}

/// Program compilation metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProgramMetadata {
    /// Compiler version that generated this program
    pub compiler_version: String,
    /// Compilation timestamp
    pub compiled_at: String,
    /// Source policy information
    pub source_info: String,
    /// Optimization level used
    pub optimization_level: u8,
}
