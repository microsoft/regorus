// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use super::super::types::SourceFile;
use super::super::types::{BuiltinInfo, ProgramMetadata, RuleInfo, SpanInfo};
use super::Program;
use crate::rvm::instructions::InstructionData;
use crate::rvm::Instruction;
use crate::value::Value;
use indexmap::IndexMap;

impl Program {
    /// Serialize to JSON format with complete program information and proper field names
    pub fn serialize_json(&self) -> Result<String, String> {
        let json_data = serde_json::json!({
            "metadata": {
                "compiler_version": self.metadata.compiler_version,
                "compiled_at": self.metadata.compiled_at,
                "source_info": self.metadata.source_info,
                "optimization_level": self.metadata.optimization_level,
                "rego_v0": self.rego_v0,
                "needs_runtime_recursion_check": self.needs_runtime_recursion_check,
                "needs_recompilation": self.needs_recompilation
            },
            "program_structure": {
                "main_entry_point": self.main_entry_point,
                "max_rule_window_size": self.max_rule_window_size,
                "dispatch_window_size": self.dispatch_window_size,
            },
            "instructions": self.instructions,
            "instruction_data": {
                "loop_params": self.instruction_data.loop_params,
                "builtin_call_params": self.instruction_data.builtin_call_params,
                "function_call_params": self.instruction_data.function_call_params,
                "object_create_params": self.instruction_data.object_create_params,
                "array_create_params": self.instruction_data.array_create_params,
                "set_create_params": self.instruction_data.set_create_params,
                "virtual_data_document_lookup_params": self.instruction_data.virtual_data_document_lookup_params,
                "chained_index_params": self.instruction_data.chained_index_params,
                "comprehension_begin_params": self.instruction_data.comprehension_begin_params
            },
            "literals": self.literals,
            "builtin_info_table": self.builtin_info_table,
            "entry_points": self.entry_points,
            "sources": self.sources,
            "rule_infos": self.rule_infos,
            "instruction_spans": self.instruction_spans,
            "rule_tree": self.rule_tree
        });

        serde_json::to_string_pretty(&json_data)
            .map_err(|e| format!("JSON serialization failed: {}", e))
    }

    /// Deserialize program from JSON format
    pub fn deserialize_json(data: &str) -> Result<Program, String> {
        let json_data: serde_json::Value =
            serde_json::from_str(data).map_err(|e| format!("JSON parsing failed: {}", e))?;

        let metadata = json_data
            .get("metadata")
            .ok_or("Missing metadata section")?;
        let compiler_version = metadata
            .get("compiler_version")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string();
        let compiled_at = metadata
            .get("compiled_at")
            .and_then(|v| v.as_str())
            .unwrap_or("unknown")
            .to_string();
        let source_info = metadata
            .get("source_info")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        let optimization_level = metadata
            .get("optimization_level")
            .and_then(|v| v.as_u64())
            .and_then(|v| u8::try_from(v).ok())
            .unwrap_or(0);
        let rego_v0 = metadata
            .get("rego_v0")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let needs_runtime_recursion_check = metadata
            .get("needs_runtime_recursion_check")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let needs_recompilation = metadata
            .get("needs_recompilation")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);

        let program_structure = json_data
            .get("program_structure")
            .ok_or("Missing program_structure section")?;
        let main_entry_point = program_structure
            .get("main_entry_point")
            .and_then(|v| v.as_u64())
            .and_then(|v| u32::try_from(v).ok())
            .unwrap_or(0);
        let max_rule_window_size = program_structure
            .get("max_rule_window_size")
            .and_then(|v| v.as_u64())
            .and_then(|v| u8::try_from(v).ok())
            .unwrap_or(0);
        let dispatch_window_size = program_structure
            .get("dispatch_window_size")
            .and_then(|v| v.as_u64())
            .and_then(|v| u8::try_from(v).ok())
            .unwrap_or(0);

        let instructions: Vec<Instruction> = serde_json::from_value(
            json_data
                .get("instructions")
                .ok_or("Missing instructions section")?
                .clone(),
        )
        .map_err(|e| format!("Failed to deserialize instructions: {}", e))?;

        let instruction_data_json = json_data
            .get("instruction_data")
            .ok_or("Missing instruction_data section")?;
        let instruction_data: InstructionData =
            serde_json::from_value(instruction_data_json.clone())
                .map_err(|e| format!("Failed to deserialize instruction_data: {}", e))?;

        let literals: Vec<Value> = json_data
            .get("literals")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let builtin_info_table: Vec<BuiltinInfo> = json_data
            .get("builtin_info_table")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let entry_points: IndexMap<String, usize> = json_data
            .get("entry_points")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let sources: Vec<SourceFile> = json_data
            .get("sources")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let rule_infos: Vec<RuleInfo> = json_data
            .get("rule_infos")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let instruction_spans: Vec<Option<SpanInfo>> = json_data
            .get("instruction_spans")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let rule_tree: Value = json_data
            .get("rule_tree")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_else(|_| Value::new_object()))
            .unwrap_or_else(Value::new_object);

        let mut program = Program {
            instructions,
            literals,
            instruction_data,
            builtin_info_table,
            entry_points,
            sources,
            rule_infos,
            instruction_spans,
            main_entry_point,
            max_rule_window_size,
            dispatch_window_size,
            metadata: ProgramMetadata {
                compiler_version,
                compiled_at,
                source_info,
                optimization_level,
            },
            rule_tree,
            resolved_builtins: Vec::new(),
            needs_runtime_recursion_check,
            needs_recompilation,
            rego_v0,
        };

        if !program.builtin_info_table.is_empty() {
            let _ = program.initialize_resolved_builtins();
        }

        Ok(program)
    }
}
