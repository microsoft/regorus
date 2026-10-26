// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use super::super::metadata::ProgramMetadata;
use super::super::types::{BuiltinInfo, FunctionInfo, RuleInfo, RuleType, SourceFile, SpanInfo};
use super::Program;
use crate::rvm::instructions::InstructionData;
use crate::rvm::Instruction;
use crate::value::Value;

#[derive(serde::Serialize)]
struct FlatRuleInfoV6<'a> {
    name: &'a String,
    rule_type: &'a RuleType,
    definitions: &'a crate::Rc<Vec<Vec<u32>>>,
    function_info: &'a Option<FunctionInfo>,
    default_literal_index: Option<u16>,
    result_reg: u8,
    num_registers: u8,
    destructuring_blocks: &'a Vec<Option<u32>>,
    else_bodies: &'a Vec<Vec<bool>>,
    early_exit_on_first_success: bool,
}

impl Program {
    /// Serialize to JSON format with complete program information and proper field names
    pub fn serialize_json(&self) -> Result<String, String> {
        self.validate_limits()?;
        let has_runtime_defaults = self.rule_infos.iter().any(|rule_info| {
            rule_info.default_entry_point.is_some() || rule_info.default_is_indexed
        });
        let rule_infos = if has_runtime_defaults {
            serde_json::to_value(&self.rule_infos)
                .map_err(|error| format!("Rule info JSON serialization failed: {error}"))?
        } else {
            let rule_infos: Vec<_> = self
                .rule_infos
                .iter()
                .map(|rule_info| FlatRuleInfoV6 {
                    name: &rule_info.name,
                    rule_type: &rule_info.rule_type,
                    definitions: &rule_info.definitions,
                    function_info: &rule_info.function_info,
                    default_literal_index: rule_info.default_literal_index,
                    result_reg: rule_info.result_reg,
                    num_registers: rule_info.num_registers,
                    destructuring_blocks: &rule_info.destructuring_blocks,
                    else_bodies: &rule_info.else_bodies,
                    early_exit_on_first_success: rule_info.early_exit_on_first_success,
                })
                .collect();
            serde_json::to_value(rule_infos)
                .map_err(|error| format!("Rule info JSON serialization failed: {error}"))?
        };
        let json_data = serde_json::json!({
            "metadata": {
                "compiler_version": self.metadata.compiler_version,
                "compiled_at": self.metadata.compiled_at,
                "source_info": self.metadata.source_info,
                "optimization_level": self.metadata.optimization_level,
                "rego_v0": self.rego_v0,
                "needs_runtime_recursion_check": self.needs_runtime_recursion_check,
                "has_host_await": self.has_host_await,
                "needs_recompilation": self.needs_recompilation,
                "language": self.metadata.language,
                "annotations": self.metadata.annotations
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
            "rule_infos": rule_infos,
            "instruction_spans": self.instruction_spans,
            "rule_tree": self.rule_tree
        });

        let output_data = if has_runtime_defaults {
            serde_json::json!({
                "version": Self::SERIALIZATION_VERSION,
                "program": json_data
            })
        } else {
            json_data
        };

        serde_json::to_string_pretty(&output_data)
            .map_err(|e| format!("JSON serialization failed: {}", e))
    }

    /// Deserialize program from JSON format
    pub fn deserialize_json(data: &str) -> Result<Program, String> {
        let parsed_json: serde_json::Value =
            serde_json::from_str(data).map_err(|e| format!("JSON parsing failed: {}", e))?;
        let json_data = if let Some(version) = parsed_json.get("version") {
            let version = version
                .as_u64()
                .and_then(|value| u32::try_from(value).ok())
                .ok_or("Invalid JSON program version")?;
            if version != Self::SERIALIZATION_VERSION {
                return Err(format!("Unsupported JSON program version {version}"));
            }
            parsed_json
                .get("program")
                .cloned()
                .ok_or("Missing program section in versioned JSON")?
        } else {
            parsed_json
        };

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
        let language = metadata
            .get("language")
            .and_then(|v| v.as_str())
            .unwrap_or("")
            .to_string();
        #[allow(clippy::needless_borrowed_reference)]
        let annotations: alloc::collections::BTreeMap<String, Value> = match metadata
            .get("annotations")
        {
            Some(&serde_json::Value::Object(ref map)) => {
                let mut result = alloc::collections::BTreeMap::new();
                for (k, json_val) in map {
                    let val = serde_json::from_value::<Value>(json_val.clone())
                        .map_err(|e| format!("Annotation '{}' deserialization failed: {}", k, e))?;
                    result.insert(k.clone(), val);
                }
                result
            }
            _ => alloc::collections::BTreeMap::new(),
        };
        let rego_v0 = metadata
            .get("rego_v0")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let needs_runtime_recursion_check = metadata
            .get("needs_runtime_recursion_check")
            .and_then(|v| v.as_bool())
            .unwrap_or(false);
        let has_host_await = metadata
            .get("has_host_await")
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

        let entry_points = json_data
            .get("entry_points")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let sources: Vec<SourceFile> = json_data
            .get("sources")
            .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
            .unwrap_or_default();

        let rule_infos: Vec<RuleInfo> = match json_data.get("rule_infos") {
            Some(value) => serde_json::from_value(value.clone())
                .map_err(|error| format!("Failed to deserialize rule_infos: {error}"))?,
            None => Vec::new(),
        };

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
                language,
                annotations,
            },
            rule_tree,
            resolved_builtins: Vec::new(),
            needs_runtime_recursion_check,
            has_host_await,
            needs_recompilation,
            rego_v0,
        };

        // Recompute has_host_await when it was not provided in the JSON input
        // or when the provided value is not a valid boolean.
        if json_data
            .get("metadata")
            .and_then(|m| m.get("has_host_await").and_then(|v| v.as_bool()))
            .is_none()
        {
            program.recompute_host_await_presence();
        }

        if !program.builtin_info_table.is_empty() {
            let _ = program.initialize_resolved_builtins();
        }

        program.validate_limits()?;

        Ok(program)
    }
}
