// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use super::super::metadata::ProgramMetadata;
use super::super::types::{BuiltinInfo, RuleInfo, SourceFile, SpanInfo};
use super::Program;
use crate::rvm::instructions::InstructionData;
use crate::rvm::Instruction;
use crate::value::{Object, Value};
use indexmap::IndexMap;
use serde_json::{Map as JsonMap, Value as JsonValue};

const PROGRAM_JSON_VALUE_ENCODING: &str = "typed-keys-v1";

fn needs_program_json_value_encoding(node: &Value) -> bool {
    match *node {
        Value::Undefined | Value::Set(_) => true,
        Value::Array(ref items) => items.iter().any(needs_program_json_value_encoding),
        Value::Object(ref fields) => fields.iter_sorted().any(|(key, value)| {
            !matches!(key, Value::String(_))
                || needs_program_json_value_encoding(key)
                || needs_program_json_value_encoding(value)
        }),
        Value::Null | Value::Bool(_) | Value::Number(_) | Value::String(_) => false,
    }
}

fn program_json_memory_check(field: &str) -> Result<(), String> {
    crate::utils::limits::check_memory_limit_if_needed()
        .map_err(|error| format!("Program JSON `{field}` allocation failed: {error}"))
}

fn encode_program_json_value(node: &Value, field: &str) -> Result<JsonValue, String> {
    match *node {
        Value::Null => Ok(JsonValue::Null),
        Value::Bool(value) => Ok(JsonValue::Bool(value)),
        Value::Number(ref value) => serde_json::to_value(value)
            .map_err(|error| format!("Program JSON `{field}` number encoding failed: {error}")),
        Value::String(ref value) => Ok(JsonValue::String(value.to_string())),
        Value::Array(ref values) => {
            let mut encoded = Vec::with_capacity(values.len());
            for value in values.iter() {
                encoded.push(encode_program_json_value(value, field)?);
                program_json_memory_check(field)?;
            }
            Ok(JsonValue::Array(encoded))
        }
        Value::Set(ref values) => {
            let mut encoded_values = Vec::with_capacity(values.len());
            for value in values.iter_sorted() {
                encoded_values.push(encode_program_json_value(value, field)?);
                program_json_memory_check(field)?;
            }

            let mut marker = JsonMap::new();
            marker.insert("$set".to_string(), JsonValue::Array(encoded_values));
            Ok(JsonValue::Object(marker))
        }
        Value::Object(ref fields) => {
            let mut encoded_fields = JsonMap::new();
            for (key, value) in fields.iter_sorted() {
                let encoded_key = encode_program_json_value(key, field)?;
                let encoded_key = serde_json::to_string(&encoded_key).map_err(|error| {
                    format!("Program JSON `{field}` object-key encoding failed: {error}")
                })?;
                let encoded_value = encode_program_json_value(value, field)?;
                if encoded_fields
                    .insert(encoded_key.clone(), encoded_value)
                    .is_some()
                {
                    return Err(format!(
                        "Program JSON `{field}` has duplicate encoded object key {encoded_key}"
                    ));
                }
                program_json_memory_check(field)?;
            }
            Ok(JsonValue::Object(encoded_fields))
        }
        Value::Undefined => {
            let mut marker = JsonMap::new();
            marker.insert("$undefined".to_string(), JsonValue::Null);
            Ok(JsonValue::Object(marker))
        }
    }
}

fn decode_program_json_value(node: &JsonValue, field: &str) -> Result<Value, String> {
    match *node {
        JsonValue::Null => Ok(Value::Null),
        JsonValue::Bool(value) => Ok(Value::Bool(value)),
        JsonValue::Number(_) => serde_json::from_value(node.clone())
            .map_err(|error| format!("Program JSON `{field}` number decoding failed: {error}")),
        JsonValue::String(ref value) => Ok(Value::from(value.as_str())),
        JsonValue::Array(ref values) => {
            let mut decoded = Vec::with_capacity(values.len());
            for value in values {
                decoded.push(decode_program_json_value(value, field)?);
                program_json_memory_check(field)?;
            }
            let decoded = Value::from(decoded);
            program_json_memory_check(field)?;
            Ok(decoded)
        }
        JsonValue::Object(ref fields) => {
            let undefined = fields.get("$undefined");
            let set = fields.get("$set");
            match (undefined, set) {
                (Some(payload), None) => {
                    if fields.len() != 1 || !payload.is_null() {
                        return Err(format!(
                            "Program JSON `{field}` has a malformed $undefined sentinel"
                        ));
                    }
                    return Ok(Value::Undefined);
                }
                (None, Some(payload)) => {
                    if fields.len() != 1 {
                        return Err(format!(
                            "Program JSON `{field}` has a malformed $set sentinel"
                        ));
                    }
                    let values = payload.as_array().ok_or_else(|| {
                        format!("Program JSON `{field}` $set payload must be an array")
                    })?;
                    let mut decoded = BTreeSet::new();
                    for value in values {
                        let value = decode_program_json_value(value, field)?;
                        if !decoded.insert(value) {
                            return Err(format!(
                                "Program JSON `{field}` $set payload contains a duplicate value"
                            ));
                        }
                        program_json_memory_check(field)?;
                    }
                    let decoded = Value::from(decoded);
                    program_json_memory_check(field)?;
                    return Ok(decoded);
                }
                (Some(_), Some(_)) => {
                    return Err(format!(
                        "Program JSON `{field}` object cannot contain both $undefined and $set"
                    ));
                }
                (None, None) => {}
            }

            let mut decoded = Object::new();
            for (encoded_key, encoded_value) in fields {
                let encoded_key: JsonValue =
                    serde_json::from_str(encoded_key).map_err(|error| {
                        format!(
                            "Program JSON `{field}` contains an invalid encoded object key \
                         {encoded_key:?}: {error}"
                        )
                    })?;
                let key = decode_program_json_value(&encoded_key, field)?;
                let value = decode_program_json_value(encoded_value, field)?;
                if decoded.insert(key, value).is_some() {
                    return Err(format!(
                        "Program JSON `{field}` contains duplicate decoded object keys"
                    ));
                }
                program_json_memory_check(field)?;
            }
            let decoded = Value::from(decoded);
            program_json_memory_check(field)?;
            Ok(decoded)
        }
    }
}

fn decode_program_json_literals(node: &JsonValue) -> Result<Vec<Value>, String> {
    let values = node
        .as_array()
        .ok_or("Program JSON `literals` field must be an array")?;
    let mut literals = Vec::with_capacity(values.len());
    for value in values {
        literals.push(decode_program_json_value(value, "literals")?);
        program_json_memory_check("literals")?;
    }
    Ok(literals)
}

impl Program {
    /// Serialize to JSON format with complete program information and proper field names
    pub fn serialize_json(&self) -> Result<String, String> {
        let use_value_encoding = self.literals.iter().any(needs_program_json_value_encoding)
            || needs_program_json_value_encoding(&self.rule_tree);
        let literals = if use_value_encoding {
            let mut values = Vec::with_capacity(self.literals.len());
            for value in &self.literals {
                values.push(encode_program_json_value(value, "literals")?);
                program_json_memory_check("literals")?;
            }
            JsonValue::Array(values)
        } else {
            serde_json::to_value(&self.literals)
                .map_err(|error| format!("Program JSON `literals` serialization failed: {error}"))?
        };
        let rule_tree = if use_value_encoding {
            encode_program_json_value(&self.rule_tree, "rule_tree")?
        } else {
            serde_json::to_value(&self.rule_tree).map_err(|error| {
                format!("Program JSON `rule_tree` serialization failed: {error}")
            })?
        };

        let mut json_data = serde_json::json!({
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
            "builtin_info_table": self.builtin_info_table,
            "entry_points": self.entry_points,
            "sources": self.sources,
            "rule_infos": self.rule_infos,
            "instruction_spans": self.instruction_spans
        });
        let json_fields = json_data
            .as_object_mut()
            .ok_or("Program JSON root must be an object")?;
        json_fields.insert("literals".to_string(), literals);
        json_fields.insert("rule_tree".to_string(), rule_tree);
        if use_value_encoding {
            json_fields.insert(
                "value_encoding".to_string(),
                JsonValue::String(PROGRAM_JSON_VALUE_ENCODING.to_string()),
            );
        }

        serde_json::to_string_pretty(&json_data)
            .map_err(|e| format!("JSON serialization failed: {}", e))
    }

    /// Deserialize program from JSON format
    pub fn deserialize_json(data: &str) -> Result<Program, String> {
        let json_data: serde_json::Value =
            serde_json::from_str(data).map_err(|e| format!("JSON parsing failed: {}", e))?;
        let use_value_encoding = match json_data.get("value_encoding") {
            None => false,
            Some(encoding) => match encoding.as_str() {
                Some(PROGRAM_JSON_VALUE_ENCODING) => true,
                Some(encoding) => {
                    return Err(format!(
                        "Unsupported Program JSON `value_encoding` marker: {encoding}"
                    ));
                }
                None => {
                    return Err("Program JSON `value_encoding` marker must be a string".to_string());
                }
            },
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

        let literals: Vec<Value> = if use_value_encoding {
            let encoded_literals = json_data
                .get("literals")
                .ok_or("Program JSON `literals` field is missing")?;
            decode_program_json_literals(encoded_literals)
                .map_err(|error| format!("Program JSON `literals` decoding failed: {error}"))?
        } else {
            json_data
                .get("literals")
                .map(|v| serde_json::from_value(v.clone()).unwrap_or_default())
                .unwrap_or_default()
        };

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

        let rule_tree: Value = if use_value_encoding {
            let encoded_rule_tree = json_data
                .get("rule_tree")
                .ok_or("Program JSON `rule_tree` field is missing")?;
            decode_program_json_value(encoded_rule_tree, "rule_tree")
                .map_err(|error| format!("Program JSON `rule_tree` decoding failed: {error}"))?
        } else {
            json_data
                .get("rule_tree")
                .map(|v| serde_json::from_value(v.clone()).unwrap_or_else(|_| Value::new_object()))
                .unwrap_or_else(Value::new_object)
        };

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

        Ok(program)
    }
}
