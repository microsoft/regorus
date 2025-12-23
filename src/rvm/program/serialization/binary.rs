// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::as_conversions,
    clippy::unused_trait_names
)]

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use bincode::config::standard;
use bincode::serde::{decode_from_slice, encode_to_vec};
use indexmap::IndexMap;

use super::super::types::SourceFile;
use super::{DeserializationResult, Program};
use crate::value::Value;

use super::value::{
    binaries_to_values, binary_to_value, BinaryValue, BinaryValueRef, BinaryValueSlice,
};
type ArtifactData = (IndexMap<String, usize>, Vec<SourceFile>, bool);

impl Program {
    /// Serialize program to binary format.
    /// Uses pure bincode for all sections now that `Value` supports serde.
    pub fn serialize_binary(&self) -> Result<Vec<u8>, String> {
        let mut buffer = Vec::new();

        buffer.extend_from_slice(&Self::MAGIC);
        buffer.extend_from_slice(&Self::SERIALIZATION_VERSION.to_le_bytes());

        let entry_points_bin = encode_to_vec(&self.entry_points, standard())
            .map_err(|e| format!("Entry points bincode serialization failed: {}", e))?;

        let sources_bin = encode_to_vec(&self.sources, standard())
            .map_err(|e| format!("Sources bincode serialization failed: {}", e))?;

        let literals_bin = encode_to_vec(BinaryValueSlice(self.literals.as_slice()), standard())
            .map_err(|e| format!("Literals bincode serialization failed: {}", e))?;

        let rule_tree_bin = encode_to_vec(BinaryValueRef(&self.rule_tree), standard())
            .map_err(|e| format!("Rule tree bincode serialization failed: {}", e))?;

        let binary_data = encode_to_vec(self, standard())
            .map_err(|e| format!("Program structure binary serialization failed: {}", e))?;

        buffer.extend_from_slice(&(entry_points_bin.len() as u32).to_le_bytes());
        buffer.extend_from_slice(&(sources_bin.len() as u32).to_le_bytes());
        buffer.extend_from_slice(&(literals_bin.len() as u32).to_le_bytes());
        buffer.extend_from_slice(&(rule_tree_bin.len() as u32).to_le_bytes());
        buffer.push(if self.rego_v0 { 1 } else { 0 });

        buffer.extend_from_slice(&entry_points_bin);
        buffer.extend_from_slice(&sources_bin);
        buffer.extend_from_slice(&literals_bin);
        buffer.extend_from_slice(&rule_tree_bin);

        buffer.extend_from_slice(&(binary_data.len() as u32).to_le_bytes());
        buffer.extend_from_slice(&binary_data);

        Ok(buffer)
    }

    /// Deserialize only the artifact section (entry_points and sources) from binary format
    pub fn deserialize_artifacts_only(data: &[u8]) -> Result<ArtifactData, String> {
        if data.len() < 9 {
            return Err("Data too short for artifact header".to_string());
        }

        if data[0..4] != Self::MAGIC {
            return Err("Invalid file format - magic number mismatch".to_string());
        }

        let version = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);

        match version {
            1 => {
                if data.len() < 17 {
                    return Err("Data too short for artifact header".to_string());
                }

                let entry_points_len =
                    u32::from_le_bytes([data[8], data[9], data[10], data[11]]) as usize;
                let sources_len =
                    u32::from_le_bytes([data[12], data[13], data[14], data[15]]) as usize;
                let rego_v0 = data[16] != 0;
                let entry_points_start = 17;
                let sources_start = entry_points_start + entry_points_len;
                let sources_end = sources_start + sources_len;

                if data.len() < sources_end {
                    return Err("Data truncated in artifact section".to_string());
                }

                let entry_points =
                    decode_from_slice(&data[entry_points_start..sources_start], standard())
                        .map(|(value, _)| value)
                        .unwrap_or_else(|_| IndexMap::new());

                let sources = decode_from_slice(&data[sources_start..sources_end], standard())
                    .map(|(value, _)| value)
                    .unwrap_or_else(|_| Vec::new());

                Ok((entry_points, sources, rego_v0))
            }
            2 | 3 => {
                if data.len() < 25 {
                    return Err("Data too short for artifact header".to_string());
                }

                let entry_points_len =
                    u32::from_le_bytes([data[8], data[9], data[10], data[11]]) as usize;
                let sources_len =
                    u32::from_le_bytes([data[12], data[13], data[14], data[15]]) as usize;
                let literals_len =
                    u32::from_le_bytes([data[16], data[17], data[18], data[19]]) as usize;
                let rule_tree_len =
                    u32::from_le_bytes([data[20], data[21], data[22], data[23]]) as usize;
                let rego_v0 = data[24] != 0;

                let entry_points_start = 25;
                let sources_start = entry_points_start + entry_points_len;
                let literals_start = sources_start + sources_len;
                let rule_tree_start = literals_start + literals_len;
                let rule_tree_end = rule_tree_start + rule_tree_len;

                if data.len() < rule_tree_end {
                    return Err("Data truncated in artifact section".to_string());
                }

                let entry_points =
                    decode_from_slice(&data[entry_points_start..sources_start], standard())
                        .map(|(value, _)| value)
                        .unwrap_or_else(|_| IndexMap::new());

                let sources = decode_from_slice(&data[sources_start..literals_start], standard())
                    .map(|(value, _)| value)
                    .unwrap_or_else(|_| Vec::new());

                Ok((entry_points, sources, rego_v0))
            }
            v => Err(format!("Unsupported version {}", v)),
        }
    }

    /// Deserialize program from binary format with version checking
    pub fn deserialize_binary(data: &[u8]) -> Result<DeserializationResult, String> {
        if data.len() < 9 {
            return Err("Data too short for header".to_string());
        }

        if data[0..4] != Self::MAGIC {
            return Err("Invalid file format - magic number mismatch".to_string());
        }

        let version = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);
        if version > Self::SERIALIZATION_VERSION {
            return Err(format!(
                "Unsupported version {}. Maximum supported version is {}",
                version,
                Self::SERIALIZATION_VERSION
            ));
        }

        match version {
            1 => {
                if data.len() < 25 {
                    return Err("Data too short for header".to_string());
                }

                let entry_points_len =
                    u32::from_le_bytes([data[8], data[9], data[10], data[11]]) as usize;
                let sources_len =
                    u32::from_le_bytes([data[12], data[13], data[14], data[15]]) as usize;
                let rego_v0 = data[16] != 0;
                let entry_points_start = 17;
                let sources_start = entry_points_start + entry_points_len;
                let binary_len_start = sources_start + sources_len;

                if data.len() < binary_len_start + 4 {
                    return Err("Data too short for binary length".to_string());
                }

                let binary_len = u32::from_le_bytes([
                    data[binary_len_start],
                    data[binary_len_start + 1],
                    data[binary_len_start + 2],
                    data[binary_len_start + 3],
                ]) as usize;

                let json_len_start = binary_len_start + 4 + binary_len;
                if data.len() < json_len_start + 4 {
                    return Err("Data too short for JSON length".to_string());
                }

                let json_len = u32::from_le_bytes([
                    data[json_len_start],
                    data[json_len_start + 1],
                    data[json_len_start + 2],
                    data[json_len_start + 3],
                ]) as usize;

                let total_expected = json_len_start + 4 + json_len;
                if data.len() < total_expected {
                    return Err("Data truncated".to_string());
                }

                let binary_start = binary_len_start + 4;
                let json_start = json_len_start + 4;

                let entry_points =
                    decode_from_slice(&data[entry_points_start..sources_start], standard())
                        .map(|(value, _)| value)
                        .map_err(|e| format!("Entry points deserialization failed: {}", e))?;

                let sources = decode_from_slice(&data[sources_start..binary_len_start], standard())
                    .map(|(value, _)| value)
                    .map_err(|e| format!("Sources deserialization failed: {}", e))?;

                let mut needs_recompilation = false;

                let mut program = match decode_from_slice::<Program, _>(
                    &data[binary_start..json_start],
                    standard(),
                ) {
                    Ok((prog, _)) => prog,
                    Err(_e) => {
                        needs_recompilation = true;
                        Program::new()
                    }
                };

                let (literals, rule_tree) = match serde_json::from_slice::<serde_json::Value>(
                    &data[json_start..json_start + json_len],
                ) {
                    Ok(combined) => {
                        let literals = combined
                            .get("literals")
                            .and_then(|v| serde_json::from_value::<Vec<Value>>(v.clone()).ok())
                            .unwrap_or_else(|| {
                                needs_recompilation = true;
                                Vec::new()
                            });

                        let rule_tree = combined
                            .get("rule_tree")
                            .and_then(|v| serde_json::from_value::<Value>(v.clone()).ok())
                            .unwrap_or_else(|| {
                                needs_recompilation = true;
                                Value::new_object()
                            });

                        (literals, rule_tree)
                    }
                    Err(_e) => {
                        needs_recompilation = true;
                        (Vec::new(), Value::new_object())
                    }
                };

                program.entry_points = entry_points;
                program.sources = sources;
                program.literals = literals;
                program.rule_tree = rule_tree;
                program.rego_v0 = rego_v0;
                program.needs_recompilation = needs_recompilation;

                if !program.builtin_info_table.is_empty() {
                    if let Err(_e) = program.initialize_resolved_builtins() {
                        program.needs_recompilation = true;
                    }
                }

                if program.needs_recompilation {
                    Ok(DeserializationResult::Partial(program))
                } else {
                    Ok(DeserializationResult::Complete(program))
                }
            }
            2 | 3 => {
                if data.len() < 29 {
                    return Err("Data too short for header".to_string());
                }

                let entry_points_len =
                    u32::from_le_bytes([data[8], data[9], data[10], data[11]]) as usize;
                let sources_len =
                    u32::from_le_bytes([data[12], data[13], data[14], data[15]]) as usize;
                let literals_len =
                    u32::from_le_bytes([data[16], data[17], data[18], data[19]]) as usize;
                let rule_tree_len =
                    u32::from_le_bytes([data[20], data[21], data[22], data[23]]) as usize;
                let rego_v0 = data[24] != 0;

                let entry_points_start = 25;
                let sources_start = entry_points_start + entry_points_len;
                let literals_start = sources_start + sources_len;
                let rule_tree_start = literals_start + literals_len;
                let binary_len_start = rule_tree_start + rule_tree_len;

                if data.len() < binary_len_start + 4 {
                    return Err("Data too short for binary length".to_string());
                }

                let binary_len = u32::from_le_bytes([
                    data[binary_len_start],
                    data[binary_len_start + 1],
                    data[binary_len_start + 2],
                    data[binary_len_start + 3],
                ]) as usize;

                let binary_start = binary_len_start + 4;
                let binary_end = binary_start + binary_len;

                if data.len() < binary_end {
                    return Err("Data truncated".to_string());
                }

                let entry_points =
                    decode_from_slice(&data[entry_points_start..sources_start], standard())
                        .map(|(value, _)| value)
                        .map_err(|e| format!("Entry points deserialization failed: {}", e))?;

                let sources = decode_from_slice(&data[sources_start..literals_start], standard())
                    .map(|(value, _)| value)
                    .map_err(|e| format!("Sources deserialization failed: {}", e))?;

                let mut needs_recompilation = false;

                let literals = match decode_from_slice::<Vec<BinaryValue>, _>(
                    &data[literals_start..rule_tree_start],
                    standard(),
                ) {
                    Ok((binary_literals, _)) => match binaries_to_values(binary_literals) {
                        Ok(values) => values,
                        Err(_e) => {
                            needs_recompilation = true;
                            Vec::new()
                        }
                    },
                    Err(_e) => {
                        needs_recompilation = true;
                        Vec::new()
                    }
                };

                let rule_tree = match decode_from_slice::<BinaryValue, _>(
                    &data[rule_tree_start..binary_len_start],
                    standard(),
                ) {
                    Ok((binary_tree, _)) => match binary_to_value(binary_tree) {
                        Ok(value) => value,
                        Err(_e) => {
                            needs_recompilation = true;
                            Value::new_object()
                        }
                    },
                    Err(_e) => {
                        needs_recompilation = true;
                        Value::new_object()
                    }
                };

                let mut program = match decode_from_slice::<Program, _>(
                    &data[binary_start..binary_end],
                    standard(),
                ) {
                    Ok((prog, _)) => prog,
                    Err(_e) => {
                        needs_recompilation = true;
                        Program::new()
                    }
                };

                program.entry_points = entry_points;
                program.sources = sources;
                program.literals = literals;
                program.rule_tree = rule_tree;
                program.rego_v0 = rego_v0;
                program.needs_recompilation = needs_recompilation;

                if !program.builtin_info_table.is_empty() {
                    if let Err(_e) = program.initialize_resolved_builtins() {
                        program.needs_recompilation = true;
                    }
                }

                if program.needs_recompilation {
                    Ok(DeserializationResult::Partial(program))
                } else {
                    Ok(DeserializationResult::Complete(program))
                }
            }
            v => Err(format!("Unsupported version {}", v)),
        }
    }

    /// Check if data can be deserialized without actually deserializing
    pub fn can_deserialize(data: &[u8]) -> Result<bool, String> {
        if data.len() < 8 {
            return Ok(false);
        }

        if data[0..4] != Self::MAGIC {
            return Ok(false);
        }

        let version = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);

        match version {
            1..=3 => Ok(true),
            _ => Ok(false),
        }
    }

    /// Get file format information without deserializing
    pub fn get_file_info(data: &[u8]) -> Result<(u32, usize), String> {
        if data.len() < 9 {
            return Err("Data too short for header".to_string());
        }

        if data[0..4] != Self::MAGIC {
            return Err("Invalid file format".to_string());
        }

        let version = u32::from_le_bytes([data[4], data[5], data[6], data[7]]);

        match version {
            1 => {
                if data.len() < 25 {
                    return Err("Data too short for header".to_string());
                }

                let entry_points_len =
                    u32::from_le_bytes([data[8], data[9], data[10], data[11]]) as usize;
                let sources_len =
                    u32::from_le_bytes([data[12], data[13], data[14], data[15]]) as usize;
                let binary_len_start = 17 + entry_points_len + sources_len;

                if data.len() < binary_len_start + 4 {
                    return Err("Data too short for binary length".to_string());
                }

                let binary_len = u32::from_le_bytes([
                    data[binary_len_start],
                    data[binary_len_start + 1],
                    data[binary_len_start + 2],
                    data[binary_len_start + 3],
                ]) as usize;

                Ok((version, binary_len))
            }
            2 | 3 => {
                if data.len() < 29 {
                    return Err("Data too short for header".to_string());
                }

                let entry_points_len =
                    u32::from_le_bytes([data[8], data[9], data[10], data[11]]) as usize;
                let sources_len =
                    u32::from_le_bytes([data[12], data[13], data[14], data[15]]) as usize;
                let literals_len =
                    u32::from_le_bytes([data[16], data[17], data[18], data[19]]) as usize;
                let rule_tree_len =
                    u32::from_le_bytes([data[20], data[21], data[22], data[23]]) as usize;
                let binary_len_start =
                    25 + entry_points_len + sources_len + literals_len + rule_tree_len;

                if data.len() < binary_len_start + 4 {
                    return Err("Data too short for binary length".to_string());
                }

                let binary_len = u32::from_le_bytes([
                    data[binary_len_start],
                    data[binary_len_start + 1],
                    data[binary_len_start + 2],
                    data[binary_len_start + 3],
                ]) as usize;

                Ok((version, binary_len))
            }
            v => Err(format!("Unsupported version {}", v)),
        }
    }
}
