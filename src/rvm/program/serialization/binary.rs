// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use bincode::config::standard;
use bincode::serde::{decode_from_slice, encode_to_vec};

use super::{DeserializationResult, Program};
use crate::value::Value;

use super::value::{
    binaries_to_values, binary_to_value, BinaryValue, BinaryValueRef, BinaryValueSlice,
};

/// Helper for tracking offsets with overflow checking
struct OffsetTracker {
    current: usize,
}

impl OffsetTracker {
    const fn new(start: usize) -> Self {
        Self { current: start }
    }

    fn advance(&mut self, amount: usize) -> Result<usize, String> {
        let start = self.current;
        self.current = self.current.checked_add(amount).ok_or("Offset overflow")?;
        Ok(start)
    }

    const fn current(&self) -> usize {
        self.current
    }
}

impl Program {
    /// Helper: safely read u32 from 4 bytes starting at offset
    fn read_u32(data: &[u8], offset: usize) -> Result<u32, String> {
        let bytes = data
            .get(offset..offset.checked_add(4).ok_or("Offset overflow")?)
            .ok_or_else(|| format!("Cannot read u32 at offset {}", offset))?;
        Ok(u32::from_le_bytes([
            *bytes.first().ok_or("Missing byte 0")?,
            *bytes.get(1).ok_or("Missing byte 1")?,
            *bytes.get(2).ok_or("Missing byte 2")?,
            *bytes.get(3).ok_or("Missing byte 3")?,
        ]))
    }

    /// Helper: safely read u32 as usize
    fn read_u32_as_usize(data: &[u8], offset: usize) -> Result<usize, String> {
        Self::read_u32(data, offset)?
            .try_into()
            .map_err(|_| "Size conversion overflow".to_string())
    }

    /// Helper: safely get a byte at offset
    fn read_byte(data: &[u8], offset: usize) -> Result<u8, String> {
        data.get(offset)
            .copied()
            .ok_or_else(|| format!("Cannot read byte at offset {}", offset))
    }

    /// Helper: safely get slice
    fn get_slice(data: &[u8], start: usize, end: usize) -> Result<&[u8], String> {
        data.get(start..end)
            .ok_or_else(|| format!("Cannot get slice [{}..{}]", start, end))
    }

    /// Serialize program to binary format.
    /// Uses pure bincode for all sections now that `Value` supports serde.
    pub fn serialize_binary(&self) -> Result<Vec<u8>, String> {
        self.validate_limits()?;

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

        buffer.extend_from_slice(
            &u32::try_from(entry_points_bin.len())
                .map_err(|_| "Entry points size too large")?
                .to_le_bytes(),
        );
        buffer.extend_from_slice(
            &u32::try_from(sources_bin.len())
                .map_err(|_| "Sources size too large")?
                .to_le_bytes(),
        );
        buffer.extend_from_slice(
            &u32::try_from(literals_bin.len())
                .map_err(|_| "Literals size too large")?
                .to_le_bytes(),
        );
        buffer.extend_from_slice(
            &u32::try_from(rule_tree_bin.len())
                .map_err(|_| "Rule tree size too large")?
                .to_le_bytes(),
        );
        buffer.push(if self.rego_v0 { 1 } else { 0 });

        buffer.extend_from_slice(&entry_points_bin);
        buffer.extend_from_slice(&sources_bin);
        buffer.extend_from_slice(&literals_bin);
        buffer.extend_from_slice(&rule_tree_bin);

        buffer.extend_from_slice(
            &u32::try_from(binary_data.len())
                .map_err(|_| "Binary data size too large")?
                .to_le_bytes(),
        );
        buffer.extend_from_slice(&binary_data);

        Ok(buffer)
    }

    /// Deserialize program from binary format with version checking
    pub fn deserialize_binary(data: &[u8]) -> Result<DeserializationResult, String> {
        if data.len() < 9 {
            return Err("Data too short for header".to_string());
        }

        let magic = Self::get_slice(data, 0, 4)?;
        if magic != Self::MAGIC {
            return Err("Invalid file format - magic number mismatch".to_string());
        }

        let version = Self::read_u32(data, 4)?;
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

                let entry_points_len = Self::read_u32_as_usize(data, 8)?;
                let sources_len = Self::read_u32_as_usize(data, 12)?;
                let rego_v0 = Self::read_byte(data, 16)? != 0;

                let mut offset = OffsetTracker::new(17);
                let entry_points_start = offset.advance(entry_points_len)?;
                let sources_start = offset.advance(sources_len)?;
                let binary_len_start = offset.current();

                if data.len() < binary_len_start.checked_add(4).ok_or("Offset overflow")? {
                    return Err("Data too short for binary length".to_string());
                }

                let binary_len = Self::read_u32_as_usize(data, binary_len_start)?;

                let mut binary_offset = OffsetTracker::new(binary_len_start);
                binary_offset.advance(4)?; // Skip the binary_len u32
                let binary_start = binary_offset.advance(binary_len)?;
                let json_start = binary_offset.current();

                if data.len() < json_start.checked_add(4).ok_or("Offset overflow")? {
                    return Err("Data too short for JSON length".to_string());
                }

                let json_len = Self::read_u32_as_usize(data, json_start)?;

                let total_expected = json_start
                    .checked_add(4)
                    .and_then(|v| v.checked_add(json_len))
                    .ok_or("Offset overflow")?;
                if data.len() < total_expected {
                    return Err("Data truncated".to_string());
                }

                let json_end = json_start
                    .checked_add(4)
                    .and_then(|v| v.checked_add(json_len))
                    .ok_or("Offset overflow")?;

                let entry_points = decode_from_slice(
                    Self::get_slice(data, entry_points_start, sources_start)?,
                    standard(),
                )
                .map(|(value, _)| value)
                .map_err(|e| format!("Entry points deserialization failed: {}", e))?;

                let sources = decode_from_slice(
                    Self::get_slice(data, sources_start, binary_len_start)?,
                    standard(),
                )
                .map(|(value, _)| value)
                .map_err(|e| format!("Sources deserialization failed: {}", e))?;

                let mut needs_recompilation = false;

                let mut program = match decode_from_slice::<Program, _>(
                    Self::get_slice(data, binary_start, json_start)?,
                    standard(),
                ) {
                    Ok((prog, _)) => prog,
                    Err(_e) => {
                        needs_recompilation = true;
                        Program::new()
                    }
                };

                let (literals, rule_tree) =
                    match serde_json::from_slice::<serde_json::Value>(Self::get_slice(
                        data,
                        json_start.checked_add(4).ok_or("Offset overflow")?,
                        json_end,
                    )?) {
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

                let entry_points_len = Self::read_u32_as_usize(data, 8)?;
                let sources_len = Self::read_u32_as_usize(data, 12)?;
                let literals_len = Self::read_u32_as_usize(data, 16)?;
                let rule_tree_len = Self::read_u32_as_usize(data, 20)?;
                let rego_v0 = Self::read_byte(data, 24)? != 0;

                let mut offset = OffsetTracker::new(25);
                let entry_points_start = offset.advance(entry_points_len)?;
                let sources_start = offset.advance(sources_len)?;
                let literals_start = offset.advance(literals_len)?;
                let rule_tree_start = offset.advance(rule_tree_len)?;
                let binary_len_start = offset.current();

                if data.len() < binary_len_start.checked_add(4).ok_or("Offset overflow")? {
                    return Err("Data too short for binary length".to_string());
                }

                let binary_len = Self::read_u32_as_usize(data, binary_len_start)?;

                let mut binary_offset = OffsetTracker::new(binary_len_start);
                binary_offset.advance(4)?; // Skip the binary_len u32
                let binary_start = binary_offset.advance(binary_len)?;
                let binary_end = binary_offset.current();

                if data.len() < binary_end {
                    return Err("Data truncated".to_string());
                }

                let entry_points = decode_from_slice(
                    Self::get_slice(data, entry_points_start, sources_start)?,
                    standard(),
                )
                .map(|(value, _)| value)
                .map_err(|e| format!("Entry points deserialization failed: {}", e))?;

                let sources = decode_from_slice(
                    Self::get_slice(data, sources_start, literals_start)?,
                    standard(),
                )
                .map(|(value, _)| value)
                .map_err(|e| format!("Sources deserialization failed: {}", e))?;

                let mut needs_recompilation = false;

                let literals = match decode_from_slice::<Vec<BinaryValue>, _>(
                    Self::get_slice(data, literals_start, rule_tree_start)?,
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
                    Self::get_slice(data, rule_tree_start, binary_len_start)?,
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
                    Self::get_slice(data, binary_start, binary_end)?,
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

        let magic = Self::get_slice(data, 0, 4).ok();
        if magic != Some(&Self::MAGIC[..]) {
            return Ok(false);
        }

        let version = Self::read_u32(data, 4).ok();

        match version {
            Some(1..=3) => Ok(true),
            _ => Ok(false),
        }
    }
}
