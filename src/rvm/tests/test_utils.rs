// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::shadow_unrelated,
    clippy::as_conversions
)]

//! Test utility functions for RVM serialization

use crate::rvm::program::{binaries_to_values, BinaryValue, Program};
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use bincode::config::standard;
use bincode::serde::decode_from_slice;

/// Test utility function for round-trip serialization
/// Serializes program, deserializes it, and serializes again to check for consistency
pub fn test_round_trip_serialization(program: &Program) -> Result<(), String> {
    // First serialization
    let serialized1 = program.serialize_binary()?;

    // Basic validation: ensure literal section decodes cleanly under the current format.
    if serialized1.len() >= 8 && serialized1.starts_with(&Program::MAGIC) {
        let version = u32::from_le_bytes([
            serialized1[4],
            serialized1[5],
            serialized1[6],
            serialized1[7],
        ]);

        if version == 2 && serialized1.len() >= 25 {
            let entry_points_len = u32::from_le_bytes([
                serialized1[8],
                serialized1[9],
                serialized1[10],
                serialized1[11],
            ]) as usize;
            let sources_len = u32::from_le_bytes([
                serialized1[12],
                serialized1[13],
                serialized1[14],
                serialized1[15],
            ]) as usize;
            let literals_len = u32::from_le_bytes([
                serialized1[16],
                serialized1[17],
                serialized1[18],
                serialized1[19],
            ]) as usize;
            let entry_points_start = 25;
            let sources_start = entry_points_start + entry_points_len;
            let literals_start = sources_start + sources_len;
            let rule_tree_start = literals_start + literals_len;

            if literals_len > 0 && serialized1.len() >= rule_tree_start {
                match decode_from_slice::<Vec<BinaryValue>, _>(
                    &serialized1[literals_start..rule_tree_start],
                    standard(),
                ) {
                    Ok((decoded_literals, _)) => {
                        if binaries_to_values(decoded_literals).is_err() {
                            return Err(
                                "Failed to convert literal table from binary representation".into(),
                            );
                        }
                    }
                    Err(err) => {
                        return Err(format!(
                            "Failed to decode literal table with bincode: {}",
                            err
                        ));
                    }
                }
            }
        }
    }

    // Deserialize
    let deserialized = match Program::deserialize_binary(&serialized1)? {
        crate::rvm::program::DeserializationResult::Complete(program) => program,
        crate::rvm::program::DeserializationResult::Partial(program) => {
            let info = format!(
                "Deserialization resulted in partial program during round-trip test \
                 (instructions={}, literals={}, needs_recompilation={})",
                program.instructions.len(),
                program.literals.len(),
                program.needs_recompilation()
            );
            return Err(info);
        }
    };

    // Second serialization
    let serialized2 = deserialized.serialize_binary()?;

    // Compare the two serialized versions
    if serialized1 == serialized2 {
        Ok(())
    } else {
        Err(format!(
            "Round-trip serialization failed: serialized data differs. \
            First serialization: {} bytes, Second: {} bytes",
            serialized1.len(),
            serialized2.len()
        ))
    }
}
