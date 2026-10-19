// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use postcard::{from_bytes, to_allocvec};

use super::{DeserializationResult, Program};

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
    /// Uses postcard for all sections now that `Value` supports serde.
    pub fn serialize_binary(&self) -> Result<Vec<u8>, String> {
        self.validate_limits()?;

        let mut buffer = Vec::new();

        buffer.extend_from_slice(&Self::MAGIC);
        buffer.extend_from_slice(&Self::SERIALIZATION_VERSION.to_le_bytes());

        let entry_points_bin = to_allocvec(&self.entry_points)
            .map_err(|e| format!("Entry points postcard serialization failed: {}", e))?;

        let sources_bin = to_allocvec(&self.sources)
            .map_err(|e| format!("Sources postcard serialization failed: {}", e))?;

        let literals_bin = to_allocvec(&BinaryValueSlice(self.literals.as_slice()))
            .map_err(|e| format!("Literals postcard serialization failed: {}", e))?;

        let rule_tree_bin = to_allocvec(&BinaryValueRef(&self.rule_tree))
            .map_err(|e| format!("Rule tree postcard serialization failed: {}", e))?;

        let binary_data = to_allocvec(self)
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
            1..=5 => {
                let mut program = Program::new();
                program.needs_recompilation = true;
                program.rego_v0 = Self::legacy_rego_v0(data, version).unwrap_or(false);
                Ok(DeserializationResult::Partial(program))
            }
            6 => {
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
                if data.len() > binary_end {
                    return Err("Unexpected trailing data".to_string());
                }

                let entry_points =
                    from_bytes(Self::get_slice(data, entry_points_start, sources_start)?)
                        .map_err(|e| format!("Entry points deserialization failed: {}", e))?;

                let sources = from_bytes(Self::get_slice(data, sources_start, literals_start)?)
                    .map_err(|e| format!("Sources deserialization failed: {}", e))?;

                // Fail-closed contract for a blob at `SERIALIZATION_VERSION`: every section it
                // declares is readable by this exact code, so a section that does not decode is
                // corruption or truncation, not a format we can degrade from. Substituting
                // defaults here used to hand back `Ok(Partial)` with an empty literal table, an
                // empty rule tree or `Program::new()` (zero instructions), which a caller that
                // ignores `needs_recompilation` would happily execute. The legacy versions above
                // keep the `Partial` + recompile path because their layout is not readable at all.
                let literals = binaries_to_values(
                    from_bytes::<Vec<BinaryValue>>(Self::get_slice(
                        data,
                        literals_start,
                        rule_tree_start,
                    )?)
                    .map_err(|e| format!("Literals deserialization failed: {}", e))?,
                )?;

                let rule_tree = binary_to_value(
                    from_bytes::<BinaryValue>(Self::get_slice(
                        data,
                        rule_tree_start,
                        binary_len_start,
                    )?)
                    .map_err(|e| format!("Rule tree deserialization failed: {}", e))?,
                )?;

                let mut program =
                    from_bytes::<Program>(Self::get_slice(data, binary_start, binary_end)?)
                        .map_err(|e| format!("Program structure deserialization failed: {}", e))?;

                program.entry_points = entry_points;
                program.sources = sources;
                program.literals = literals;
                program.rule_tree = rule_tree;
                program.rego_v0 = rego_v0;
                program.needs_recompilation = false;

                // Consume-side half of `validate_limits()`: the compilers and `serialize_binary`
                // (produce) already refuse to emit an over-limit program, so such a blob can only
                // be assembled by hand - and `Instruction` jump targets and literal indices are
                // u16, so loading it would index past those tables at run time. Checking the
                // assembled program keeps this the same predicate the produce side uses.
                program.validate_limits()?;

                if !program.builtin_info_table.is_empty() {
                    // Not a decode failure: the bytes are intact, this engine just cannot resolve a
                    // builtin the blob names, so recompiling is still the documented answer.
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
            Some(1..=6) => Ok(true),
            _ => Ok(false),
        }
    }

    fn legacy_rego_v0(data: &[u8], version: u32) -> Option<bool> {
        match version {
            1 => data.get(16).map(|value| *value != 0),
            2..=5 => data.get(24).map(|value| *value != 0),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::arithmetic_side_effects,
        clippy::as_conversions,
        clippy::expect_used,
        clippy::indexing_slicing,
        clippy::panic,
        clippy::print_stdout,
        clippy::unwrap_used
    )]

    //! The hostile-blob cases the public test surface cannot express: they need the private
    //! section encoders (`BinaryValueSlice` / `BinaryValueRef`) and they need to bypass
    //! `serialize_binary`, which refuses to produce an over-limit program in the first place.

    use super::*;
    use crate::rvm::Instruction;
    use crate::value::Value;

    /// Bytes before the first section: MAGIC(4) + version(4) + 4 section lengths + rego_v0(1).
    const HDR: usize = 25;

    struct Sections {
        entry_points: Vec<u8>,
        sources: Vec<u8>,
        literals: Vec<u8>,
        rule_tree: Vec<u8>,
        artifact: Vec<u8>,
    }

    /// Encode the sections exactly as `serialize_binary` does, except that the artifact section is
    /// taken straight from `to_allocvec`: `serialize_binary` runs `validate_limits()` first and so
    /// cannot produce an over-limit blob. That refusal is the gap consume has to close itself.
    fn sections(program: &Program) -> Sections {
        Sections {
            entry_points: to_allocvec(&program.entry_points).expect("entry points"),
            sources: to_allocvec(&program.sources).expect("sources"),
            literals: to_allocvec(&BinaryValueSlice(program.literals.as_slice()))
                .expect("literals"),
            rule_tree: to_allocvec(&BinaryValueRef(&program.rule_tree)).expect("rule tree"),
            artifact: to_allocvec(program).expect("artifact section"),
        }
    }

    fn assemble(sections: &Sections) -> Vec<u8> {
        let len_of = |section: &Vec<u8>| {
            u32::try_from(section.len())
                .expect("section fits in u32")
                .to_le_bytes()
        };
        let mut blob = Vec::new();
        blob.extend_from_slice(&Program::MAGIC);
        blob.extend_from_slice(&Program::SERIALIZATION_VERSION.to_le_bytes());
        for section in [
            &sections.entry_points,
            &sections.sources,
            &sections.literals,
            &sections.rule_tree,
        ] {
            blob.extend_from_slice(&len_of(section));
        }
        blob.push(0); // rego_v0 = false
        for section in [
            &sections.entry_points,
            &sections.sources,
            &sections.literals,
            &sections.rule_tree,
        ] {
            blob.extend_from_slice(section);
        }
        blob.extend_from_slice(&len_of(&sections.artifact));
        blob.extend_from_slice(&sections.artifact);
        blob
    }

    fn sample_program() -> Program {
        let mut program = Program::new();
        program.entry_points.insert("main".to_string(), 0);
        program.instructions = alloc::vec![Instruction::LoadNull { dest: 0 }];
        program.literals = alloc::vec![Value::from(1.5_f64), Value::from("x")];
        program.rule_tree = Value::from(7_i64);
        program
    }

    /// Byte range of each section within an assembled blob.
    fn literals_range(blob: &[u8]) -> core::ops::Range<usize> {
        let len_at = |off: usize| {
            u32::from_le_bytes([blob[off], blob[off + 1], blob[off + 2], blob[off + 3]]) as usize
        };
        let literals_start = HDR + len_at(8) + len_at(12);
        let literals_end = literals_start + len_at(16);
        literals_start..literals_end
    }

    /// Peak RSS of this process in kB. Reading it is how the "no pre-allocation" claims below are
    /// checked rather than asserted by prose.
    fn peak_rss_kb() -> u64 {
        std::fs::read_to_string("/proc/self/status")
            .unwrap_or_default()
            .lines()
            .find_map(|line| {
                line.strip_prefix("VmHWM:")
                    .and_then(|value| value.split_whitespace().next())
                    .and_then(|value| value.parse::<u64>().ok())
            })
            .unwrap_or(0)
    }

    /// LEB128, the encoding postcard uses for sequence and map lengths.
    fn varint(mut value: u64) -> Vec<u8> {
        let mut out = Vec::new();
        loop {
            let byte = 0x80 | u8::try_from(value & 0x7f).expect("masked nibble fits in u8");
            value >>= 7;
            if value == 0 {
                out.push(byte & 0x7f);
                return out;
            }
            out.push(byte);
        }
    }

    /// `validate_limits()` on consume, instructions side. A blob carrying more than
    /// `MAX_INSTRUCTIONS` instructions cannot be produced by this crate, so it is hand-assembled;
    /// `Instruction` jump targets and literal indices are `u16`, so loading it is unsound at run
    /// time rather than merely large.
    #[test]
    fn consume_rejects_over_limit_instruction_count() {
        let mut program = sample_program();
        program.instructions =
            alloc::vec![Instruction::LoadNull { dest: 0 }; Program::MAX_INSTRUCTIONS + 1];

        // The produce side already refuses. This is the half that was missing.
        program
            .serialize_binary()
            .expect_err("serialize_binary must keep refusing an over-limit program");

        let err = Program::deserialize_binary(&assemble(&sections(&program)))
            .expect_err("consume must reject an over-limit instruction count");
        assert!(err.contains("max instructions"), "unexpected error: {err}");
    }

    /// `validate_limits()` on consume, literals side: same construction, the literals section is
    /// the one that overflows.
    #[test]
    fn consume_rejects_over_limit_literal_count() {
        let mut program = sample_program();
        program.literals = alloc::vec![Value::Null; Program::MAX_LITERALS + 1];

        program
            .serialize_binary()
            .expect_err("serialize_binary must keep refusing an over-limit program");

        let err = Program::deserialize_binary(&assemble(&sections(&program)))
            .expect_err("consume must reject an over-limit literal count");
        assert!(err.contains("max literals"), "unexpected error: {err}");
    }

    /// A corrupted literals section must be `Err` at the current version, not `Ok(Partial)` with an
    /// empty literal table (the pre-fix behaviour substituted `Vec::new()` and set
    /// `needs_recompilation`, so a caller that ignored the flag evaluated the wrong program).
    #[test]
    fn consume_rejects_a_corrupted_literals_section() {
        let blob = assemble(&sections(&sample_program()));
        let literals = literals_range(&blob);
        // Section layout: u32 varint element count, then one `BinaryValue` per literal.
        assert_eq!(blob[literals.start], 2, "two literals were encoded");

        // (a) an out-of-range variant tag: `value.rs BINARY_VARIANTS` has 11 entries (0..=10).
        let mut bad_tag = blob.clone();
        bad_tag[literals.start + 1] = 99;
        match Program::deserialize_binary(&bad_tag) {
            Err(err) => std::println!("corrupt literals tag rejected: {err}"),
            Ok(result) => panic!("corrupt literals tag accepted: {result:?}"),
        }

        // Teeth: the untouched blob still consumes cleanly.
        match Program::deserialize_binary(&blob).expect("the intact blob must consume") {
            DeserializationResult::Complete(program) => {
                assert_eq!(program.literals.len(), 2);
                assert!(!program.needs_recompilation);
            }
            DeserializationResult::Partial(program) => {
                panic!(
                    "intact blob came back Partial (needs_recompilation={})",
                    program.needs_recompilation
                )
            }
        }
    }

    /// Attacker-controlled element counts must not be trusted for pre-allocation. Three shapes:
    /// the entry-points map count, the literals seq count, and the artifact section's first field
    /// (`Program::instructions`, first in the derive's field order) - each declares
    /// 4_000_000_000 elements and carries no payload.
    ///
    /// Mechanism that keeps this cheap (verified against the vendored sources, not guessed):
    /// the section byte lengths are checked against the buffer before any slicing, and postcard's
    /// `SeqAccess::size_hint` (postcard-1.1.3 src/de/deserializer.rs) reports `None` whenever the
    /// declared element count exceeds the bytes left in the section, so serde's `Vec` visitor
    /// reserves nothing; where the count is plausible, serde's `size_hint::cautious` and indexmap's
    /// `cautious_capacity` cap the reservation at 1 MiB of elements.
    #[test]
    fn consume_does_not_pre_allocate_from_forged_element_counts() {
        let honest = sections(&sample_program());
        let forged_len = varint(4_000_000_000);

        for field in ["entry_points", "literals", "artifact instructions"] {
            let mut sections = Sections {
                entry_points: honest.entry_points.clone(),
                sources: honest.sources.clone(),
                literals: honest.literals.clone(),
                rule_tree: honest.rule_tree.clone(),
                artifact: honest.artifact.clone(),
            };
            match field {
                "entry_points" => sections.entry_points = forged_len.clone(),
                "literals" => sections.literals = forged_len.clone(),
                _ => sections.artifact = forged_len.clone(),
            }
            let err = Program::deserialize_binary(&assemble(&sections))
                .expect_err(&format!("{field}: a forged element count must be rejected"));
            assert!(!err.is_empty(), "{field}: empty error message");
        }

        let rss = peak_rss_kb();
        std::println!("peak RSS after three forged 4_000_000_000 element counts: {rss} kB");
        assert!(rss < 300_000, "forged element counts peaked at {rss} kB");
    }
}
