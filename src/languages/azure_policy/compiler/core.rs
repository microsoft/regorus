// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]
#![allow(clippy::pattern_type_mismatch)]

//! Core `Compiler` struct, main compilation pipeline, and register/emit
//! infrastructure.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::rvm::program::{Program, SpanInfo};
use crate::rvm::Instruction;
use crate::{Rc, Value};

use crate::languages::azure_policy::ast::PolicyRule;

// ---------------------------------------------------------------------------
// Types
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
pub(super) struct CountBinding {
    pub(super) name: Option<String>,
    pub(super) field_wildcard_prefix: Option<String>,
    pub(super) current_reg: u8,
}

#[derive(Debug, Default)]
pub(super) struct Compiler {
    pub(super) program: Program,
    pub(super) register_counter: u8,
    /// High-water mark of `register_counter`.
    pub(super) register_high_water: u8,
    pub(super) source_to_index: BTreeMap<String, usize>,
    pub(super) builtin_index: BTreeMap<String, u16>,
    pub(super) count_bindings: Vec<CountBinding>,
    /// Cached register for `LoadInput` — allocated once on first use.
    pub(super) cached_input_reg: Option<u8>,
    /// Cached register for `LoadContext` — allocated once on first use.
    pub(super) cached_context_reg: Option<u8>,
    /// Map from lowercase fully-qualified alias name → short name.
    pub(super) alias_map: BTreeMap<String, String>,
    /// Map from lowercase fully-qualified alias name → modifiable flag.
    pub(super) alias_modifiable: BTreeMap<String, bool>,
    /// Default values for policy parameters.
    pub(super) parameter_defaults: Option<Value>,
    /// When set, field conditions resolve against this register instead of
    /// `input.resource`.  Used for `existenceCondition`.
    pub(super) resource_override_reg: Option<u8>,

    // -- Metadata accumulators ---------------------------------------------
    pub(super) observed_field_kinds: BTreeSet<String>,
    pub(super) observed_aliases: BTreeSet<String>,
    pub(super) observed_tag_names: BTreeSet<String>,
    pub(super) observed_operators: BTreeSet<String>,
    pub(super) observed_resource_types: BTreeSet<String>,
    pub(super) observed_uses_count: bool,
    pub(super) observed_has_dynamic_fields: bool,
    pub(super) observed_has_wildcard_aliases: bool,

    /// When `true`, unknown aliases are silently treated as raw property paths.
    pub(super) alias_fallback_to_raw: bool,
}

// ---------------------------------------------------------------------------
// Core infrastructure
// ---------------------------------------------------------------------------

impl Compiler {
    pub(super) fn new() -> Self {
        Self {
            register_counter: 0,
            ..Self::default()
        }
    }

    pub(super) fn compile(mut self, rule: &PolicyRule) -> Result<Rc<Program>> {
        let cond_reg = self.compile_constraint(&rule.condition)?;
        self.emit(
            Instruction::ReturnUndefinedIfNotTrue {
                condition: cond_reg,
            },
            &rule.span,
        );

        let effect_reg = self.compile_effect(rule)?;
        self.emit(
            Instruction::Return { value: effect_reg },
            &rule.then_block.span,
        );

        self.program.main_entry_point = 0;
        self.program.entry_points.insert("main".to_string(), 0);
        self.program.dispatch_window_size = self.register_high_water.max(2);
        self.program.max_rule_window_size = 0;

        if !self.program.builtin_info_table.is_empty() {
            self.program.initialize_resolved_builtins()?;
        }

        self.program
            .validate_limits()
            .map_err(|message| anyhow!(message))?;

        self.populate_compiled_annotations();

        Ok(Rc::new(self.program))
    }

    // -- register / span / emit helpers ------------------------------------

    /// Restore `register_counter` to `saved` while protecting cached registers.
    pub(super) fn restore_register_counter(&mut self, saved: u8) {
        let mut floor = saved;
        if let Some(r) = self.cached_input_reg {
            floor = floor.max(r.saturating_add(1));
        }
        if let Some(r) = self.cached_context_reg {
            floor = floor.max(r.saturating_add(1));
        }
        self.register_counter = floor;
    }

    pub(super) fn alloc_register(&mut self) -> Result<u8> {
        if self.register_counter == u8::MAX {
            bail!("azure-policy compiler exhausted RVM registers");
        }
        let reg = self.register_counter;
        self.register_counter = self.register_counter.saturating_add(1);
        if self.register_counter > self.register_high_water {
            self.register_high_water = self.register_counter;
        }
        Ok(reg)
    }

    pub(super) fn span_info(&mut self, span: &crate::lexer::Span) -> SpanInfo {
        let path = span.source.get_path().to_string();
        let source_index = if let Some(index) = self.source_to_index.get(path.as_str()) {
            *index
        } else {
            let index = self
                .program
                .add_source(path.clone(), span.source.get_contents().to_string());
            self.source_to_index.insert(path, index);
            index
        };

        SpanInfo::from_lexer_span(span, source_index)
    }

    pub(super) fn emit(&mut self, instruction: Instruction, span: &crate::lexer::Span) {
        let span_info = self.span_info(span);
        self.program.add_instruction(instruction, Some(span_info));
    }

    /// Return the PC (instruction index) that the *next* emitted instruction
    /// will occupy.
    pub(super) fn current_pc(&self) -> Result<u16> {
        u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))
    }

    /// Patch tracked instruction indices, setting their `end_pc` field.
    pub(super) fn patch_end_pc(&mut self, pcs: &[u16], end_pc: u16) -> Result<()> {
        for &pc in pcs {
            let idx = usize::from(pc);
            let instr = self
                .program
                .instructions
                .get_mut(idx)
                .ok_or_else(|| anyhow!("patch_end_pc: pc {} out of bounds", pc))?;
            match instr {
                Instruction::LogicalBlockStart {
                    end_pc: ref mut ep, ..
                }
                | Instruction::AllOfNext {
                    end_pc: ref mut ep, ..
                }
                | Instruction::AnyOfNext {
                    end_pc: ref mut ep, ..
                } => {
                    *ep = end_pc;
                }
                _ => {
                    bail!("patch_end_pc: unexpected instruction at pc {}", pc);
                }
            }
        }
        Ok(())
    }
}
