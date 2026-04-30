// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]
#![allow(clippy::pattern_type_mismatch)]

//! Core `Compiler` struct, main compilation pipeline, and register/emit
//! infrastructure.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::rvm::instructions::{BuiltinCallParams, ChainedIndexParams, LiteralOrRegister};
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
    /// Cached literal-table index for `parameter_defaults` (or an empty object
    /// when no defaults exist). Populated on first `parameters()` call to avoid
    /// repeated O(n) literal-table scans and deep `Value` clones.
    pub(super) cached_defaults_literal_idx: Option<u16>,
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

    // -- literal / builtin / chained-index helpers -------------------------

    pub(super) fn add_literal_u16(&mut self, value: Value) -> Result<u16> {
        let idx = self.program.add_literal(value);
        u16::try_from(idx).map_err(|_| anyhow!("literal table exceeds u16 index space"))
    }

    pub(super) fn load_literal(&mut self, value: Value, span: &crate::lexer::Span) -> Result<u8> {
        let literal_idx = self.add_literal_u16(value)?;
        let dest = self.alloc_register()?;
        self.emit(Instruction::Load { dest, literal_idx }, span);
        Ok(dest)
    }

    pub(super) fn get_or_add_builtin_index(&mut self, name: &str, num_args: u16) -> u16 {
        let key = format!("{}/{}", name, num_args);
        if let Some(index) = self.builtin_index.get(&key) {
            return *index;
        }

        let index = self
            .program
            .add_builtin_info(crate::rvm::program::BuiltinInfo {
                name: name.to_string(),
                num_args,
            });
        self.builtin_index.insert(key, index);
        index
    }

    pub(super) fn emit_builtin_call(
        &mut self,
        name: &str,
        args: &[u8],
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        // TODO: Some ARM template functions are variadic (e.g. format,
        // coalesce, union).  If >8 args are needed, consider packing into an
        // array or folding/chaining associative calls.
        if args.len() > 8 {
            bail!(span.error(&format!("builtin call {} exceeds max 8 args", name)));
        }

        let dest = self.alloc_register()?;
        let builtin_index = self.get_or_add_builtin_index(
            name,
            u16::try_from(args.len()).map_err(|_| anyhow!("arg count overflow"))?,
        );

        let mut arg_slots = [0_u8; 8];
        for (slot, arg) in arg_slots.iter_mut().zip(args.iter()) {
            *slot = *arg;
        }

        let params_index = self.program.add_builtin_call_params(BuiltinCallParams {
            dest,
            builtin_index,
            num_args: u8::try_from(args.len()).map_err(|_| anyhow!("arg count overflow"))?,
            args: arg_slots,
        });

        self.emit(Instruction::BuiltinCall { params_index }, span);
        Ok(dest)
    }

    pub(super) fn emit_chained_index_literal_path(
        &mut self,
        root: u8,
        path: &[&str],
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let dest = self.alloc_register()?;

        // TODO: Auto-parsing numeric-looking segments as u64 can mis-index
        // object keys that happen to be digits (e.g. a tag named "123" would
        // become numeric index 123).  Consider carrying type metadata from
        // `split_path_without_wildcards` or adding a string-only variant of
        // this helper for object key lookups like tags.
        let path_components = path
            .iter()
            .map(|segment| {
                let value = segment
                    .parse::<u64>()
                    .map_or_else(|_| Value::from((*segment).to_string()), Value::from);
                self.add_literal_u16(value).map(LiteralOrRegister::Literal)
            })
            .collect::<Result<Vec<_>>>()?;

        let params_index =
            self.program
                .instruction_data
                .add_chained_index_params(ChainedIndexParams {
                    dest,
                    root,
                    path_components,
                });
        self.emit(Instruction::ChainedIndex { params_index }, span);

        Ok(dest)
    }

    pub(super) fn load_input(&mut self, span: &crate::lexer::Span) -> Result<u8> {
        if let Some(reg) = self.cached_input_reg {
            return Ok(reg);
        }
        let dest = self.alloc_register()?;
        self.emit(Instruction::LoadInput { dest }, span);
        self.cached_input_reg = Some(dest);
        Ok(dest)
    }

    pub(super) fn load_context(&mut self, span: &crate::lexer::Span) -> Result<u8> {
        if let Some(reg) = self.cached_context_reg {
            return Ok(reg);
        }
        let dest = self.alloc_register()?;
        self.emit(Instruction::LoadContext { dest }, span);
        self.cached_context_reg = Some(dest);
        Ok(dest)
    }

    /// Emit a `CoalesceUndefinedToNull` instruction for the given register.
    ///
    /// In Azure Policy, a missing field is semantically `null`, not undefined.
    pub(super) fn emit_coalesce_undefined_to_null(
        &mut self,
        register: u8,
        span: &crate::lexer::Span,
    ) {
        self.emit(Instruction::CoalesceUndefinedToNull { register }, span);
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

    // -- alias resolution --------------------------------------------------

    pub(super) fn resolve_alias_path(
        &self,
        path: &str,
        span: &crate::lexer::Span,
    ) -> Result<String> {
        let lc = path.to_ascii_lowercase();
        if let Some(short) = self.alias_map.get(&lc) {
            let resolved = short.clone();
            let result = Self::strip_fq_prefix(&resolved).to_ascii_lowercase();
            return Ok(result);
        }

        // Fallback: derive array path from a corresponding `[*]` alias.
        if !lc.contains("[*]") {
            let wildcard_key = alloc::format!("{}[*]", lc);
            if let Some(short) = self.alias_map.get(&wildcard_key) {
                let resolved = Self::strip_fq_prefix(short).to_ascii_lowercase();
                if let Some(base) = resolved.strip_suffix("[*]") {
                    return Ok(base.to_string());
                }
            }
        }

        if !self.alias_map.is_empty() && !self.alias_fallback_to_raw {
            bail!(span.error(&alloc::format!(
                "unknown alias '{}': field references must use fully-qualified alias names when an alias catalog is loaded",
                path
            )));
        }

        if self.alias_map.is_empty() {
            Ok(path.to_string())
        } else {
            let result = Self::strip_fq_prefix(path).to_ascii_lowercase();
            Ok(result)
        }
    }

    /// Strip any resource-type prefix segments from a resolved alias short
    /// name, keeping only the trailing property path.
    pub(super) fn strip_fq_prefix(resolved: &str) -> String {
        resolved
            .rfind('/')
            .and_then(|idx| resolved.get(idx.saturating_add(1)..))
            .unwrap_or(resolved)
            .to_string()
    }
}
