// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Implicit allOf for unbound `[*]` wildcard fields.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::{anyhow, Result};

use crate::languages::azure_policy::ast::{Condition, FieldKind, Lhs};
use crate::rvm::instructions::{GuardMode, LoopMode, LoopStartParams};
use crate::rvm::Instruction;

use super::core::{Compiler, CountBinding};
use super::utils::{split_count_wildcard_path, split_path_without_wildcards};

impl Compiler {
    /// Check whether a condition's LHS is a field with an unbound `[*]`
    /// wildcard (i.e., not inside a count loop that covers this path).
    pub(super) fn has_unbound_wildcard_field(&self, lhs: &Lhs) -> Result<Option<String>> {
        let field = match lhs {
            Lhs::Field(field_node) => field_node,
            _ => return Ok(None),
        };

        let path = match &field.kind {
            FieldKind::Alias(alias) => self.resolve_alias_path(alias, &field.span)?,
            _ => return Ok(None),
        };

        if !path.contains("[*]") {
            return Ok(None);
        }

        if self.resolve_count_binding(&path)?.is_some() {
            return Ok(None);
        }

        Ok(Some(path))
    }

    /// Check whether a condition's LHS has an inner unbound `[*]` that lives
    /// *inside* an active count binding.
    pub(super) fn has_inner_unbound_wildcard_field(
        &self,
        lhs: &Lhs,
    ) -> Result<Option<(CountBinding, String)>> {
        let field = match lhs {
            Lhs::Field(field_node) => field_node,
            _ => return Ok(None),
        };

        let path = match &field.kind {
            FieldKind::Alias(alias) => self.resolve_alias_path(alias, &field.span)?,
            _ => return Ok(None),
        };

        if !path.contains("[*]") {
            return Ok(None);
        }

        let binding = match self.resolve_count_binding(&path)? {
            Some(b) => b,
            None => return Ok(None),
        };

        if let Some(prefix) = &binding.field_wildcard_prefix {
            let bound_len = prefix.len().saturating_add(4); // len("prefix") + len("[*].")
            if path.len() > bound_len {
                if let Some(remainder) = path.get(bound_len..) {
                    if remainder.contains("[*]") {
                        return Ok(Some((binding, remainder.to_string())));
                    }
                }
            }
        }

        Ok(None)
    }

    /// Compile a condition where the field LHS contains `[*]` outside a
    /// count loop.  Emits implicit *allOf* (Every loop).
    pub(super) fn compile_condition_wildcard_allof(
        &mut self,
        field_path: &str,
        condition: &Condition,
    ) -> Result<u8> {
        let span = &condition.span;
        let rhs_reg = self.compile_value_or_expr(&condition.rhs, span)?;
        self.compile_allof_loop_inner(None, field_path, rhs_reg, condition)
    }

    /// Recursive helper: emit one `Every` loop per `[*]` in the path.
    pub(super) fn compile_allof_loop_inner(
        &mut self,
        base_reg: Option<u8>,
        remaining_path: &str,
        rhs_reg: u8,
        condition: &Condition,
    ) -> Result<u8> {
        let (prefix, suffix) = split_count_wildcard_path(remaining_path)?;
        let prefix = prefix.to_ascii_lowercase();
        let suffix = suffix.map(|s| s.to_ascii_lowercase());
        let span = &condition.span;

        let collection_reg = match base_reg {
            Some(base) if prefix.is_empty() => base,
            Some(base) => {
                let parts = split_path_without_wildcards(&prefix)?;
                let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                self.emit_chained_index_literal_path(base, &refs, span)?
            }
            None if prefix.is_empty() => self.compile_resource_root(span)?,
            None => self.compile_resource_path_value(&prefix, span)?,
        };

        let key_reg = self.alloc_register()?;
        let current_reg = self.alloc_register()?;
        let loop_result_reg = self.alloc_register()?;

        let params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::Every,
            collection: collection_reg,
            key_reg,
            value_reg: current_reg,
            result_reg: loop_result_reg,
            body_start: 0,
            loop_end: 0,
        });

        self.emit(Instruction::LoopStart { params_index }, span);

        let body_start = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        match suffix {
            Some(ref s) if s.contains("[*]") => {
                let inner_result =
                    self.compile_allof_loop_inner(Some(current_reg), s, rhs_reg, condition)?;
                self.emit(
                    Instruction::Guard {
                        register: inner_result,
                        mode: GuardMode::Condition,
                    },
                    span,
                );
            }
            _ => {
                let element_reg = match &suffix {
                    Some(s) => {
                        let parts = split_path_without_wildcards(s)?;
                        let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                        self.emit_chained_index_literal_path(current_reg, &refs, span)?
                    }
                    None => current_reg,
                };

                let cmp_reg = self.emit_policy_operator(
                    &condition.operator.kind,
                    element_reg,
                    rhs_reg,
                    &condition.operator.span,
                )?;

                self.emit(
                    Instruction::Guard {
                        register: cmp_reg,
                        mode: GuardMode::Condition,
                    },
                    span,
                );
            }
        }

        self.emit(
            Instruction::LoopNext {
                body_start,
                loop_end: 0,
            },
            span,
        );

        let loop_end = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        self.program.update_loop_params(params_index, |params| {
            params.body_start = body_start;
            params.loop_end = loop_end;
        });

        if let Some(Instruction::LoopNext { loop_end: le, .. }) =
            self.program.instructions.last_mut()
        {
            *le = loop_end;
        }

        Ok(loop_result_reg)
    }
}
