// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! `count` / `count.where` compilation and count-binding resolution.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::languages::azure_policy::ast::{
    Condition, Constraint, CountNode, FieldKind, JsonValue, OperatorKind, ValueOrExpr,
};
use crate::rvm::instructions::{GuardMode, LoopMode, LoopStartParams, PolicyOp};
use crate::rvm::Instruction;
use crate::Value;

use super::core::{Compiler, CountBinding};
use super::utils::{split_count_wildcard_path, split_path_without_wildcards};

impl Compiler {
    pub(super) fn compile_count(&mut self, count_node: &CountNode) -> Result<u8> {
        self.observed_uses_count = true;
        match count_node {
            CountNode::Value {
                span,
                value,
                name,
                where_,
            } => {
                let collection_reg = self.compile_value_or_expr(value, span)?;
                self.compile_count_loop(
                    collection_reg,
                    name.as_ref().map(|n| n.name.clone()),
                    None,
                    where_.as_deref(),
                    span,
                )
            }
            CountNode::Field {
                span,
                field,
                where_,
            } => {
                let field_path = self.extract_field_count_path(field, span)?;
                let (_prefix, suffix) = split_count_wildcard_path(&field_path)
                    .map_err(|e| span.error(&e.to_string()))?;

                // Multi-level wildcard (e.g. `A[*].B[*]`) → emit nested loops.
                // If an outer count binding covers part of the path, start
                // from the bound element instead of the resource root.
                if suffix.as_ref().is_some_and(|s| s.contains("[*]")) {
                    if let Some(binding) = self.resolve_count_binding(&field_path)? {
                        if let Some(outer_prefix) = &binding.field_wildcard_prefix {
                            let lc_prefix = outer_prefix.to_ascii_lowercase();
                            let wildcard_dot = format!("{}[*].", lc_prefix);
                            if let Some(inner_path) =
                                field_path.to_ascii_lowercase().strip_prefix(&wildcard_dot)
                            {
                                let inner_path = inner_path.to_string();
                                return self.compile_count_nested(
                                    Some(binding.current_reg),
                                    &inner_path,
                                    where_.as_deref(),
                                    outer_prefix,
                                    span,
                                );
                            }
                        }
                    }
                    return self.compile_count_nested(
                        None,
                        &field_path,
                        where_.as_deref(),
                        "",
                        span,
                    );
                }

                // Single wildcard → existing path via resolve + single count loop.
                let (collection_reg, prefix) = self.resolve_count_field_collection(field, span)?;
                self.compile_count_loop(collection_reg, None, Some(prefix), where_.as_deref(), span)
            }
        }
    }

    /// Resolve the collection register and wildcard prefix for a field-based
    /// count node, handling nested count bindings.
    fn resolve_count_field_collection(
        &mut self,
        field: &crate::languages::azure_policy::ast::FieldNode,
        span: &crate::lexer::Span,
    ) -> Result<(u8, String)> {
        let field_path = self.extract_field_count_path(field, span)?;
        let (collection_prefix, suffix) =
            split_count_wildcard_path(&field_path).map_err(|e| span.error(&e.to_string()))?;

        // Check if this field path is relative to an outer count binding.
        if let Some(binding) = self.resolve_count_binding(&field_path)? {
            if let Some(outer_prefix) = &binding.field_wildcard_prefix {
                let lc_prefix = outer_prefix.to_ascii_lowercase();
                let wildcard_dot = format!("{}[*].", lc_prefix);
                if let Some(inner_path) =
                    field_path.to_ascii_lowercase().strip_prefix(&wildcard_dot)
                {
                    let inner_path = inner_path.to_string();
                    if inner_path.contains("[*]") {
                        let (inner_collection, _) = split_count_wildcard_path(&inner_path)
                            .map_err(|e| span.error(&e.to_string()))?;
                        let inner_collection = inner_collection.to_ascii_lowercase();
                        let parts = split_path_without_wildcards(&inner_collection)?;
                        let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                        let collection_reg =
                            self.emit_chained_index_literal_path(binding.current_reg, &refs, span)?;
                        let inner_prefix = format!("{}[*].{}", lc_prefix, inner_collection);
                        return Ok((collection_reg, inner_prefix));
                    }
                }
            }
        }

        // Multi-level wildcard: now handled by compile_count_nested in compile_count.
        // (Single-wildcard paths fall through to here.)
        if suffix.as_ref().is_some_and(|s| s.contains("[*]")) {
            bail!(span.error(&format!(
                "multi-wildcard path should have been handled before resolve_count_field_collection: {}",
                field_path
            )));
        }

        let collection_reg = self.compile_resource_path_value(&collection_prefix, span)?;
        Ok((collection_reg, collection_prefix))
    }

    /// Compile a multi-wildcard count path as nested loops.
    ///
    /// Each intermediate `[*]` level emits a `ForEach` loop that accumulates
    /// the inner count.  The innermost `[*]` emits the real count loop with
    /// the where clause and binding.
    ///
    /// * `base_reg` — `None` for resource root, `Some` when inside an outer loop.
    /// * `remaining_path` — the portion of the field path still to process;
    ///   must contain at least one `[*]`.
    /// * `where_clause` — the optional where constraint (applied only at the
    ///   innermost level).
    /// * `accumulated_prefix` — the path prefix accumulated from outer levels,
    ///   used to build binding prefixes.
    fn compile_count_nested(
        &mut self,
        base_reg: Option<u8>,
        remaining_path: &str,
        where_clause: Option<&Constraint>,
        accumulated_prefix: &str,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let (collection_part, suffix) =
            split_count_wildcard_path(remaining_path).map_err(|e| span.error(&e.to_string()))?;
        let has_more_wildcards = suffix.as_ref().is_some_and(|s| s.contains("[*]"));

        // Build the binding prefix for this level.
        let binding_prefix = if accumulated_prefix.is_empty() {
            collection_part.clone()
        } else {
            format!("{}[*].{}", accumulated_prefix, collection_part)
        };

        // Lowercase the collection path to match normalized resource keys.
        let collection_lower = collection_part.to_ascii_lowercase();

        // Navigate to the collection.  `split_count_wildcard_path` guarantees
        // the collection segment before `[*]` is non-empty.
        let collection_reg = match base_reg {
            Some(base) => {
                let parts = split_path_without_wildcards(&collection_lower)?;
                let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                self.emit_chained_index_literal_path(base, &refs, span)?
            }
            None => self.compile_resource_path_value(&collection_lower, span)?,
        };

        if !has_more_wildcards {
            // Innermost wildcard → delegate to the regular count loop.
            // Optimization: if no where clause, just emit Count instruction.
            // Note: Count returns Undefined for non-iterable collections,
            // which differs from LoopMode::Any (treats them as empty).  The
            // existence-pattern optimizer (`try_compile_count_as_any`) skips
            // nested-wildcard no-where counts so this path is always taken
            // for that case, preserving Undefined-propagation semantics.
            if where_clause.is_none() {
                let dest = self.alloc_register()?;
                self.emit(
                    Instruction::Count {
                        dest,
                        collection: collection_reg,
                    },
                    span,
                );
                return Ok(dest);
            }
            return self.compile_count_loop(
                collection_reg,
                None,
                Some(binding_prefix),
                where_clause,
                span,
            );
        }

        // Intermediate wildcard → ForEach loop that accumulates inner counts.
        let count_reg = self.load_literal(Value::from(0_i64), span)?;
        let key_reg = self.alloc_register()?;
        let current_reg = self.alloc_register()?;
        let loop_result_reg = self.alloc_register()?;

        let params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::ForEach,
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

        // Push binding for this level so inner where-clause field references
        // can resolve through this wildcard level.
        self.count_bindings.push(CountBinding {
            name: None,
            field_wildcard_prefix: Some(binding_prefix.clone()),
            current_reg,
        });

        // Recurse for the inner level(s).
        let suffix_ref = suffix
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("suffix should be Some for nested count"))?;
        let inner_count = self.compile_count_nested(
            Some(current_reg),
            suffix_ref,
            where_clause,
            &binding_prefix,
            span,
        )?;

        // Accumulate inner count into outer count.
        self.emit(
            Instruction::Add {
                dest: count_reg,
                left: count_reg,
                right: inner_count,
            },
            span,
        );

        self.count_bindings.pop();

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

        Ok(count_reg)
    }

    /// Compile a multi-wildcard count path as nested `Any` loops for the
    /// `count > 0` / `count == 0` existence-pattern optimization.
    ///
    /// Each intermediate `[*]` level emits an `Any` loop whose body is the
    /// next level.  The innermost `[*]` emits `compile_count_any_loop` with
    /// the where clause.  If `exists` is false the result is negated.
    ///
    /// **Important:** This must only be called when `where_clause` is `Some`.
    /// Without a where clause the non-optimized path (`compile_count_nested`)
    /// uses `Instruction::Count` at the innermost level.  That instruction
    /// returns `Undefined` for missing/non-iterable collections, whereas the
    /// `Any` loop treats them as empty (false).  The difference changes the
    /// semantics of `count == 0` from false (via Undefined propagation) to
    /// true (via `Not(false)`).  The caller (`try_compile_count_as_any`)
    /// returns `None` for no-where nested counts so the generic count+compare
    /// path is used instead.
    fn compile_count_nested_any(
        &mut self,
        base_reg: Option<u8>,
        remaining_path: &str,
        where_clause: &Constraint,
        accumulated_prefix: &str,
        exists: bool,
        span: &crate::lexer::Span,
    ) -> Result<Option<u8>> {
        let (collection_part, suffix) =
            split_count_wildcard_path(remaining_path).map_err(|e| span.error(&e.to_string()))?;
        let has_more_wildcards = suffix.as_ref().is_some_and(|s| s.contains("[*]"));

        let binding_prefix = if accumulated_prefix.is_empty() {
            collection_part.clone()
        } else {
            format!("{}[*].{}", accumulated_prefix, collection_part)
        };

        // Lowercase the collection path to match normalized resource keys.
        let collection_lower = collection_part.to_ascii_lowercase();

        // Navigate to the collection.  `split_count_wildcard_path` guarantees
        // the collection segment before `[*]` is non-empty.
        let collection_reg = match base_reg {
            Some(base) => {
                let parts = split_path_without_wildcards(&collection_lower)?;
                let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                self.emit_chained_index_literal_path(base, &refs, span)?
            }
            None => self.compile_resource_path_value(&collection_lower, span)?,
        };

        if !has_more_wildcards {
            // Innermost wildcard → regular Any loop.
            let any_result = self.compile_count_any_loop(
                collection_reg,
                None,
                Some(binding_prefix),
                Some(where_clause),
                span,
            )?;
            return if exists {
                Ok(Some(any_result))
            } else {
                let dest = self.alloc_register()?;
                self.emit(
                    Instruction::PolicyCondition {
                        dest,
                        left: any_result,
                        right: 0,
                        op: PolicyOp::Not,
                    },
                    span,
                );
                Ok(Some(dest))
            };
        }

        // Intermediate wildcard → Any loop wrapping inner nested Any.
        let key_reg = self.alloc_register()?;
        let current_reg = self.alloc_register()?;
        let result_reg = self.alloc_register()?;

        let params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::Any,
            collection: collection_reg,
            key_reg,
            value_reg: current_reg,
            result_reg,
            body_start: 0,
            loop_end: 0,
        });

        self.emit(Instruction::LoopStart { params_index }, span);

        let body_start = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        // Push binding for this level.
        self.count_bindings.push(CountBinding {
            name: None,
            field_wildcard_prefix: Some(binding_prefix.clone()),
            current_reg,
        });

        // Recurse — the inner call returns Some(result_reg) with the final
        // negation already applied at the innermost level.  For the outer
        // Any loop, we need "any inner satisfies" so we pass `exists = true`
        // here and handle the overall negation at the end.
        let suffix_ref = suffix
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("suffix should be Some for nested any"))?;
        let inner = self
            .compile_count_nested_any(
                Some(current_reg),
                suffix_ref,
                where_clause,
                &binding_prefix,
                /* exists */ true,
                span,
            )?
            .ok_or_else(|| anyhow::anyhow!("nested any should always return Some"))?;

        // The outer Any body succeeds when the inner Any returned true.
        self.emit(
            Instruction::Guard {
                register: inner,
                mode: GuardMode::Condition,
            },
            span,
        );

        self.count_bindings.pop();

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

        // If !exists (count == 0), negate the Any result.
        if exists {
            Ok(Some(result_reg))
        } else {
            let dest = self.alloc_register()?;
            self.emit(
                Instruction::PolicyCondition {
                    dest,
                    left: result_reg,
                    right: 0,
                    op: PolicyOp::Not,
                },
                span,
            );
            Ok(Some(dest))
        }
    }

    /// Map a [`FieldNode`] to the dotted property path used for count
    /// resolution.  Built-in field kinds (`type`, `id`, …) are returned
    /// as-is; aliases go through [`resolve_alias_path`] which normalises
    /// and lowercases when the alias catalog is loaded.
    fn extract_field_count_path(
        &self,
        field: &crate::languages::azure_policy::ast::FieldNode,
        span: &crate::lexer::Span,
    ) -> Result<String> {
        match &field.kind {
            FieldKind::Type => Ok("type".to_string()),
            FieldKind::Id => Ok("id".to_string()),
            FieldKind::Kind => Ok("kind".to_string()),
            FieldKind::Name => Ok("name".to_string()),
            FieldKind::Location => Ok("location".to_string()),
            FieldKind::FullName => Ok("fullName".to_string()),
            FieldKind::IdentityType => Ok("identity.type".to_string()),
            FieldKind::IdentityField(subpath) => {
                Ok(format!("identity.{}", subpath.to_ascii_lowercase()))
            }
            FieldKind::ApiVersion => Ok("apiVersion".to_string()),
            FieldKind::Tags => Ok("tags".to_string()),
            FieldKind::Tag(tag) => Ok(format!("tags.{}", tag)),
            FieldKind::Alias(path) => self.resolve_alias_path(path, span),
            FieldKind::Expr(_) => {
                bail!(span.error("count over expression field is not supported in core subset",))
            }
        }
    }

    /// Emit a single-level `ForEach` count loop.
    ///
    /// Iterates `collection_reg`, pushes a [`CountBinding`] for the duration
    /// of the loop body (so nested `current()` / field references resolve),
    /// optionally guards with the where clause, and increments a counter
    /// register on each passing iteration.
    ///
    /// Returns the register holding the final count.
    fn compile_count_loop(
        &mut self,
        collection_reg: u8,
        binding_name: Option<String>,
        field_wildcard_prefix: Option<String>,
        where_constraint: Option<&Constraint>,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let count_reg = self.load_literal(Value::from(0_i64), span)?;
        // Hoist the increment constant above the loop.
        let one_reg = self.load_literal(Value::from(1_i64), span)?;
        let key_reg = self.alloc_register()?;
        let current_reg = self.alloc_register()?;
        let loop_result_reg = self.alloc_register()?;

        let params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::ForEach,
            collection: collection_reg,
            key_reg,
            value_reg: current_reg,
            result_reg: loop_result_reg,
            body_start: 0,
            loop_end: 0,
        });

        self.emit(Instruction::LoopStart { params_index }, span);

        let body_start_u16 = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        self.count_bindings.push(CountBinding {
            name: binding_name,
            field_wildcard_prefix,
            current_reg,
        });

        // Compile where clause body (if present) as a conditional increment.
        if let Some(where_clause) = where_constraint {
            let where_reg = self.compile_constraint(where_clause)?;
            self.emit(
                Instruction::Guard {
                    register: where_reg,
                    mode: GuardMode::Condition,
                },
                span,
            );
        }

        self.emit(
            Instruction::Add {
                dest: count_reg,
                left: count_reg,
                right: one_reg,
            },
            span,
        );

        self.count_bindings.pop();

        self.emit(
            Instruction::LoopNext {
                body_start: body_start_u16,
                loop_end: 0,
            },
            span,
        );

        let loop_end_u16 = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        self.program.update_loop_params(params_index, |params| {
            params.body_start = body_start_u16;
            params.loop_end = loop_end_u16;
        });

        if let Some(Instruction::LoopNext { loop_end, .. }) = self.program.instructions.last_mut() {
            *loop_end = loop_end_u16;
        }

        Ok(count_reg)
    }

    // -- count existence optimization (Any mode) ---------------------------

    /// Try to compile a count condition as a `LoopMode::Any` loop when the
    /// operator + RHS form an existence check (e.g., `count > 0`).
    ///
    /// Returns `Some(result_reg)` if optimized, `None` to fall back to the
    /// generic count + compare path.
    pub(super) fn try_compile_count_as_any(
        &mut self,
        count_node: &CountNode,
        condition: &Condition,
    ) -> Result<Option<u8>> {
        // Determine whether the operator+RHS is an existence pattern.
        let exists = match Self::classify_existence_pattern(condition) {
            Some(e) => e,
            None => return Ok(None),
        };

        // Keep the where clause optional so plain `count(field: 'a[*]') > 0`
        // can also use the early-exit Any lowering.
        let where_constraint = match count_node {
            CountNode::Field { where_, .. } | CountNode::Value { where_, .. } => where_.as_deref(),
        };

        self.observed_uses_count = true;

        // Resolve collection and compile as Any loop.
        let any_result = match count_node {
            CountNode::Value {
                span, value, name, ..
            } => {
                let collection_reg = self.compile_value_or_expr(value, span)?;
                self.compile_count_any_loop(
                    collection_reg,
                    name.as_ref().map(|n| n.name.clone()),
                    None,
                    where_constraint,
                    span,
                )?
            }
            CountNode::Field { span, field, .. } => {
                // Multi-wildcard field paths use nested Any loops.
                // Resolve outer bindings so we start from the bound element.
                let field_path = self.extract_field_count_path(field, span)?;
                let (_, suffix) = split_count_wildcard_path(&field_path)
                    .map_err(|e| span.error(&e.to_string()))?;
                if suffix.as_ref().is_some_and(|s| s.contains("[*]")) {
                    // Skip the nested Any optimization when there is no where
                    // clause.  The non-optimized path in `compile_count_nested`
                    // uses `Instruction::Count` for the innermost level, which
                    // returns `Undefined` when the collection is missing or
                    // non-iterable.  The Any-based lowering instead treats a
                    // missing collection as empty (Any → false), so
                    // `Not(false)` → true, changing `count == 0` from false to
                    // true.  Falling back to the generic count+compare path
                    // preserves the Undefined-propagation semantics.
                    let Some(wc) = where_constraint else {
                        return Ok(None);
                    };

                    if let Some(binding) = self.resolve_count_binding(&field_path)? {
                        if let Some(outer_prefix) = &binding.field_wildcard_prefix {
                            let lc_prefix = outer_prefix.to_ascii_lowercase();
                            let expected_prefix = format!("{}[*].", lc_prefix);
                            if let Some(inner_path) = field_path
                                .to_ascii_lowercase()
                                .strip_prefix(&expected_prefix)
                            {
                                let inner_path = inner_path.to_string();
                                return self.compile_count_nested_any(
                                    Some(binding.current_reg),
                                    &inner_path,
                                    wc,
                                    outer_prefix,
                                    exists,
                                    span,
                                );
                            }
                        }
                    }
                    return self.compile_count_nested_any(None, &field_path, wc, "", exists, span);
                }

                let (collection_reg, prefix) = self.resolve_count_field_collection(field, span)?;
                self.compile_count_any_loop(
                    collection_reg,
                    None,
                    Some(prefix),
                    where_constraint,
                    span,
                )?
            }
        };

        if exists {
            Ok(Some(any_result))
        } else {
            let dest = self.alloc_register()?;
            self.emit(
                Instruction::PolicyCondition {
                    dest,
                    left: any_result,
                    right: 0,
                    op: PolicyOp::Not,
                },
                &condition.span,
            );
            Ok(Some(dest))
        }
    }

    /// Check whether a count condition's operator + RHS form an existence
    /// pattern.  Returns `Some(true)` for "at least one" semantics,
    /// `Some(false)` for "none" semantics, or `None` if not applicable.
    fn classify_existence_pattern(condition: &Condition) -> Option<bool> {
        let n = match &condition.rhs {
            ValueOrExpr::Value(JsonValue::Number(_, s)) => s.parse::<i64>().ok()?,
            _ => return None,
        };
        match (&condition.operator.kind, n) {
            (OperatorKind::Greater, 0)
            | (OperatorKind::GreaterOrEquals, 1)
            | (OperatorKind::NotEquals, 0) => Some(true),
            (OperatorKind::Equals, 0)
            | (OperatorKind::Less, 1)
            | (OperatorKind::LessOrEquals, 0) => Some(false),
            _ => None,
        }
    }

    /// Compile a count's where clause as a `LoopMode::Any` loop.
    ///
    /// The result register is `true` if any element satisfies the where
    /// constraint (or simply exists when `where_constraint` is `None`),
    /// `false` otherwise.  The loop exits on the first match.
    fn compile_count_any_loop(
        &mut self,
        collection_reg: u8,
        binding_name: Option<String>,
        field_wildcard_prefix: Option<String>,
        where_constraint: Option<&Constraint>,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let key_reg = self.alloc_register()?;
        let current_reg = self.alloc_register()?;
        let result_reg = self.alloc_register()?;

        let params_index = self.program.add_loop_params(LoopStartParams {
            mode: LoopMode::Any,
            collection: collection_reg,
            key_reg,
            value_reg: current_reg,
            result_reg,
            body_start: 0,
            loop_end: 0,
        });

        self.emit(Instruction::LoopStart { params_index }, span);

        let body_start = u16::try_from(self.program.instructions.len())
            .map_err(|_| anyhow!("instruction index overflow"))?;

        self.count_bindings.push(CountBinding {
            name: binding_name,
            field_wildcard_prefix,
            current_reg,
        });

        if let Some(wc) = where_constraint {
            let where_reg = self.compile_constraint(wc)?;
            self.emit(
                Instruction::Guard {
                    register: where_reg,
                    mode: GuardMode::Condition,
                },
                span,
            );
        }

        self.count_bindings.pop();

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

        Ok(result_reg)
    }

    /// Find the innermost active count binding that covers `field_path`.
    ///
    /// Matching rules (all case-insensitive):
    /// 1. **Named binding** — `field_path` equals the binding's `name`.
    /// 2. **Wildcard prefix** — `field_path` matches the binding's prefix,
    ///    its `prefix[*]` form, or starts with `prefix.` / `prefix[*].`.
    ///
    /// Bindings are searched innermost-first (reverse stack order) so a
    /// nested count's binding shadows an outer one for the same prefix.
    pub(super) fn resolve_count_binding(&self, field_path: &str) -> Result<Option<CountBinding>> {
        let fp = field_path.to_ascii_lowercase();
        for binding in self.count_bindings.iter().rev() {
            if let Some(name) = &binding.name {
                if fp.eq_ignore_ascii_case(name) {
                    return Ok(Some(binding.clone()));
                }
            }

            if let Some(prefix) = &binding.field_wildcard_prefix {
                let lc_prefix = prefix.to_ascii_lowercase();
                let wildcard_prefix = format!("{}[*]", lc_prefix);
                let prefix_dot = format!("{}.", lc_prefix);
                let wildcard_dot = format!("{}.", wildcard_prefix);
                if fp == lc_prefix
                    || fp.starts_with(&prefix_dot)
                    || fp == wildcard_prefix
                    || fp.starts_with(&wildcard_dot)
                {
                    return Ok(Some(binding.clone()));
                }
            }
        }

        Ok(None)
    }

    /// Compile a field reference relative to an active count binding.
    ///
    /// If `field_path` matches the binding exactly (name or prefix),
    /// emits a `Move` from the binding's current-element register.
    /// If `field_path` extends past the binding (e.g. `prefix.sub.key`),
    /// navigates the suffix via chained index lookups.  All comparisons
    /// are case-insensitive.
    pub(super) fn compile_from_binding(
        &mut self,
        binding: &CountBinding,
        field_path: &str,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let fp = field_path.to_ascii_lowercase();

        if let Some(name) = &binding.name {
            if fp.eq_ignore_ascii_case(name) {
                let dest = self.alloc_register()?;
                self.emit(
                    Instruction::Move {
                        dest,
                        src: binding.current_reg,
                    },
                    span,
                );
                return Ok(dest);
            }
        }

        if let Some(prefix) = &binding.field_wildcard_prefix {
            let lc_prefix = prefix.to_ascii_lowercase();
            let wildcard_prefix = format!("{}[*]", lc_prefix);

            if fp == lc_prefix || fp == wildcard_prefix {
                let dest = self.alloc_register()?;
                self.emit(
                    Instruction::Move {
                        dest,
                        src: binding.current_reg,
                    },
                    span,
                );
                return Ok(dest);
            }

            let prefix_dot = format!("{}.", lc_prefix);
            if let Some(suffix) = fp.strip_prefix(&prefix_dot) {
                return self.compile_suffix_from_binding(binding.current_reg, suffix, span);
            }

            let wildcard_dot = format!("{}[*].", lc_prefix);
            if let Some(suffix) = fp.strip_prefix(&wildcard_dot) {
                return self.compile_suffix_from_binding(binding.current_reg, suffix, span);
            }
        }

        bail!(span.error(&format!(
            "invalid current count binding for field path '{}'",
            field_path
        )))
    }

    /// Compile a suffix path from a binding's current register.
    ///
    /// If the suffix contains `[*]` (from a nested count context), only the
    /// portion before the first `[*]` is used for navigation.  The inner
    /// count's loop will handle the iteration.
    fn compile_suffix_from_binding(
        &mut self,
        base_reg: u8,
        suffix: &str,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        // Strip any trailing [*] or [*].suffix — we only navigate to the
        // array itself; the count loop iterates its elements.
        let nav_path = suffix
            .split_once("[*]")
            .map_or(suffix, |(prefix, _)| prefix);
        // Lowercase to match normalizer-lowercased keys.
        let nav_path = nav_path.to_ascii_lowercase();
        let parts = split_path_without_wildcards(&nav_path)?;
        let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
        self.emit_chained_index_literal_path(base_reg, &refs, span)
    }

    /// Compile a `current('key')` reference inside a count's where clause.
    ///
    /// Resolution is two-phase:
    /// 1. Try matching `key` directly against the active binding stack
    ///    (case-insensitive).  This handles literal alias paths and
    ///    named value-count bindings.
    /// 2. If no direct match, resolve `key` through the alias catalog
    ///    and retry.  When the catalog is loaded and fallback is disabled,
    ///    alias-resolution errors propagate so the caller sees "unknown
    ///    alias" rather than a generic scope error.
    ///
    /// Bails with a "used outside an active count scope" error if neither
    /// phase finds a matching binding.
    pub(super) fn compile_current_reference(
        &mut self,
        key: &str,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let resolve_for_key = |compiler: &mut Self, candidate: &str| -> Result<Option<u8>> {
            let lc_candidate = candidate.to_ascii_lowercase();
            for binding in compiler.count_bindings.iter().rev() {
                if let Some(name) = &binding.name {
                    let lc_name = name.to_ascii_lowercase();
                    if lc_candidate == lc_name {
                        let current_reg = binding.current_reg;
                        let dest = compiler.alloc_register()?;
                        compiler.emit(
                            Instruction::Move {
                                dest,
                                src: current_reg,
                            },
                            span,
                        );
                        return Ok(Some(dest));
                    }

                    let name_dot = format!("{}.", lc_name);
                    if let Some(suffix) = lc_candidate.strip_prefix(&name_dot) {
                        let parts = split_path_without_wildcards(suffix)?;
                        let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                        return compiler
                            .emit_chained_index_literal_path(binding.current_reg, &refs, span)
                            .map(Some);
                    }
                }

                if let Some(prefix) = &binding.field_wildcard_prefix {
                    let lc_prefix = prefix.to_ascii_lowercase();
                    if lc_candidate == lc_prefix || lc_candidate == format!("{}[*]", lc_prefix) {
                        let current_reg = binding.current_reg;
                        let dest = compiler.alloc_register()?;
                        compiler.emit(
                            Instruction::Move {
                                dest,
                                src: current_reg,
                            },
                            span,
                        );
                        return Ok(Some(dest));
                    }

                    let prefix_dot = format!("{}.", lc_prefix);
                    if let Some(suffix) = lc_candidate.strip_prefix(&prefix_dot) {
                        return compiler
                            .compile_suffix_from_binding(binding.current_reg, suffix, span)
                            .map(Some);
                    }

                    let prefix_wildcard_dot = format!("{}[*].", lc_prefix);
                    if let Some(suffix) = lc_candidate.strip_prefix(&prefix_wildcard_dot) {
                        return compiler
                            .compile_suffix_from_binding(binding.current_reg, suffix, span)
                            .map(Some);
                    }
                }
            }

            Ok(None)
        };

        if let Some(result) = resolve_for_key(self, key)? {
            return Ok(result);
        }

        // Try resolving via the alias catalog.  When the catalog is loaded
        // and fallback is disabled, propagate alias-resolution errors so the
        // caller sees "unknown alias" instead of the generic "outside an
        // active count scope" message.
        match self.resolve_alias_path(key, span) {
            Ok(normalized_key) if normalized_key != key => {
                if let Some(result) = resolve_for_key(self, &normalized_key)? {
                    return Ok(result);
                }
            }
            Err(e) if !self.alias_map.is_empty() && !self.alias_fallback_to_raw => {
                return Err(e);
            }
            _ => {}
        }

        bail!(span.error(&format!(
            "current('{}') is used outside an active count scope",
            key
        )))
    }
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]
mod tests {
    use alloc::string::ToString as _;
    use alloc::vec;
    use alloc::vec::Vec;

    use crate::languages::azure_policy::ast::{
        Condition, Constraint, CountNode, FieldKind, FieldNode, JsonValue, OperatorKind,
        OperatorNode, ValueOrExpr,
    };
    use crate::languages::azure_policy::compiler::core::{Compiler, CountBinding};
    use crate::lexer::Source;
    use crate::rvm::instructions::{GuardMode, LoopMode, PolicyOp};
    use crate::rvm::Instruction;

    fn dummy_span() -> crate::lexer::Span {
        let source = Source::from_contents("test".into(), " ".into()).unwrap();
        crate::lexer::Span {
            source,
            line: 1,
            col: 1,
            start: 0,
            end: 0,
        }
    }

    // -----------------------------------------------------------------------
    // resolve_count_binding
    // -----------------------------------------------------------------------

    #[test]
    fn resolve_binding_empty_stack() {
        let c = Compiler::new();
        assert!(c.resolve_count_binding("a[*].b").unwrap().is_none());
    }

    #[test]
    fn resolve_binding_by_field_prefix() {
        let mut c = Compiler::new();
        c.count_bindings.push(CountBinding {
            name: None,
            field_wildcard_prefix: Some("a".to_string()),
            current_reg: 5,
        });
        let binding = c.resolve_count_binding("a[*].b").unwrap().unwrap();
        assert_eq!(binding.current_reg, 5);
        assert_eq!(binding.field_wildcard_prefix.as_deref(), Some("a"));
    }

    #[test]
    fn resolve_binding_by_name() {
        let mut c = Compiler::new();
        c.count_bindings.push(CountBinding {
            name: Some("myCollection".to_string()),
            field_wildcard_prefix: None,
            current_reg: 3,
        });
        let binding = c.resolve_count_binding("myCollection").unwrap().unwrap();
        assert_eq!(binding.current_reg, 3);
    }

    #[test]
    fn resolve_binding_case_insensitive() {
        let mut c = Compiler::new();
        c.count_bindings.push(CountBinding {
            name: Some("MyCollection".to_string()),
            field_wildcard_prefix: None,
            current_reg: 4,
        });
        // Lookup with different casing should still match.
        let binding = c.resolve_count_binding("mycollection").unwrap().unwrap();
        assert_eq!(binding.current_reg, 4);

        let binding_upper = c.resolve_count_binding("MYCOLLECTION").unwrap().unwrap();
        assert_eq!(binding_upper.current_reg, 4);
    }

    #[test]
    fn resolve_binding_field_prefix_case_insensitive() {
        let mut c = Compiler::new();
        c.count_bindings.push(CountBinding {
            name: None,
            field_wildcard_prefix: Some("Microsoft.Test/resource".to_string()),
            current_reg: 6,
        });
        // Mixed-case lookup against the prefix.
        let binding = c
            .resolve_count_binding("microsoft.test/resource[*].prop")
            .unwrap()
            .unwrap();
        assert_eq!(binding.current_reg, 6);
    }

    #[test]
    fn resolve_binding_innermost_wins() {
        let mut c = Compiler::new();
        c.count_bindings.push(CountBinding {
            name: None,
            field_wildcard_prefix: Some("a".to_string()),
            current_reg: 1,
        });
        c.count_bindings.push(CountBinding {
            name: None,
            field_wildcard_prefix: Some("a[*].b".to_string()),
            current_reg: 2,
        });
        // The inner binding (a[*].b) matches a[*].b[*].c, and since we
        // iterate in reverse, it wins.
        let binding = c.resolve_count_binding("a[*].b[*].c").unwrap().unwrap();
        assert_eq!(binding.current_reg, 2);
    }

    #[test]
    fn resolve_binding_no_match() {
        let mut c = Compiler::new();
        c.count_bindings.push(CountBinding {
            name: None,
            field_wildcard_prefix: Some("x".to_string()),
            current_reg: 1,
        });
        assert!(c.resolve_count_binding("y[*].z").unwrap().is_none());
    }

    // -----------------------------------------------------------------------
    // compile_count_nested — instruction shape for multi-wildcard paths
    // -----------------------------------------------------------------------

    #[test]
    fn nested_count_no_where_emits_foreach_and_count() {
        let mut c = Compiler::new();
        let span = dummy_span();
        // Compile a[*].b[*] (no where clause) starting from resource root.
        let result_reg = c
            .compile_count_nested(None, "a[*].b[*]", None, "", &span)
            .unwrap();

        // The outer loop should be ForEach (accumulating inner counts).
        // Find the first LoopStart and check its mode.
        let first_loop_idx = c
            .program
            .instructions
            .iter()
            .position(|i| matches!(i, Instruction::LoopStart { .. }))
            .expect("should have a LoopStart");

        if let Instruction::LoopStart { params_index } = c.program.instructions[first_loop_idx] {
            let params = c
                .program
                .instruction_data
                .get_loop_params(params_index)
                .unwrap();
            assert_eq!(
                params.mode,
                LoopMode::ForEach,
                "outer loop should be ForEach"
            );
        }

        // The innermost level has no where clause, so it should use Count
        // instruction (direct count, no loop).
        assert!(
            c.program
                .instructions
                .iter()
                .any(|i| matches!(i, Instruction::Count { .. })),
            "innermost level without where should emit Count"
        );

        // Should also have an Add instruction to accumulate.
        assert!(
            c.program
                .instructions
                .iter()
                .any(|i| matches!(i, Instruction::Add { .. })),
            "should accumulate inner counts via Add"
        );

        // The result register should be valid.
        assert!(result_reg < c.register_counter);
    }

    #[test]
    fn nested_count_with_where_emits_foreach_loops() {
        let mut c = Compiler::new();
        let span = dummy_span();

        // A simple where clause: { field: "type", equals: "someType" }
        let where_clause = Constraint::Condition(alloc::boxed::Box::new(Condition {
            span: dummy_span(),
            lhs: crate::languages::azure_policy::ast::Lhs::Field(FieldNode {
                span: dummy_span(),
                kind: FieldKind::Type,
            }),
            operator: OperatorNode {
                span: dummy_span(),
                kind: OperatorKind::Equals,
            },
            rhs: ValueOrExpr::Value(JsonValue::Str(dummy_span(), "someType".to_string())),
        }));

        let _result_reg = c
            .compile_count_nested(None, "a[*].b[*]", Some(&where_clause), "", &span)
            .unwrap();

        // With a where clause the innermost level should emit a loop (not
        // a bare Count instruction).
        let loop_starts: Vec<_> = c
            .program
            .instructions
            .iter()
            .filter(|i| matches!(i, Instruction::LoopStart { .. }))
            .collect();
        assert!(
            loop_starts.len() >= 2,
            "nested count with where should emit at least 2 LoopStart instructions, got {}",
            loop_starts.len()
        );
    }

    // -----------------------------------------------------------------------
    // compile_count_nested_any — existence-pattern optimization for nested paths
    // -----------------------------------------------------------------------

    #[test]
    fn nested_any_exists_true_emits_any_loops() {
        let mut c = Compiler::new();
        let span = dummy_span();

        let where_clause = Constraint::Condition(alloc::boxed::Box::new(Condition {
            span: dummy_span(),
            lhs: crate::languages::azure_policy::ast::Lhs::Field(FieldNode {
                span: dummy_span(),
                kind: FieldKind::Type,
            }),
            operator: OperatorNode {
                span: dummy_span(),
                kind: OperatorKind::Equals,
            },
            rhs: ValueOrExpr::Value(JsonValue::Str(dummy_span(), "someType".to_string())),
        }));

        let result = c
            .compile_count_nested_any(
                None,
                "a[*].b[*]",
                &where_clause,
                "",
                true, // exists = true → count > 0
                &span,
            )
            .unwrap();
        assert!(result.is_some(), "nested any should return Some");

        // All loops should be LoopMode::Any for the existence optimization.
        for instr in &c.program.instructions {
            if let Instruction::LoopStart { params_index } = instr {
                let params = c
                    .program
                    .instruction_data
                    .get_loop_params(*params_index)
                    .unwrap();
                assert_eq!(
                    params.mode,
                    LoopMode::Any,
                    "existence pattern should use Any loops"
                );
            }
        }
    }

    #[test]
    fn nested_any_exists_false_emits_not() {
        let mut c = Compiler::new();
        let span = dummy_span();

        let where_clause = Constraint::Condition(alloc::boxed::Box::new(Condition {
            span: dummy_span(),
            lhs: crate::languages::azure_policy::ast::Lhs::Field(FieldNode {
                span: dummy_span(),
                kind: FieldKind::Type,
            }),
            operator: OperatorNode {
                span: dummy_span(),
                kind: OperatorKind::Equals,
            },
            rhs: ValueOrExpr::Value(JsonValue::Str(dummy_span(), "someType".to_string())),
        }));

        let result = c
            .compile_count_nested_any(
                None,
                "a[*].b[*]",
                &where_clause,
                "",
                false, // exists = false → count == 0
                &span,
            )
            .unwrap();
        assert!(result.is_some());

        // Should have a PolicyCondition with Not op for the negation.
        assert!(
            c.program.instructions.iter().any(|i| matches!(
                i,
                Instruction::PolicyCondition { op, .. } if *op == PolicyOp::Not
            )),
            "count == 0 pattern should negate with PolicyCondition::Not"
        );
    }

    // -----------------------------------------------------------------------
    // try_compile_count_as_any — existence detection via operator + RHS
    // -----------------------------------------------------------------------

    /// Helper: build a Condition with count LHS, given operator and numeric RHS.
    fn make_count_condition(count_node: CountNode, op: OperatorKind, rhs_number: i64) -> Condition {
        Condition {
            span: dummy_span(),
            lhs: crate::languages::azure_policy::ast::Lhs::Count(count_node),
            operator: OperatorNode {
                span: dummy_span(),
                kind: op,
            },
            rhs: ValueOrExpr::Value(JsonValue::Number(dummy_span(), rhs_number.to_string())),
        }
    }

    fn make_value_count_with_where() -> CountNode {
        CountNode::Value {
            span: dummy_span(),
            value: ValueOrExpr::Value(JsonValue::Array(
                dummy_span(),
                vec![
                    JsonValue::Number(dummy_span(), "1".to_string()),
                    JsonValue::Number(dummy_span(), "2".to_string()),
                    JsonValue::Number(dummy_span(), "3".to_string()),
                ],
            )),
            name: None,
            where_: Some(alloc::boxed::Box::new(Constraint::Condition(
                alloc::boxed::Box::new(Condition {
                    span: dummy_span(),
                    lhs: crate::languages::azure_policy::ast::Lhs::Value {
                        key_span: dummy_span(),
                        value: ValueOrExpr::Value(JsonValue::Number(dummy_span(), "1".to_string())),
                    },
                    operator: OperatorNode {
                        span: dummy_span(),
                        kind: OperatorKind::Equals,
                    },
                    rhs: ValueOrExpr::Value(JsonValue::Number(dummy_span(), "1".to_string())),
                }),
            ))),
        }
    }

    #[test]
    fn any_optimization_greater_zero() {
        let mut c = Compiler::new();
        let count_node = make_value_count_with_where();
        let condition = make_count_condition(count_node.clone(), OperatorKind::Greater, 0);
        let result = c.try_compile_count_as_any(&count_node, &condition).unwrap();
        assert!(
            result.is_some(),
            "count > 0 should trigger Any optimization"
        );

        // The loop should use LoopMode::Any.
        for instr in &c.program.instructions {
            if let Instruction::LoopStart { params_index } = instr {
                let params = c
                    .program
                    .instruction_data
                    .get_loop_params(*params_index)
                    .unwrap();
                assert_eq!(params.mode, LoopMode::Any);
            }
        }
    }

    #[test]
    fn any_optimization_equals_zero_negates() {
        let mut c = Compiler::new();
        let count_node = make_value_count_with_where();
        let condition = make_count_condition(count_node.clone(), OperatorKind::Equals, 0);
        let result = c.try_compile_count_as_any(&count_node, &condition).unwrap();
        assert!(
            result.is_some(),
            "count == 0 should trigger Any optimization"
        );

        // Should negate: PolicyCondition with Not.
        assert!(
            c.program.instructions.iter().any(|i| matches!(
                i,
                Instruction::PolicyCondition { op, .. } if *op == PolicyOp::Not
            )),
            "count == 0 should negate"
        );
    }

    #[test]
    fn any_optimization_not_triggered_for_equals_two() {
        let mut c = Compiler::new();
        let count_node = make_value_count_with_where();
        let condition = make_count_condition(count_node.clone(), OperatorKind::Equals, 2);
        let result = c.try_compile_count_as_any(&count_node, &condition).unwrap();
        assert!(
            result.is_none(),
            "count == 2 is not an existence pattern, should return None"
        );
    }

    #[test]
    fn any_optimization_no_where_uses_any_loop() {
        let mut c = Compiler::new();
        let count_node = CountNode::Value {
            span: dummy_span(),
            value: ValueOrExpr::Value(JsonValue::Array(dummy_span(), vec![])),
            name: None,
            where_: None,
        };
        let condition = make_count_condition(count_node.clone(), OperatorKind::Greater, 0);
        let result = c.try_compile_count_as_any(&count_node, &condition).unwrap();
        assert!(
            result.is_some(),
            "without where clause, Any optimization should still apply for existence patterns"
        );

        // Verify it emitted an Any loop.
        let has_any_loop = c.program.instructions.iter().any(|instr| {
            if let Instruction::LoopStart { params_index } = instr {
                let params = c
                    .program
                    .instruction_data
                    .get_loop_params(*params_index)
                    .unwrap();
                params.mode == LoopMode::Any
            } else {
                false
            }
        });
        assert!(has_any_loop, "should emit a LoopMode::Any loop");
    }

    // -----------------------------------------------------------------------
    // compile_count — value-based count loop
    // -----------------------------------------------------------------------

    #[test]
    fn compile_value_count_without_where() {
        let mut c = Compiler::new();
        let count_node = CountNode::Value {
            span: dummy_span(),
            value: ValueOrExpr::Value(JsonValue::Array(
                dummy_span(),
                vec![
                    JsonValue::Number(dummy_span(), "1".to_string()),
                    JsonValue::Number(dummy_span(), "2".to_string()),
                ],
            )),
            name: None,
            where_: None,
        };

        let result_reg = c.compile_count(&count_node).unwrap();
        assert!(result_reg < c.register_counter);

        // Should emit a ForEach loop with Add to increment count.
        let has_loop = c
            .program
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::LoopStart { .. }));
        let has_add = c
            .program
            .instructions
            .iter()
            .any(|i| matches!(i, Instruction::Add { .. }));
        assert!(has_loop, "value count should emit a loop");
        assert!(has_add, "value count should emit Add to increment");
    }

    #[test]
    fn compile_value_count_with_where() {
        let mut c = Compiler::new();
        let count_node = make_value_count_with_where();

        let result_reg = c.compile_count(&count_node).unwrap();
        assert!(result_reg < c.register_counter);

        // Should have Guard instruction for the where clause.
        assert!(
            c.program.instructions.iter().any(|i| matches!(
                i,
                Instruction::Guard {
                    mode: GuardMode::Condition,
                    ..
                }
            )),
            "count with where should emit Guard for where condition"
        );
    }

    // -----------------------------------------------------------------------
    // classify_existence_pattern — direct coverage of all recognized patterns
    // -----------------------------------------------------------------------

    /// Helper to build a Condition with the given operator and numeric RHS
    /// (LHS is irrelevant for classify_existence_pattern).
    fn make_condition_for_classify(op: OperatorKind, rhs: i64) -> Condition {
        Condition {
            span: dummy_span(),
            lhs: crate::languages::azure_policy::ast::Lhs::Field(FieldNode {
                span: dummy_span(),
                kind: FieldKind::Type,
            }),
            operator: OperatorNode {
                span: dummy_span(),
                kind: op,
            },
            rhs: ValueOrExpr::Value(JsonValue::Number(dummy_span(), rhs.to_string())),
        }
    }

    #[test]
    fn classify_existence_all_patterns() {
        // "at least one" patterns → Some(true)
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::Greater,
                0
            )),
            Some(true),
            "> 0"
        );
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::GreaterOrEquals,
                1
            )),
            Some(true),
            ">= 1"
        );
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::NotEquals,
                0
            )),
            Some(true),
            "!= 0"
        );

        // "none" patterns → Some(false)
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::Equals,
                0
            )),
            Some(false),
            "== 0"
        );
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::Less,
                1
            )),
            Some(false),
            "< 1"
        );
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::LessOrEquals,
                0
            )),
            Some(false),
            "<= 0"
        );

        // Non-existence patterns → None
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::Equals,
                2
            )),
            None,
            "== 2"
        );
        assert_eq!(
            Compiler::classify_existence_pattern(&make_condition_for_classify(
                OperatorKind::Greater,
                1
            )),
            None,
            "> 1"
        );
    }

    // -----------------------------------------------------------------------
    // try_compile_count_as_any — nested no-where field count is skipped
    // -----------------------------------------------------------------------

    #[test]
    fn any_optimization_skips_nested_no_where_field_count() {
        // A nested wildcard field path without a where clause should NOT be
        // optimised into Any loops because of Undefined-propagation semantics.
        let mut c = Compiler::new();
        let count_node = CountNode::Field {
            span: dummy_span(),
            field: FieldNode {
                span: dummy_span(),
                kind: FieldKind::Alias("a[*].b[*]".to_string()),
            },
            where_: None,
        };
        let condition = make_count_condition(count_node.clone(), OperatorKind::Equals, 0);
        let result = c.try_compile_count_as_any(&count_node, &condition).unwrap();
        assert!(
            result.is_none(),
            "nested no-where field count should fall back to generic path"
        );
    }
}
