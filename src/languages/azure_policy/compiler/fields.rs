// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Field-kind and resource-path compilation.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::languages::azure_policy::ast::{Expr, ExprLiteral, FieldKind};
use crate::rvm::instructions::{LoopMode, LoopStartParams};
use crate::rvm::Instruction;

use super::core::Compiler;
use super::utils::{split_count_wildcard_path, split_path_without_wildcards};

impl Compiler {
    pub(super) fn compile_field_kind(
        &mut self,
        kind: &FieldKind,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let reg = match kind {
            FieldKind::Type => {
                self.record_field_kind("type");
                self.compile_resource_path_value("type", span)?
            }
            FieldKind::Id => {
                self.record_field_kind("id");
                self.compile_resource_path_value("id", span)?
            }
            FieldKind::Kind => {
                self.record_field_kind("kind");
                self.compile_resource_path_value("kind", span)?
            }
            FieldKind::Name => {
                self.record_field_kind("name");
                self.compile_resource_path_value("name", span)?
            }
            FieldKind::Location => {
                self.record_field_kind("location");
                self.compile_resource_path_value("location", span)?
            }
            FieldKind::FullName => {
                self.record_field_kind("fullName");
                self.compile_resource_path_value("fullName", span)?
            }
            FieldKind::Tags => {
                self.record_field_kind("tags");
                self.compile_resource_path_value("tags", span)?
            }
            FieldKind::IdentityType => {
                self.record_field_kind("identity.type");
                self.compile_resource_path_value("identity.type", span)?
            }
            FieldKind::IdentityField(ref subpath) => {
                let path = format!("identity.{}", subpath.to_ascii_lowercase());
                self.record_field_kind(&path);
                self.compile_resource_path_value(&path, span)?
            }
            FieldKind::ApiVersion => {
                self.record_field_kind("apiVersion");
                self.compile_resource_path_value("apiVersion", span)?
            }
            FieldKind::Tag(tag) => {
                self.record_field_kind("tags");
                self.record_tag_name(tag);
                let tag_lower = tag.to_ascii_lowercase();
                if let Some(override_reg) = self.resource_override_reg {
                    self.emit_chained_index_literal_path(override_reg, &["tags", &tag_lower], span)?
                } else {
                    let input_reg = self.load_input(span)?;
                    self.emit_chained_index_literal_path(
                        input_reg,
                        &["resource", "tags", &tag_lower],
                        span,
                    )?
                }
            }
            FieldKind::Alias(path) => {
                self.record_alias(path);
                let short = self.resolve_alias_path(path, span)?;
                self.compile_field_path_expression(&short, span)?
            }
            FieldKind::Expr(expr) => self.compile_dynamic_field_expr(expr, span)?,
        };
        Ok(reg)
    }

    /// Compile a dynamic field expression (`FieldKind::Expr`).
    fn compile_dynamic_field_expr(&mut self, expr: &Expr, span: &crate::lexer::Span) -> Result<u8> {
        if let Expr::Call { func, args, .. } = expr {
            if let Expr::Ident { name, .. } = func.as_ref() {
                if name.eq_ignore_ascii_case("if") {
                    if let [cond_arg, Expr::Literal {
                        value: ExprLiteral::String(alias_a),
                        ..
                    }, Expr::Literal {
                        value: ExprLiteral::String(alias_b),
                        ..
                    }] = args.as_slice()
                    {
                        self.record_alias(alias_a);
                        self.record_alias(alias_b);

                        let short_a = self.resolve_alias_path(alias_a, span)?;
                        let short_b = self.resolve_alias_path(alias_b, span)?;

                        let cond_reg = self.compile_expr(cond_arg)?;

                        let then_reg = self.compile_field_path_expression(&short_a, span)?;
                        self.emit_coalesce_undefined_to_null(then_reg, span);

                        let else_reg = self.compile_field_path_expression(&short_b, span)?;
                        self.emit_coalesce_undefined_to_null(else_reg, span);

                        return self.emit_builtin_call(
                            "azure.policy.if",
                            &[cond_reg, then_reg, else_reg],
                            span,
                        );
                    }
                }
            }
        }

        // Handle concat() that produces a tag path.
        if let Expr::Call { func, args, .. } = expr {
            if let Expr::Ident { name, .. } = func.as_ref() {
                if name.eq_ignore_ascii_case("concat") && !args.is_empty() {
                    if let Some(Expr::Literal {
                        value: ExprLiteral::String(first),
                        ..
                    }) = args.first()
                    {
                        if first == "tags"
                            || first.starts_with("tags.")
                            || first.starts_with("tags[")
                        {
                            self.observed_has_dynamic_fields = true;
                            let path_reg = self.compile_expr(expr)?;
                            let resource_reg = self.compile_resource_root(span)?;
                            return self.emit_builtin_call(
                                "azure.policy.resolve_field",
                                &[resource_reg, path_reg],
                                span,
                            );
                        }
                    }
                }
            }
        }

        bail!(span.error(
            "unsupported dynamic field expression; only \
             `if(cond, 'alias', 'alias')` and `concat('tags...', ...)` \
             patterns are supported",
        ));
    }

    pub(super) fn compile_field_path_expression(
        &mut self,
        field_path: &str,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        if let Some(binding) = self.resolve_count_binding(field_path)? {
            return self.compile_from_binding(&binding, field_path, span);
        }
        if field_path.contains("[*]") {
            return self.compile_field_wildcard_collect(field_path, span);
        }
        self.compile_resource_path_value(field_path, span)
    }

    pub(super) fn compile_resource_path_value(
        &mut self,
        field_path: &str,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let lowered = field_path.to_ascii_lowercase();

        if let Some(override_reg) = self.resource_override_reg {
            let parts = split_path_without_wildcards(&lowered)?;
            let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
            return self.emit_chained_index_literal_path(override_reg, &refs, span);
        }

        let input_reg = self.load_input(span)?;

        let mut path = Vec::new();
        path.push("resource".to_string());
        for part in split_path_without_wildcards(&lowered)? {
            path.push(part);
        }

        let refs = path.iter().map(String::as_str).collect::<Vec<_>>();
        self.emit_chained_index_literal_path(input_reg, &refs, span)
    }

    pub(super) fn compile_resource_root(&mut self, span: &crate::lexer::Span) -> Result<u8> {
        if let Some(override_reg) = self.resource_override_reg {
            return Ok(override_reg);
        }
        let input_reg = self.load_input(span)?;
        self.emit_chained_index_literal_path(input_reg, &["resource"], span)
    }

    // -- wildcard collection -----------------------------------------------

    pub(super) fn compile_field_wildcard_collect(
        &mut self,
        field_path: &str,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let result_reg = self.alloc_register()?;
        self.emit(Instruction::ArrayNew { dest: result_reg }, span);
        self.compile_wildcard_collect_inner(None, field_path, result_reg, span)?;
        Ok(result_reg)
    }

    fn compile_wildcard_collect_inner(
        &mut self,
        base_reg: Option<u8>,
        remaining_path: &str,
        result_reg: u8,
        span: &crate::lexer::Span,
    ) -> Result<()> {
        let (prefix, suffix) = split_count_wildcard_path(remaining_path)?;

        let prefix_lower = prefix.to_ascii_lowercase();

        let collection_reg = match base_reg {
            Some(base) if prefix_lower.is_empty() => base,
            Some(base) => {
                let parts = split_path_without_wildcards(&prefix_lower)?;
                let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                self.emit_chained_index_literal_path(base, &refs, span)?
            }
            None if prefix_lower.is_empty() => self.compile_resource_root(span)?,
            None => self.compile_resource_path_value(&prefix_lower, span)?,
        };

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

        match suffix {
            Some(ref s) if s.contains("[*]") => {
                self.compile_wildcard_collect_inner(Some(current_reg), s, result_reg, span)?;
            }
            Some(ref s) => {
                let s_lower = s.to_ascii_lowercase();
                let parts = split_path_without_wildcards(&s_lower)?;
                let refs = parts.iter().map(String::as_str).collect::<Vec<_>>();
                let val_reg = self.emit_chained_index_literal_path(current_reg, &refs, span)?;
                self.emit(
                    Instruction::ArrayPushDefined {
                        arr: result_reg,
                        value: val_reg,
                    },
                    span,
                );
            }
            None => {
                self.emit(
                    Instruction::ArrayPushDefined {
                        arr: result_reg,
                        value: current_reg,
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

        Ok(())
    }
}
