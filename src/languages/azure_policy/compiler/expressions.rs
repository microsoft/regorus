// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Template-expression and call-expression compilation.

use alloc::format;
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::languages::azure_policy::ast::{Expr, ExprLiteral, JsonValue, ValueOrExpr};
use crate::rvm::Instruction;
use crate::Value;

use super::core::Compiler;
use super::utils::{extract_string_literal, json_value_to_runtime};

/// Maximum nesting depth for recursive JSON value compilation.
const MAX_JSON_DEPTH: usize = 32;

impl Compiler {
    pub(super) fn compile_value_or_expr(
        &mut self,
        voe: &ValueOrExpr,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        match voe {
            ValueOrExpr::Value(value) => self.compile_json_value(value, span),
            ValueOrExpr::Expr { expr, .. } => self.compile_expr(expr),
        }
    }

    pub(super) fn compile_json_value(
        &mut self,
        value: &crate::languages::azure_policy::ast::JsonValue,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        self.compile_json_value_inner(value, span, 0)
    }

    fn compile_json_value_inner(
        &mut self,
        value: &crate::languages::azure_policy::ast::JsonValue,
        span: &crate::lexer::Span,
        depth: usize,
    ) -> Result<u8> {
        if depth > MAX_JSON_DEPTH {
            bail!(span.error(&format!(
                "JSON value nesting exceeds maximum depth of {MAX_JSON_DEPTH}"
            )));
        }

        use crate::languages::azure_policy::expr::ExprParser;
        use crate::languages::azure_policy::parser::is_template_expr;

        // Standalone string template expressions like `"[concat(...)]"`
        // must be compiled so they evaluate at runtime.
        if let JsonValue::Str(str_span, s) = value {
            if is_template_expr(s) {
                let inner = s
                    .strip_prefix('[')
                    .and_then(|inner| inner.strip_suffix(']'))
                    .ok_or_else(|| {
                        str_span.error("invalid template expression: missing brackets")
                    })?;
                let expr = ExprParser::parse_from_brackets(inner, str_span)
                    .map_err(|e| anyhow!("{}", e))?;
                return self.compile_expr(&expr);
            }
        }

        // Arrays: recursively compile elements so nested template expressions
        // are evaluated at runtime.
        if let JsonValue::Array(_, items) = value {
            if contains_template_expr(value) {
                return self.compile_dynamic_array(items, span, depth.saturating_add(1));
            }
            // Fall through: json_value_to_runtime handles `[[` unescaping for
            // string elements, so static arrays are converted correctly.
        }

        // Objects: recursively compile values so nested template expressions
        // are evaluated at runtime.
        if let JsonValue::Object(_, entries) = value {
            if contains_template_expr(value) {
                return self.compile_dynamic_object(entries, span, depth.saturating_add(1));
            }
        }

        // Static value — convert to runtime literal.
        // Enforce depth limit on static JSON to prevent stack overflow in
        // json_value_to_runtime's own recursion.  Use subtree-local depth (0),
        // not the compiler recursion depth, since the static subtree's nesting
        // is independent of how deep we are in dynamic compilation.
        check_json_depth(value, 0).map_err(|_| {
            anyhow!(span.error(&alloc::format!(
                "JSON value nesting exceeds maximum depth of {MAX_JSON_DEPTH}"
            )))
        })?;
        let runtime_value = json_value_to_runtime(value)?;
        self.load_literal(runtime_value, span)
    }

    /// Compile a JSON array where some elements may contain template expressions.
    fn compile_dynamic_array(
        &mut self,
        items: &[JsonValue],
        span: &crate::lexer::Span,
        depth: usize,
    ) -> Result<u8> {
        let mut element_regs = Vec::with_capacity(items.len());
        for item in items {
            let reg = self.compile_json_value_inner(item, item.span(), depth)?;
            element_regs.push(reg);
        }

        let arr_dest = self.alloc_register()?;
        let params = self.program.instruction_data.add_array_create_params(
            crate::rvm::instructions::ArrayCreateParams {
                dest: arr_dest,
                elements: element_regs,
            },
        );
        self.emit(
            Instruction::ArrayCreate {
                params_index: params,
            },
            span,
        );
        Ok(arr_dest)
    }

    /// Compile a JSON object where some values may contain template expressions.
    fn compile_dynamic_object(
        &mut self,
        entries: &[crate::languages::azure_policy::ast::ObjectEntry],
        span: &crate::lexer::Span,
        depth: usize,
    ) -> Result<u8> {
        let mut keys: Vec<(u16, u8)> = Vec::with_capacity(entries.len());
        for entry in entries {
            let val_reg = self.compile_json_value_inner(&entry.value, entry.value.span(), depth)?;
            let key_idx = self.add_literal_u16(Value::from(entry.key.clone()))?;
            keys.push((key_idx, val_reg));
        }
        super::effects::build_object_from_keys(self, keys, span)
    }

    pub(super) fn compile_expr(&mut self, expr: &Expr) -> Result<u8> {
        match expr {
            Expr::Literal { span, value } => {
                let v = match value {
                    ExprLiteral::Number(n) => Value::from_numeric_string(n)?,
                    ExprLiteral::String(s) => Value::from(s.clone()),
                    ExprLiteral::Bool(b) => Value::Bool(*b),
                };
                self.load_literal(v, span)
            }
            Expr::Ident { name, span } => match name.to_ascii_lowercase().as_str() {
                "true" => self.load_literal(Value::Bool(true), span),
                "false" => self.load_literal(Value::Bool(false), span),
                "null" => self.load_literal(Value::Null, span),
                _ => bail!(span.error(&alloc::format!(
                    "unsupported bare identifier in template expression: {}",
                    name
                ))),
            },
            Expr::Call { span, func, args } => self.compile_call_expr(span, func, args),
            Expr::Dot {
                span,
                object,
                field,
                ..
            } => {
                let object_reg = self.compile_expr(object)?;
                let dest = self.alloc_register()?;
                let literal_idx = self.add_literal_u16(Value::from(field.clone()))?;
                self.emit(
                    Instruction::IndexLiteral {
                        dest,
                        container: object_reg,
                        literal_idx,
                    },
                    span,
                );
                Ok(dest)
            }
            Expr::Index {
                span,
                object,
                index,
            } => {
                let object_reg = self.compile_expr(object)?;
                let index_reg = self.compile_expr(index)?;
                let dest = self.alloc_register()?;
                self.emit(
                    Instruction::Index {
                        dest,
                        container: object_reg,
                        key: index_reg,
                    },
                    span,
                );
                Ok(dest)
            }
        }
    }

    fn compile_call_expr(
        &mut self,
        span: &crate::lexer::Span,
        func: &Expr,
        args: &[Expr],
    ) -> Result<u8> {
        let Expr::Ident { name, .. } = func else {
            bail!(span.error("unsupported dynamic function expression"));
        };

        let function_name = name.to_ascii_lowercase();

        match function_name.as_str() {
            "parameters" => {
                let [first_arg] = args else {
                    bail!(span.error("parameters() requires exactly one argument"));
                };
                let param_name = extract_string_literal(first_arg)?;
                let input_reg = self.load_input(span)?;
                let params_reg =
                    self.emit_chained_index_literal_path(input_reg, &["parameters"], span)?;
                let defaults_reg = if let Some(reg) = self.cached_defaults_reg {
                    reg
                } else {
                    let reg = if let Some(ref defaults) = self.parameter_defaults {
                        self.load_literal(defaults.clone(), span)?
                    } else {
                        self.load_literal(Value::new_object(), span)?
                    };
                    self.cached_defaults_reg = Some(reg);
                    reg
                };
                let name_reg = self.load_literal(Value::from(param_name), span)?;
                self.emit_builtin_call(
                    "azure.policy.get_parameter",
                    &[params_reg, defaults_reg, name_reg],
                    span,
                )
            }
            "field" => {
                let [first_arg] = args else {
                    bail!(span.error("field() requires exactly one argument"));
                };
                let field_path = extract_string_literal(first_arg)?;
                let resolved = match field_path.to_ascii_lowercase().as_str() {
                    "type" | "id" | "kind" | "name" | "location" | "fullname" | "tags"
                    | "identity.type" | "apiversion" => field_path.clone(),
                    s if s.starts_with("identity.") => field_path.clone(),
                    s if s.starts_with("tags.") || s.starts_with("tags[") => field_path.clone(),
                    _ => self.resolve_alias_path(&field_path, span)?,
                };

                // The field() template function always reads from the primary
                // resource, even inside existenceCondition.
                let saved_override = self.resource_override_reg.take();
                let reg = self.compile_field_path_expression(&resolved, span)?;
                self.resource_override_reg = saved_override;

                let reg = if resolved.contains("[*]") {
                    if self.resolve_count_binding(&resolved)?.is_some() {
                        let arr = self.alloc_register()?;
                        self.emit(Instruction::ArrayNew { dest: arr }, span);
                        self.emit(Instruction::ArrayPush { arr, value: reg }, span);
                        arr
                    } else {
                        reg
                    }
                } else {
                    reg
                };

                self.emit_coalesce_undefined_to_null(reg, span);
                Ok(reg)
            }
            "current" => match args.first() {
                Some(first_arg) => {
                    let key = extract_string_literal(first_arg)?;
                    self.compile_current_reference(&key, span)
                }
                None => {
                    let binding = self.count_bindings.last().ok_or_else(|| {
                        anyhow::anyhow!("{}", span.error("current() used outside a count scope"))
                    })?;
                    let current_reg = binding.current_reg;
                    let dest = self.alloc_register()?;
                    self.emit(
                        crate::rvm::Instruction::Move {
                            dest,
                            src: current_reg,
                        },
                        span,
                    );
                    Ok(dest)
                }
            },
            "resourcegroup" => {
                if !args.is_empty() {
                    bail!(span.error("resourceGroup() takes no arguments"))
                }
                let ctx_reg = self.load_context(span)?;
                self.emit_chained_index_literal_path(ctx_reg, &["resourceGroup"], span)
            }
            "subscription" => {
                if !args.is_empty() {
                    bail!(span.error("subscription() takes no arguments"))
                }
                let ctx_reg = self.load_context(span)?;
                self.emit_chained_index_literal_path(ctx_reg, &["subscription"], span)
            }
            "requestcontext" => {
                if !args.is_empty() {
                    bail!(span.error("requestContext() takes no arguments"))
                }
                let ctx_reg = self.load_context(span)?;
                self.emit_chained_index_literal_path(ctx_reg, &["requestContext"], span)
            }
            "claims" => {
                if !args.is_empty() {
                    bail!(span.error("claims() takes no arguments"))
                }
                let ctx_reg = self.load_context(span)?;
                self.emit_chained_index_literal_path(ctx_reg, &["claims"], span)
            }
            "policy" => {
                if !args.is_empty() {
                    bail!(span.error("policy() takes no arguments"))
                }
                let ctx_reg = self.load_context(span)?;
                self.emit_chained_index_literal_path(ctx_reg, &["policy"], span)
            }
            "utcnow" => {
                if !args.is_empty() {
                    bail!(span.error("utcNow() takes no arguments"))
                }
                let ctx_reg = self.load_context(span)?;
                self.emit_chained_index_literal_path(ctx_reg, &["utcNow"], span)
            }
            "concat" | "if" | "and" | "not" | "tolower" | "toupper" | "replace" | "substring"
            | "length" | "add" | "equals" | "greaterorequals" | "lessorequals" | "contains" => self
                .compile_arm_template_function(&function_name, span, args)?
                .ok_or_else(|| anyhow!("{}", span.error("unreachable"))),

            other => {
                if let Some(dest) = self.compile_arm_template_function(other, span, args)? {
                    Ok(dest)
                } else {
                    bail!(span.error(&alloc::format!("unsupported template function '{}'", other)))
                }
            }
        }
    }

    pub(super) fn compile_call_args(&mut self, args: &[Expr]) -> Result<Vec<u8>> {
        let mut out = Vec::with_capacity(args.len());
        for arg in args {
            out.push(self.compile_expr(arg)?);
        }
        Ok(out)
    }
}

/// Recursively check whether a JSON value tree contains any template
/// expression strings (e.g. `"[parameters('x')]"`).
///
/// Returns `false` (conservatively safe) if nesting exceeds [`MAX_JSON_DEPTH`].
fn contains_template_expr(value: &JsonValue) -> bool {
    contains_template_expr_inner(value, 0)
}

fn contains_template_expr_inner(value: &JsonValue, depth: usize) -> bool {
    if depth > MAX_JSON_DEPTH {
        return false;
    }

    use crate::languages::azure_policy::parser::is_template_expr;

    match value {
        JsonValue::Str(_, s) => is_template_expr(s),
        JsonValue::Array(_, items) => items
            .iter()
            .any(|item| contains_template_expr_inner(item, depth.saturating_add(1))),
        JsonValue::Object(_, entries) => entries
            .iter()
            .any(|e| contains_template_expr_inner(&e.value, depth.saturating_add(1))),
        _ => false,
    }
}

/// Verify that a JSON value tree does not exceed the maximum nesting depth.
///
/// Called before handing a static value to [`json_value_to_runtime`] so that
/// its unbounded recursion cannot overflow the stack.  Also used by
/// `build_parameter_defaults` to guard parameter default values.
pub(super) fn check_json_depth(value: &JsonValue, current_depth: usize) -> Result<()> {
    if current_depth > MAX_JSON_DEPTH {
        bail!("JSON value nesting exceeds maximum depth of {MAX_JSON_DEPTH}");
    }
    match value {
        JsonValue::Array(_, items) => {
            for item in items {
                check_json_depth(item, current_depth.saturating_add(1))?;
            }
        }
        JsonValue::Object(_, entries) => {
            for entry in entries {
                check_json_depth(&entry.value, current_depth.saturating_add(1))?;
            }
        }
        _ => {}
    }
    Ok(())
}
