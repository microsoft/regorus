// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Modify and Append effect detail compilation.
//!
//! Modify effects contain an array of operations (`add`, `addOrReplace`,
//! `remove`) each targeting a specific field/alias.  Append effects contain
//! a `{ "field", "value" }` pair or an array of such pairs.
//!
//! Values within operations may be template expressions (`[concat(…)]`)
//! which are compiled rather than stored as literals.

use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use anyhow::{bail, Result};

use crate::languages::azure_policy::compiler::utils::json_value_to_runtime;

use crate::languages::azure_policy::ast::{JsonValue, ObjectEntry};
use crate::rvm::instructions::ArrayCreateParams;
use crate::rvm::Instruction;

use super::core::Compiler;
use super::effects::build_object_from_keys;
use crate::Value;

impl Compiler {
    // -- Modify details -----------------------------------------------------

    /// Compile Modify effect details:
    /// `{ "effect": "modify", "details": { "roleDefinitionIds": […], "operations": […] } }`
    pub(super) fn compile_modify_details(
        &mut self,
        effect_name_reg: u8,
        details: Option<&JsonValue>,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        // When details is absent or not an object, return the bare effect.
        // Azure Policy still reports the effect even without structured
        // details — the details are instructions for the remediation engine.
        let Some(JsonValue::Object(_, entries)) = details else {
            return self.wrap_effect_result(effect_name_reg, None, span);
        };

        // Extract roleDefinitionIds and operations from details entries.
        let mut role_ids_value: Option<&JsonValue> = None;
        let mut operations: Option<&Vec<JsonValue>> = None;

        for ObjectEntry { key, value, .. } in entries {
            match key.to_lowercase().as_str() {
                "roledefinitionids" => role_ids_value = Some(value),
                "operations" => {
                    if let JsonValue::Array(_, ops) = value {
                        operations = Some(ops);
                    } else {
                        bail!(value
                            .span()
                            .error("Modify effect 'operations' must be an array"));
                    }
                }
                _ => {} // existenceCondition, conflictEffect, etc. — skip
            }
        }

        // roleDefinitionIds is required for Modify effects (must be an array
        // or a template expression that evaluates to one).
        let Some(role_json) = role_ids_value else {
            bail!(span.error("Modify effect requires 'roleDefinitionIds' in details"));
        };
        match role_json {
            JsonValue::Array(_, _) => {}
            JsonValue::Str(_, s) if crate::languages::azure_policy::parser::is_template_expr(s) => {
            }
            _ => bail!(role_json.span().error(
                "Modify effect 'roleDefinitionIds' must be an array or template expression",
            )),
        }

        let mut detail_keys: Vec<(u16, u8)> = Vec::new();

        // roleDefinitionIds — compile as expression (may be parameterized).
        {
            let role_reg = self.compile_json_value(role_json, role_json.span())?;
            let key_idx = self.add_literal_u16(Value::from("roleDefinitionIds"))?;
            detail_keys.push((key_idx, role_reg));
        }

        let Some(ops) = operations else {
            bail!(span.error("Modify effect requires 'operations' in details"));
        };
        if ops.is_empty() {
            bail!(span.error("Modify effect 'operations' must not be empty"));
        }

        // operations — compile each operation into an object.
        {
            let mut op_regs = Vec::new();
            for op_json in ops {
                let op_reg = self.compile_modify_operation(op_json, span)?;
                op_regs.push(op_reg);
            }

            let ops_dest = self.alloc_register()?;
            let ops_params = ArrayCreateParams {
                dest: ops_dest,
                elements: op_regs,
            };
            let ops_params_index = self
                .program
                .instruction_data
                .add_array_create_params(ops_params);
            self.emit(
                Instruction::ArrayCreate {
                    params_index: ops_params_index,
                },
                span,
            );

            let key_idx = self.add_literal_u16(Value::from("operations"))?;
            detail_keys.push((key_idx, ops_dest));
        }

        let details_dest = build_object_from_keys(self, detail_keys, span)?;
        self.wrap_effect_result(effect_name_reg, Some(details_dest), span)
    }

    /// Compile a single Modify operation into an object register.
    ///
    /// Expects `{ "operation": "…", "field": "…", "value": …, "condition": "…" }`.
    /// The `"value"` field may contain template expressions.
    pub(super) fn compile_modify_operation(
        &mut self,
        op_json: &JsonValue,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let JsonValue::Object(_, entries) = op_json else {
            bail!(op_json.span().error("modify operation must be an object"));
        };

        let mut op_keys: Vec<(u16, u8)> = Vec::new();
        let mut operation_name: Option<String> = None;
        let mut has_field = false;
        let mut has_value = false;

        for ObjectEntry { key, value, .. } in entries {
            match key.to_lowercase().as_str() {
                "operation" => {
                    let JsonValue::Str(_, op_str) = value else {
                        bail!(value
                            .span()
                            .error("modify operation 'operation' must be a string"));
                    };
                    let canonical_op = match op_str.to_lowercase().as_str() {
                        "add" => "add",
                        "addorreplace" => "addOrReplace",
                        "remove" => "remove",
                        other => bail!(value
                            .span()
                            .error(&format!("unsupported modify operation: {other}"))),
                    };
                    operation_name = Some(canonical_op.into());
                    let val = Value::from(canonical_op);
                    let reg = self.load_literal(val, value.span())?;
                    let key_idx = self.add_literal_u16(Value::from("operation"))?;
                    op_keys.push((key_idx, reg));
                }
                "field" => {
                    if let JsonValue::Str(_, field_path) = value {
                        self.check_modify_field_alias(field_path, value.span())?;
                        let val = Value::from(field_path.clone());
                        let reg = self.load_literal(val, value.span())?;
                        let key_idx = self.add_literal_u16(Value::from("field"))?;
                        op_keys.push((key_idx, reg));
                        has_field = true;
                    } else {
                        bail!(value
                            .span()
                            .error("modify operation 'field' must be a string"));
                    }
                }
                "value" => {
                    // Value may contain template expressions.
                    let reg = self.compile_value_or_expr_from_json(value, value.span())?;
                    let key_idx = self.add_literal_u16(Value::from("value"))?;
                    op_keys.push((key_idx, reg));
                    has_value = true;
                }
                "condition" => {
                    // The `condition` field is NOT evaluated during policy
                    // rule evaluation.  It is a remediation instruction:
                    // when Azure's remediation engine applies the modify
                    // effect it evaluates this condition against the
                    // resource to decide whether to execute the specific
                    // operation.  We preserve it verbatim (as a literal
                    // string) so the consumer receives the original
                    // expression, e.g. `"[equals(field('tags.env'), '')]"`.
                    let runtime_value = json_value_to_runtime(value)?;
                    let reg = self.load_literal(runtime_value, value.span())?;
                    let key_idx = self.add_literal_u16(Value::from("condition"))?;
                    op_keys.push((key_idx, reg));
                }
                _ => {} // Unknown fields — skip
            }
        }

        let Some(op_name) = operation_name else {
            bail!(op_json
                .span()
                .error("modify operation must include 'operation'"));
        };
        if !has_field {
            bail!(op_json
                .span()
                .error("modify operation must include 'field'"));
        }
        // 'add' and 'addOrReplace' require a value; 'remove' does not.
        if !has_value && op_name != "remove" {
            bail!(op_json.span().error(&format!(
                "modify operation '{op_name}' must include 'value'"
            )));
        }

        build_object_from_keys(self, op_keys, span)
    }

    // -- Append details -----------------------------------------------------

    /// Compile an Append effect's details.
    ///
    /// Accepts both array form `[ { "field": …, "value": … }, … ]` and
    /// single-object form `{ "field": …, "value": … }`.
    pub(super) fn compile_append_details(
        &mut self,
        effect_name_reg: u8,
        details: Option<&JsonValue>,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let Some(details) = details else {
            // When details is absent, return the bare effect.
            return self.wrap_effect_result(effect_name_reg, None, span);
        };

        let item_regs = match details {
            JsonValue::Array(_, arr) => {
                if arr.is_empty() {
                    bail!(span.error("Append effect requires non-empty 'details' array"));
                }
                let mut regs = Vec::new();
                for item in arr {
                    regs.push(self.compile_append_item(item, span)?);
                }
                regs
            }
            JsonValue::Object(_, _) => {
                vec![self.compile_append_item(details, span)?]
            }
            _ => {
                bail!(span.error("Append effect 'details' must be an array or object"));
            }
        };

        // Create the details array.
        let details_dest = self.alloc_register()?;
        let params = ArrayCreateParams {
            dest: details_dest,
            elements: item_regs,
        };
        let params_index = self
            .program
            .instruction_data
            .add_array_create_params(params);
        self.emit(Instruction::ArrayCreate { params_index }, span);

        self.wrap_effect_result(effect_name_reg, Some(details_dest), span)
    }

    /// Compile a single Append item `{ "field": "…", "value": … }` into an
    /// object register.
    pub(super) fn compile_append_item(
        &mut self,
        item_json: &JsonValue,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let JsonValue::Object(_, entries) = item_json else {
            bail!(item_json
                .span()
                .error("append details item must be an object"));
        };

        let mut field_reg: Option<u8> = None;
        let mut value_reg: Option<u8> = None;

        for ObjectEntry { key, value, .. } in entries {
            match key.to_lowercase().as_str() {
                "field" => {
                    let JsonValue::Str(_, field_path) = value else {
                        bail!(value
                            .span()
                            .error("append details item 'field' must be a string"));
                    };
                    let val = Value::from(field_path.clone());
                    field_reg = Some(self.load_literal(val, value.span())?);
                }
                "value" => {
                    value_reg = Some(self.compile_value_or_expr_from_json(value, value.span())?);
                }
                _ => {}
            }
        }

        let Some(field_reg) = field_reg else {
            bail!(item_json
                .span()
                .error("append details item must include 'field'"));
        };
        let Some(value_reg) = value_reg else {
            bail!(item_json
                .span()
                .error("append details item must include 'value'"));
        };

        let item_keys = vec![
            (self.add_literal_u16(Value::from("field"))?, field_reg),
            (self.add_literal_u16(Value::from("value"))?, value_reg),
        ];

        build_object_from_keys(self, item_keys, span)
    }
}
