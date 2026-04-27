// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Effect compilation — dispatches the policy effect and compiles
//! cross-resource (AINE/DINE) evaluation.
//!
//! The effect is the "then" clause of a policy rule.  It may be a simple
//! literal (`"Deny"`) or a parameterized expression
//! (`[parameters('effect')]`).  Cross-resource effects involve a `HostAwait`
//! to fetch a related resource and an optional `existenceCondition` evaluated
//! inline.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::ToString as _;
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::languages::azure_policy::ast::{
    EffectKind, EffectNode, Expr, ExprLiteral, JsonValue, ObjectEntry, PolicyRule,
};
use crate::languages::azure_policy::compiler::utils::json_value_to_runtime;
use crate::rvm::instructions::ObjectCreateParams;
use crate::rvm::Instruction;
use crate::Value;

use super::core::Compiler;

impl Compiler {
    // -- main dispatch ------------------------------------------------------

    /// Compile the effect clause of a policy rule.
    ///
    /// Handles both literal effect kinds (`Deny`, `Audit`, …) and
    /// parameterised effects (`[parameters('effect')]`), routing to the
    /// appropriate compilation path.
    pub(super) fn compile_effect(&mut self, rule: &PolicyRule) -> Result<u8> {
        let effect = &rule.then_block.effect;
        let span = &effect.span;

        // --- Parameterized / unknown effect kind ---
        if matches!(effect.kind, EffectKind::Other) {
            return self.compile_parameterized_effect(rule);
        }

        // --- Well-known effect kinds ---
        match &effect.kind {
            EffectKind::AuditIfNotExists | EffectKind::DeployIfNotExists => {
                let effect_name_reg = self.load_literal(Value::from(effect.raw.clone()), span)?;
                self.compile_cross_resource_effect(rule, effect_name_reg)
            }
            EffectKind::Modify | EffectKind::Append => {
                let effect_name_reg = self.load_literal(Value::from(effect.raw.clone()), span)?;
                self.compile_effect_with_details(
                    &effect.kind,
                    effect_name_reg,
                    rule.then_block.details.as_ref(),
                    span,
                )
            }
            EffectKind::Disabled => {
                // Azure Policy: Disabled means skip evaluation entirely.
                self.emit_return_undefined(span)
            }
            EffectKind::Deny | EffectKind::Audit | EffectKind::DenyAction | EffectKind::Manual => {
                let name_reg = self.load_literal(Value::from(effect.raw.clone()), span)?;
                self.wrap_effect_result(name_reg, None, span)
            }
            // Unreachable — early return above handles Other — defensive fallback.
            EffectKind::Other => {
                bail!(span.error(&format!("unsupported effect kind: {}", effect.raw)))
            }
        }
    }

    /// Compile a parameterized effect (`EffectKind::Other`).
    ///
    /// Dispatches primarily based on the `then.details` structure and
    /// `then.existence_condition`:
    /// - Object with `type` key or `existence_condition` present → cross-resource (AINE/DINE)
    /// - Object with `operations` key → Modify
    /// - Array → Append
    ///
    /// Falls back to parameter-default resolution when details is absent.
    pub(super) fn compile_parameterized_effect(&mut self, rule: &PolicyRule) -> Result<u8> {
        let effect = &rule.then_block.effect;
        let span = &effect.span;

        // Primary dispatch: infer effect family from then.details structure.
        // This is correct for Azure Policy because the details shape determines
        // compilation semantics regardless of the runtime effect name.  Azure
        // definitions don't mix effect families in practice (e.g. Modify-shaped
        // details with an Audit effect).  The disabled guard on each structured
        // path handles the Disabled ↔ any-effect interchangeability.
        let structural = detect_effect_family_from_details(rule);

        match structural {
            EffectFamily::CrossResource => {
                let effect_name_reg = self.compile_effect_name_expression(effect)?;
                return self.compile_cross_resource_effect(rule, effect_name_reg);
            }
            EffectFamily::Modify => {
                let effect_name_reg = self.compile_bracket_or_literal_expression(effect)?;
                self.emit_disabled_guard(effect_name_reg, span)?;
                return self.compile_effect_with_details(
                    &EffectKind::Modify,
                    effect_name_reg,
                    rule.then_block.details.as_ref(),
                    span,
                );
            }
            EffectFamily::Append => {
                let effect_name_reg = self.compile_bracket_or_literal_expression(effect)?;
                self.emit_disabled_guard(effect_name_reg, span)?;
                return self.compile_effect_with_details(
                    &EffectKind::Append,
                    effect_name_reg,
                    rule.then_block.details.as_ref(),
                    span,
                );
            }
            EffectFamily::Unknown => {
                // Fall through to parameter-default resolution.
            }
        }

        // Secondary dispatch: resolve from parameter default when details
        // structure is absent or ambiguous.
        let resolved = self.resolve_effect_kind(effect);

        if resolved == EffectKind::AuditIfNotExists || resolved == EffectKind::DeployIfNotExists {
            let effect_name_reg = self.compile_effect_name_expression(effect)?;
            return self.compile_cross_resource_effect(rule, effect_name_reg);
        }

        if matches!(resolved, EffectKind::Modify | EffectKind::Append) {
            let effect_name_reg = self.compile_bracket_or_literal_expression(effect)?;
            self.emit_disabled_guard(effect_name_reg, span)?;
            return self.compile_effect_with_details(
                &resolved,
                effect_name_reg,
                rule.then_block.details.as_ref(),
                span,
            );
        }

        // Generic bracket expression — compile and wrap.
        if is_bracket_expression(&effect.raw) {
            let inner = effect
                .raw
                .strip_prefix('[')
                .and_then(|s| s.strip_suffix(']'))
                .ok_or_else(
                    || anyhow!(span.error("invalid effect expression: missing brackets")),
                )?;
            let expr =
                crate::languages::azure_policy::expr::ExprParser::parse_from_brackets(inner, span)
                    .map_err(|error| anyhow!("invalid effect expression: {}", error))?;
            let name_reg = self.compile_expr(&expr)?;
            self.emit_disabled_guard(name_reg, span)?;
            return self.wrap_effect_result(name_reg, None, span);
        }

        // Plain literal string — load and wrap.
        // Unescape ARM `[[` escape so the runtime value is correct.
        let name_reg = self.load_literal(Value::from(unescape_arm_literal(&effect.raw)), span)?;
        self.emit_disabled_guard(name_reg, span)?;
        self.wrap_effect_result(name_reg, None, span)
    }

    // -- result wrapping ----------------------------------------------------

    /// Wrap an effect name register into `{ "effect": <name> }` or
    /// `{ "effect": <name>, "details": <details> }`.
    pub(super) fn wrap_effect_result(
        &mut self,
        effect_name_reg: u8,
        details_reg: Option<u8>,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let mut keys: Vec<(u16, u8)> = Vec::new();
        let effect_key_idx = self.add_literal_u16(Value::from("effect"))?;
        keys.push((effect_key_idx, effect_name_reg));

        if let Some(det_reg) = details_reg {
            let details_key_idx = self.add_literal_u16(Value::from("details"))?;
            keys.push((details_key_idx, det_reg));
        }

        build_object_from_keys(self, keys, span)
    }

    /// Route to Modify or Append detail compilation, falling back to a bare
    /// effect result for other kinds.
    pub(super) fn compile_effect_with_details(
        &mut self,
        kind: &EffectKind,
        effect_name_reg: u8,
        details: Option<&JsonValue>,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        match kind {
            EffectKind::Modify => self.compile_modify_details(effect_name_reg, details, span),
            EffectKind::Append => self.compile_append_details(effect_name_reg, details, span),
            _ => self.wrap_effect_result(effect_name_reg, None, span),
        }
    }

    // -- effect name helpers ------------------------------------------------

    /// Compile the raw effect string into a runtime register.
    ///
    /// Bracket expressions like `[parameters('effect')]` are compiled so the
    /// value is resolved at runtime.  Plain strings are loaded as literals.
    pub(super) fn compile_effect_name_expression(&mut self, effect: &EffectNode) -> Result<u8> {
        let span = &effect.span;
        if is_bracket_expression(&effect.raw) {
            let inner = effect
                .raw
                .strip_prefix('[')
                .and_then(|s| s.strip_suffix(']'))
                .ok_or_else(
                    || anyhow!(span.error("invalid effect expression: missing brackets")),
                )?;
            let expr =
                crate::languages::azure_policy::expr::ExprParser::parse_from_brackets(inner, span)
                    .map_err(|error| anyhow!("invalid effect expression: {}", error))?;
            self.compile_expr(&expr)
        } else {
            self.load_literal(Value::from(unescape_arm_literal(&effect.raw)), span)
        }
    }

    /// Compile a bracket expression or fall back to a literal load.
    pub(super) fn compile_bracket_or_literal_expression(
        &mut self,
        effect: &EffectNode,
    ) -> Result<u8> {
        self.compile_effect_name_expression(effect)
    }

    // -- cross-resource effects (AINE / DINE) --------------------------------

    /// Compile a cross-resource effect (AuditIfNotExists / DeployIfNotExists).
    ///
    /// Two-phase evaluation:
    /// 1. `HostAwait` requests the related resource from the host.
    /// 2. The `existenceCondition` (if any) is evaluated against the returned
    ///    resource inline.  If absent, existence is checked via `PolicyExists`.
    ///
    /// Host protocol:
    ///   id  = `"azure.policy.existence_check"`
    ///   arg = `{ operation: "lookup_related_resources", type, name, … }`
    ///   response = related resource object, or `null` if not found
    pub(super) fn compile_cross_resource_effect(
        &mut self,
        rule: &PolicyRule,
        effect_name_reg: u8,
    ) -> Result<u8> {
        let span = &rule.then_block.effect.span;

        let Some(details) = rule.then_block.details.as_ref() else {
            bail!(span.error("cross-resource effects (AINE/DINE) require then.details"));
        };

        let JsonValue::Object(_, _) = details else {
            bail!(span
                .error("cross-resource effects (AINE/DINE) require then.details to be an object"));
        };

        // Guard: if the runtime effect is "Disabled", skip the existence
        // check entirely and return Undefined (Compliant).
        self.emit_disabled_guard(effect_name_reg, span)?;

        // Phase 1: Request related resource from host via HostAwait.
        let related_resource_reg = self.emit_host_await_lookup(details, span)?;

        // Phase 2: Evaluate existence.
        let exists_reg = self.evaluate_existence(rule, related_resource_reg, span)?;

        // Phase 3: Produce result.
        // If exists_reg is truthy → compliant → return Undefined.
        // If exists_reg is falsy  → non-compliant → return the effect object.
        let not_exists_reg = self.alloc_register()?;
        self.emit(
            Instruction::PolicyCondition {
                dest: not_exists_reg,
                left: exists_reg,
                right: 0,
                op: crate::rvm::instructions::PolicyOp::Not,
            },
            span,
        );
        self.emit(
            Instruction::ReturnUndefinedIfNotTrue {
                condition: not_exists_reg,
            },
            span,
        );

        // Build structured result with roleDefinitionIds / type if present.
        self.compile_cross_resource_details(effect_name_reg, details, span)
    }

    /// Unconditionally return Undefined from the compiled program.
    ///
    /// Used for `Disabled` effects — Azure Policy skips evaluation entirely.
    pub(super) fn emit_return_undefined(&mut self, span: &crate::lexer::Span) -> Result<u8> {
        let false_reg = self.load_literal(Value::Bool(false), span)?;
        self.emit(
            Instruction::ReturnUndefinedIfNotTrue {
                condition: false_reg,
            },
            span,
        );
        // The return register is never reached (the instruction above always
        // returns Undefined), but the caller requires a register.
        Ok(false_reg)
    }

    /// Emit instructions that return Undefined when the runtime effect name
    /// equals `"Disabled"` — used to short-circuit parameterized effect evaluation.
    pub(super) fn emit_disabled_guard(
        &mut self,
        effect_name_reg: u8,
        span: &crate::lexer::Span,
    ) -> Result<()> {
        let disabled_reg = self.load_literal(Value::from("Disabled"), span)?;
        let is_disabled_reg = self.alloc_register()?;
        self.emit(
            Instruction::PolicyCondition {
                dest: is_disabled_reg,
                left: effect_name_reg,
                right: disabled_reg,
                op: crate::rvm::instructions::PolicyOp::Equals,
            },
            span,
        );
        // Negate: not_disabled is false when disabled → ReturnUndefined fires.
        let not_disabled_reg = self.alloc_register()?;
        self.emit(
            Instruction::PolicyCondition {
                dest: not_disabled_reg,
                left: is_disabled_reg,
                right: 0,
                op: crate::rvm::instructions::PolicyOp::Not,
            },
            span,
        );
        self.emit(
            Instruction::ReturnUndefinedIfNotTrue {
                condition: not_disabled_reg,
            },
            span,
        );
        Ok(())
    }

    /// Emit a `HostAwait` instruction to request a related resource lookup.
    ///
    /// Detail fields like `type`, `name`, `resourceGroupName`, and
    /// `existenceScope` may contain template expressions (e.g.
    /// `"[field('name')]"`) that must be compiled rather than frozen as
    /// literals.
    pub(super) fn emit_host_await_lookup(
        &mut self,
        details: &JsonValue,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let request_reg = self.build_host_await_request(details, span)?;
        let id_reg = self.load_literal(Value::from("azure.policy.existence_check"), span)?;

        let related_resource_reg = self.alloc_register()?;
        self.emit(
            Instruction::HostAwait {
                dest: related_resource_reg,
                arg: request_reg,
                id: id_reg,
            },
            span,
        );
        Ok(related_resource_reg)
    }

    /// Evaluate whether the related resource satisfies the existence check.
    ///
    /// With an `existenceCondition`: checks resource exists AND condition
    /// passes (field references resolve against the related resource).
    /// Without: simply checks whether the resource was found (non-null).
    pub(super) fn evaluate_existence(
        &mut self,
        rule: &PolicyRule,
        related_resource_reg: u8,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        if let Some(ref existence_condition) = rule.then_block.existence_condition {
            // First check that the related resource was actually found.
            // Without this guard, field lookups on a null response yield
            // Undefined and operators like PolicyNotEquals(Undefined, _)
            // return true, incorrectly marking a missing resource as
            // compliant.
            let true_reg = self.load_literal(Value::Bool(true), span)?;
            let resource_found_reg = self.alloc_register()?;
            self.emit(
                Instruction::PolicyCondition {
                    dest: resource_found_reg,
                    left: related_resource_reg,
                    right: true_reg,
                    op: crate::rvm::instructions::PolicyOp::Exists,
                },
                span,
            );

            // Compile existenceCondition with field references resolving
            // against the related resource instead of input.resource.
            // Save/restore to ensure cleanup even if compile_constraint fails.
            let prev_override = self.resource_override_reg;
            self.resource_override_reg = Some(related_resource_reg);
            let cond_result = self.compile_constraint(existence_condition);
            self.resource_override_reg = prev_override;
            let cond_reg = cond_result?;

            // Combine: resource must exist AND condition must pass.
            let and_reg = self.alloc_register()?;
            self.emit(
                Instruction::And {
                    dest: and_reg,
                    left: resource_found_reg,
                    right: cond_reg,
                },
                span,
            );
            Ok(and_reg)
        } else {
            // No existenceCondition — just check resource existence.
            let true_reg = self.load_literal(Value::Bool(true), span)?;
            let dest = self.alloc_register()?;
            self.emit(
                Instruction::PolicyCondition {
                    dest,
                    left: related_resource_reg,
                    right: true_reg,
                    op: crate::rvm::instructions::PolicyOp::Exists,
                },
                span,
            );
            Ok(dest)
        }
    }

    /// Build cross-resource effect details for the returned result object.
    ///
    /// Only emits `roleDefinitionIds` and `type` into the structured result.
    /// All other fields (`existenceCondition`, `deployment`, `name`,
    /// `resourceGroupName`, etc.) are either evaluated inline during
    /// compilation or are ARM deployment metadata that the policy evaluation
    /// engine does not interpret.
    pub(super) fn compile_cross_resource_details(
        &mut self,
        effect_name_reg: u8,
        details: &JsonValue,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let JsonValue::Object(_, entries) = details else {
            return self.wrap_effect_result(effect_name_reg, None, span);
        };

        let mut detail_keys: Vec<(u16, u8)> = Vec::new();

        for ObjectEntry { key, value, .. } in entries {
            // Only emit `roleDefinitionIds` and `type` into the structured
            // result.  All other fields (existenceCondition, deployment,
            // name, resourceGroupName, etc.) are either evaluated inline
            // during compilation or are ARM deployment metadata that the
            // policy evaluation engine does not interpret.
            match key.to_lowercase().as_str() {
                "roledefinitionids" => {
                    let val = json_value_to_runtime(value)?;
                    let reg = self.load_literal(val, span)?;
                    let key_idx = self.add_literal_u16(Value::from("roleDefinitionIds"))?;
                    detail_keys.push((key_idx, reg));
                }
                "type" => {
                    let val = json_value_to_runtime(value)?;
                    let reg = self.load_literal(val, span)?;
                    let key_idx = self.add_literal_u16(Value::from("type"))?;
                    detail_keys.push((key_idx, reg));
                }
                _ => {}
            }
        }

        if detail_keys.is_empty() {
            return self.wrap_effect_result(effect_name_reg, None, span);
        }

        let details_dest = build_object_from_keys(self, detail_keys, span)?;
        self.wrap_effect_result(effect_name_reg, Some(details_dest), span)
    }

    // -- JSON value / expression helpers ------------------------------------

    /// Compile a JSON value that may contain template expressions.
    ///
    /// Delegates to [`compile_json_value`] which handles bracket strings,
    /// arrays with embedded template expressions, and plain literals.
    pub(super) fn compile_value_or_expr_from_json(
        &mut self,
        value: &JsonValue,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        self.compile_json_value(value, span)
    }

    // -- effect kind resolution ---------------------------------------------

    /// Resolve `EffectKind::Other` to a concrete kind using parameter defaults.
    pub(super) fn resolve_effect_kind(&self, effect: &EffectNode) -> EffectKind {
        match effect.kind {
            EffectKind::Other => self
                .resolve_effect_kind_from_parameter_default(effect)
                .unwrap_or_else(|| effect.kind.clone()),
            _ => effect.kind.clone(),
        }
    }

    /// Attempt to resolve an effect kind from `[parameters('name')]` by
    /// looking up the parameter's default value.
    pub(super) fn resolve_effect_kind_from_parameter_default(
        &self,
        effect: &EffectNode,
    ) -> Option<EffectKind> {
        let name = self.extract_parameter_default_string(effect)?;
        Self::effect_kind_from_string(&name)
    }

    /// Attempt to resolve an effect name string from `[parameters('name')]`
    /// by looking up the parameter's default value.
    pub(super) fn resolve_effect_name_from_parameter_default(
        &self,
        effect: &EffectNode,
    ) -> Option<alloc::string::String> {
        self.extract_parameter_default_string(effect)
    }

    /// Common helper: parse a `[parameters('name')]` expression, look up the
    /// parameter in `self.parameter_defaults`, and return the string value.
    pub(super) fn extract_parameter_default_string(
        &self,
        effect: &EffectNode,
    ) -> Option<alloc::string::String> {
        let raw = effect.raw.as_str();
        if !is_bracket_expression(raw) {
            return None;
        }

        let inner = raw.strip_prefix('[').and_then(|s| s.strip_suffix(']'))?;
        let expr = crate::languages::azure_policy::expr::ExprParser::parse_from_brackets(
            inner,
            &effect.span,
        )
        .ok()?;

        // Must be `parameters('paramName')` — a single-argument call.
        let parameter_name = match expr {
            Expr::Call { func, args, .. } if args.len() == 1 => {
                let first_arg = args.first()?;
                match (*func, first_arg) {
                    (
                        Expr::Ident { name, .. },
                        Expr::Literal {
                            value: ExprLiteral::String(param_name),
                            ..
                        },
                    ) if name.eq_ignore_ascii_case("parameters") => param_name.clone(),
                    _ => return None,
                }
            }
            _ => return None,
        };

        let defaults = self.parameter_defaults.as_ref()?;
        let defaults_obj = defaults.as_object().ok()?;
        let default_effect = defaults_obj.get(&Value::from(parameter_name))?;
        let effect_name = default_effect.as_string().ok()?;
        Some(effect_name.to_string())
    }

    /// Map a lowercase effect name string to its `EffectKind`.
    pub(super) fn effect_kind_from_string(effect_name: &str) -> Option<EffectKind> {
        let normalized = effect_name.to_lowercase();
        Some(match normalized.as_str() {
            "deny" => EffectKind::Deny,
            "audit" => EffectKind::Audit,
            "append" => EffectKind::Append,
            "auditifnotexists" => EffectKind::AuditIfNotExists,
            "deployifnotexists" => EffectKind::DeployIfNotExists,
            "disabled" => EffectKind::Disabled,
            "modify" => EffectKind::Modify,
            "denyaction" => EffectKind::DenyAction,
            "manual" => EffectKind::Manual,
            _ => return None,
        })
    }

    // -- host await request -------------------------------------------------

    /// Build the request object for `HostAwait` related-resource lookup.
    ///
    /// Produces `{ "operation": "lookup_related_resources", "type": …, … }`
    /// by extracting known keys from the effect's `details` block.
    ///
    /// Detail field values may contain template expressions (e.g.
    /// `"[concat(field('name'), '/default')]"`), so each value is compiled
    /// via [`compile_json_value`] rather than frozen as a static literal.
    pub(super) fn build_host_await_request(
        &mut self,
        details: &JsonValue,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let mut keys: Vec<(u16, u8)> = Vec::new();

        // "operation" is always the literal "lookup_related_resources".
        let op_reg = self.load_literal(Value::from("lookup_related_resources"), span)?;
        let op_key = self.add_literal_u16(Value::from("operation"))?;
        keys.push((op_key, op_reg));

        let JsonValue::Object(_, entries) = details else {
            return build_object_from_keys(self, keys, span);
        };

        // 'type' is required for cross-resource lookups and must be a string
        // (possibly a template expression like "[parameters('resourceType')]").
        let type_entry = entries
            .iter()
            .find(|entry| entry.key.eq_ignore_ascii_case("type"));
        match type_entry {
            None => {
                bail!(
                    span.error("cross-resource effects (AINE/DINE) require 'type' in then.details")
                );
            }
            Some(entry) => {
                if !matches!(&entry.value, JsonValue::Str(_, _)) {
                    bail!(entry.value.span().error(
                        "cross-resource effects require 'type' to be a string or expression"
                    ));
                }
            }
        }

        for key in [
            "type",
            "name",
            "kind",
            "resourceGroupName",
            "existenceScope",
        ] {
            if let Some(entry) = entries
                .iter()
                .find(|entry| entry.key.eq_ignore_ascii_case(key))
            {
                let val_reg = self.compile_json_value(&entry.value, entry.value.span())?;
                let key_idx = self.add_literal_u16(Value::from(key))?;
                keys.push((key_idx, val_reg));
            }
        }

        build_object_from_keys(self, keys, span)
    }

    // -- alias modifiability check ------------------------------------------

    /// Check whether a field path used in a Modify operation targets a
    /// modifiable alias.
    ///
    /// When the alias catalog is loaded, non-modifiable aliases produce a
    /// compile-time error.  Without an alias catalog, no check is performed.
    pub(super) fn check_modify_field_alias(
        &self,
        field_path: &str,
        span: &crate::lexer::Span,
    ) -> Result<()> {
        if self.alias_modifiable.is_empty() {
            return Ok(());
        }

        let lc = field_path.to_lowercase();

        if let Some(&modifiable) = self.alias_modifiable.get(&lc) {
            if !modifiable {
                bail!(span.error(&format!(
                    "alias '{}' is not modifiable (defaultMetadata.attributes != 'Modifiable')",
                    field_path
                )));
            }
        }

        // Tags and built-in fields are always modifiable for Modify operations.
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Module-private helpers
// ---------------------------------------------------------------------------

/// Structural effect family detected from `then.details` shape.
#[derive(Debug, PartialEq, Eq)]
enum EffectFamily {
    /// Details indicate a cross-resource effect (AINE/DINE):
    /// object with `type` key, or `existence_condition` present.
    CrossResource,
    /// Details indicate Modify: object with `operations` key.
    Modify,
    /// Details indicate Append: array of `{ field, value }` items.
    Append,
    /// No details or unrecognizable structure.
    Unknown,
}

/// Detect the effect family from the `then` block structure.
///
/// This enables correct compilation of parameterized effects even when the
/// parameter default is missing or misleading, by inspecting the structural
/// shape of `then.details` and `then.existence_condition`.
fn detect_effect_family_from_details(rule: &PolicyRule) -> EffectFamily {
    // existenceCondition is always cross-resource.
    if rule.then_block.existence_condition.is_some() {
        return EffectFamily::CrossResource;
    }

    let Some(details) = rule.then_block.details.as_ref() else {
        return EffectFamily::Unknown;
    };

    match details {
        JsonValue::Array(_, _) => EffectFamily::Append,
        JsonValue::Object(_, entries) => {
            let mut has_type = false;
            let mut has_operations = false;

            for entry in entries {
                match entry.key.to_lowercase().as_str() {
                    "type" => has_type = true,
                    "operations" => has_operations = true,
                    _ => {}
                }
            }

            if has_type && has_operations {
                // Ambiguous — both cross-resource and Modify markers.
                // Fall through to parameter-default resolution.
                EffectFamily::Unknown
            } else if has_type {
                EffectFamily::CrossResource
            } else if has_operations {
                EffectFamily::Modify
            } else {
                // Check for Append-shaped object: { "field": …, "value": … }
                let has_field = entries.iter().any(|e| e.key.to_lowercase() == "field");
                let has_value = entries.iter().any(|e| e.key.to_lowercase() == "value");
                if has_field && has_value {
                    EffectFamily::Append
                } else {
                    EffectFamily::Unknown
                }
            }
        }
        _ => EffectFamily::Unknown,
    }
}

/// Check whether a string is a bracket expression (`[…]` but not `[[…`).
fn is_bracket_expression(s: &str) -> bool {
    s.starts_with('[') && s.ends_with(']') && !s.starts_with("[[")
}

/// Unescape the ARM template double-bracket literal (`[[…` → `[…`).
///
/// In ARM templates, `[[` at the start of a string is an escape for a literal
/// `[`.  This mirrors the unescaping in `json_value_to_runtime` for JSON string
/// values, ensuring effect name literals are consistent.
fn unescape_arm_literal(s: &str) -> alloc::string::String {
    s.strip_prefix("[[")
        .map_or_else(|| s.into(), |rest| format!("[{rest}"))
}

/// Canonicalize known Azure Policy detail field names to their standard casing.
///
/// Case-insensitive matching produces the canonical form used by Azure;
/// unknown keys are passed through unchanged.
fn canonicalize_detail_key(key: &str) -> alloc::string::String {
    match key.to_lowercase().as_str() {
        "roledefinitionids" => "roleDefinitionIds".into(),
        "type" => "type".into(),
        "name" => "name".into(),
        "kind" => "kind".into(),
        "resourcegroupname" => "resourceGroupName".into(),
        "existencescope" => "existenceScope".into(),
        "deployment" => "deployment".into(),
        "deploymentscope" => "deploymentScope".into(),
        "evaluationdelay" => "evaluationDelay".into(),
        _ => key.into(),
    }
}

/// Build an RVM object from a set of `(literal_key_idx, value_reg)` pairs.
///
/// This is the common pattern used throughout effect compilation:
/// 1. Build a template `BTreeMap` with `Value::Undefined` placeholders.
/// 2. Sort keys by their literal value (BTreeMap order).
/// 3. Emit `ObjectCreate`.
#[allow(clippy::indexing_slicing)]
pub(super) fn build_object_from_keys(
    compiler: &mut Compiler,
    mut keys: Vec<(u16, u8)>,
    span: &crate::lexer::Span,
) -> Result<u8> {
    // Build template: object with all keys set to Undefined.
    let mut template = BTreeMap::new();
    for &(key_idx, _) in &keys {
        // SAFETY: key_idx was just returned by `add_literal_u16`, so the
        // index is guaranteed to be in bounds.
        let key_val = compiler.program.literals[usize::from(key_idx)].clone();
        template.insert(key_val, Value::Undefined);
    }
    let template_idx = compiler.add_literal_u16(Value::Object(crate::Rc::new(template)))?;

    // Sort keys by literal value (BTreeMap order).
    keys.sort_by(|a, b| {
        compiler.program.literals[usize::from(a.0)]
            .cmp(&compiler.program.literals[usize::from(b.0)])
    });

    let dest = compiler.alloc_register()?;
    let params = ObjectCreateParams {
        dest,
        template_literal_idx: template_idx,
        literal_key_fields: keys,
        fields: Vec::new(),
    };
    let params_index = compiler
        .program
        .instruction_data
        .add_object_create_params(params);
    compiler.emit(Instruction::ObjectCreate { params_index }, span);
    Ok(dest)
}
