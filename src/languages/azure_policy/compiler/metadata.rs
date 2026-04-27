// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Annotation accumulation and metadata population.
//!
//! During compilation the compiler records which policy features are used
//! (field kinds, aliases, operators, resource types, etc.).  After the
//! main compilation pass, [`populate_compiled_annotations`] writes these
//! observations into the program's metadata so the runtime can inspect
//! them without re-analysing the AST.

use alloc::collections::BTreeSet;
use alloc::string::{String, ToString as _};

use crate::languages::azure_policy::ast::{
    Condition, EffectKind, FieldKind, JsonValue, Lhs, OperatorKind, PolicyDefinition, PolicyRule,
    ValueOrExpr,
};
use crate::{Rc, Value};

use super::core::Compiler;

impl Compiler {
    // -- recording helpers --------------------------------------------------

    /// Record a built-in field kind reference (e.g. `"type"`, `"location"`).
    pub(super) fn record_field_kind(&mut self, name: &str) {
        self.observed_field_kinds.insert(name.to_string());
    }

    /// Record an alias path reference.  Also sets the wildcard flag when the
    /// alias contains `[*]`.
    pub(super) fn record_alias(&mut self, path: &str) {
        self.observed_aliases.insert(path.to_string());
        if path.contains("[*]") {
            self.observed_has_wildcard_aliases = true;
        }
    }

    /// Record a tag name reference (e.g. `"environment"` from `tags.environment`).
    pub(super) fn record_tag_name(&mut self, tag: &str) {
        self.observed_tag_names.insert(tag.to_string());
    }

    /// Record an operator usage, mapping the `OperatorKind` to its
    /// canonical JSON name (e.g. `Equals` → `"equals"`).
    pub(super) fn record_operator(&mut self, kind: &OperatorKind) {
        let name = match kind {
            OperatorKind::Equals => "equals",
            OperatorKind::NotEquals => "notEquals",
            OperatorKind::Greater => "greater",
            OperatorKind::GreaterOrEquals => "greaterOrEquals",
            OperatorKind::Less => "less",
            OperatorKind::LessOrEquals => "lessOrEquals",
            OperatorKind::In => "in",
            OperatorKind::NotIn => "notIn",
            OperatorKind::Contains => "contains",
            OperatorKind::NotContains => "notContains",
            OperatorKind::ContainsKey => "containsKey",
            OperatorKind::NotContainsKey => "notContainsKey",
            OperatorKind::Like => "like",
            OperatorKind::NotLike => "notLike",
            OperatorKind::Match => "match",
            OperatorKind::NotMatch => "notMatch",
            OperatorKind::MatchInsensitively => "matchInsensitively",
            OperatorKind::NotMatchInsensitively => "notMatchInsensitively",
            OperatorKind::Exists => "exists",
        };
        self.observed_operators.insert(name.to_string());
    }

    /// Extract resource type strings from `{ "field": "type", "equals"/"in": … }`
    /// conditions and record them for metadata.
    pub(super) fn record_resource_type_from_condition(&mut self, condition: &Condition) {
        let is_type_field =
            matches!(&condition.lhs, Lhs::Field(f) if matches!(f.kind, FieldKind::Type));
        if !is_type_field {
            return;
        }

        match &condition.operator.kind {
            // Positive operators — record types the policy applies to.
            OperatorKind::Equals => {
                if let ValueOrExpr::Value(JsonValue::Str(_, s)) = &condition.rhs {
                    self.observed_resource_types.insert(s.clone());
                }
            }
            OperatorKind::In => match &condition.rhs {
                ValueOrExpr::Value(JsonValue::Array(_, items)) => {
                    for item in items {
                        if let JsonValue::Str(_, s) = item {
                            self.observed_resource_types.insert(s.clone());
                        }
                    }
                }
                ValueOrExpr::Value(JsonValue::Str(_, s)) => {
                    self.observed_resource_types.insert(s.clone());
                }
                _ => {}
            },
            OperatorKind::Like => match &condition.rhs {
                ValueOrExpr::Value(JsonValue::Str(_, s)) => {
                    self.observed_resource_types.insert(s.clone());
                }
                ValueOrExpr::Value(JsonValue::Array(_, items)) => {
                    for item in items {
                        if let JsonValue::Str(_, s) = item {
                            self.observed_resource_types.insert(s.clone());
                        }
                    }
                }
                _ => {}
            },
            OperatorKind::Contains => {
                if let ValueOrExpr::Value(JsonValue::Str(_, s)) = &condition.rhs {
                    self.observed_resource_types.insert(s.clone());
                }
            }
            // Negative operators (NotEquals, NotIn, NotLike, NotContains) are
            // intentionally excluded — they indicate types the policy does NOT
            // apply to, which is not the same as applicability.
            _ => {}
        }
    }

    // -- effect annotation --------------------------------------------------

    /// Build the effect annotation string, resolving parameterized effects
    /// to their default values when possible.
    pub(super) fn resolve_effect_annotation(&self, rule: &PolicyRule) -> String {
        let effect = &rule.then_block.effect;
        match &effect.kind {
            EffectKind::Other => self
                .resolve_effect_name_from_parameter_default(effect)
                .unwrap_or_else(|| effect.raw.clone()),
            _ => effect.raw.clone(),
        }
    }

    // -- annotation population ----------------------------------------------

    /// Populate `program.metadata.annotations` from accumulated observations.
    ///
    /// Called once after the main compilation pass to write all recorded
    /// features into the program metadata.
    pub(super) fn populate_compiled_annotations(&mut self) {
        // Read has_host_await before borrowing annotations mutably.
        let has_host_await = self.program.has_host_await();
        let annot = &mut self.program.metadata.annotations;

        // Observed string sets → annotation sets.
        insert_string_set_annotation(annot, "field_kinds", &self.observed_field_kinds);
        insert_string_set_annotation(annot, "aliases", &self.observed_aliases);
        insert_string_set_annotation(annot, "tag_names", &self.observed_tag_names);
        insert_string_set_annotation(annot, "operators", &self.observed_operators);
        insert_string_set_annotation(annot, "resource_types", &self.observed_resource_types);

        // Boolean flags.
        if self.observed_uses_count {
            annot.insert("uses_count".to_string(), Value::Bool(true));
        }
        if self.observed_has_dynamic_fields {
            annot.insert("has_dynamic_fields".to_string(), Value::Bool(true));
        }
        if self.observed_has_wildcard_aliases {
            annot.insert("has_wildcard_aliases".to_string(), Value::Bool(true));
        }
        if has_host_await {
            annot.insert("has_host_await".to_string(), Value::Bool(true));
        }
    }

    /// Set definition-level metadata (display name, description, category,
    /// parameter names, etc.) from a `PolicyDefinition`.
    pub(super) fn populate_definition_metadata(&mut self, defn: &PolicyDefinition) {
        let annot = &mut self.program.metadata.annotations;

        // Top-level definition fields.
        if let Some(ref name) = defn.display_name {
            annot.insert(
                "display_name".to_string(),
                Value::String(name.as_str().into()),
            );
        }
        if let Some(ref desc) = defn.description {
            annot.insert(
                "description".to_string(),
                Value::String(desc.as_str().into()),
            );
        }
        if let Some(ref mode) = defn.mode {
            annot.insert("mode".to_string(), Value::String(mode.as_str().into()));
        }

        // Extract category, version, and preview from metadata JSON.
        if let Some(JsonValue::Object(_, entries)) = defn.metadata.as_ref() {
            for entry in entries {
                match entry.key.to_lowercase().as_str() {
                    "category" => {
                        if let JsonValue::Str(_, ref s) = entry.value {
                            annot.insert("category".to_string(), Value::String(s.as_str().into()));
                        }
                    }
                    "version" => {
                        if let JsonValue::Str(_, ref s) = entry.value {
                            annot.insert("version".to_string(), Value::String(s.as_str().into()));
                        }
                    }
                    "preview" => {
                        if let JsonValue::Bool(_, b) = entry.value {
                            annot.insert("preview".to_string(), Value::Bool(b));
                        }
                    }
                    "deprecated" => {
                        if let JsonValue::Bool(_, b) = entry.value {
                            annot.insert("deprecated".to_string(), Value::Bool(b));
                        }
                    }
                    "portalreview" => {
                        if let JsonValue::Str(_, ref s) = entry.value {
                            annot.insert(
                                "portal_review".to_string(),
                                Value::String(s.as_str().into()),
                            );
                        }
                    }
                    _ => {}
                }
            }
        }

        // Parameter names.
        if !defn.parameters.is_empty() {
            let set: BTreeSet<Value> = defn
                .parameters
                .iter()
                .map(|p| Value::String(p.name.as_str().into()))
                .collect();
            annot.insert("parameter_names".to_string(), Value::Set(Rc::new(set)));
        }

        // Extra fields: policyType → policy_type, id → policy_id, name → policy_name.
        for entry in &defn.extra {
            match entry.key.to_lowercase().as_str() {
                "policytype" => {
                    if let JsonValue::Str(_, ref s) = entry.value {
                        annot.insert("policy_type".to_string(), Value::String(s.as_str().into()));
                    }
                }
                "id" => {
                    if let JsonValue::Str(_, ref s) = entry.value {
                        annot.insert("policy_id".to_string(), Value::String(s.as_str().into()));
                    }
                }
                "name" => {
                    if let JsonValue::Str(_, ref s) = entry.value {
                        annot.insert("policy_name".to_string(), Value::String(s.as_str().into()));
                    }
                }
                _ => {}
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Module-private helpers
// ---------------------------------------------------------------------------

/// Insert a non-empty `BTreeSet<String>` as a `Value::Set` annotation.
fn insert_string_set_annotation(
    annot: &mut alloc::collections::BTreeMap<String, Value>,
    key: &str,
    observed: &BTreeSet<String>,
) {
    if !observed.is_empty() {
        let set: BTreeSet<Value> = observed
            .iter()
            .map(|s| Value::String(s.as_str().into()))
            .collect();
        annot.insert(key.to_string(), Value::Set(Rc::new(set)));
    }
}
