// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure Policy AST → RVM compiler.
//!
//! The compiler is split across several files:
//! - [`core`]: `Compiler` struct, main pipeline, register/emit helpers
//! - [`conditions`]: constraint / condition / LHS compilation
//! - [`conditions_wildcard`]: implicit allOf for unbound `[*]` fields
//! - [`count`]: `count` / `count.where` loops
//! - [`count_any`]: existence-pattern optimization (count → Any loop)
//! - [`count_bindings`]: count-binding resolution and `current()` references
//! - [`expressions`]: template-expression and call-expression compilation
//! - [`fields`]: field-kind and resource-path compilation
//! - [`template_dispatch`]: ARM template function dispatch
//! - [`effects`]: effect compilation (dispatch + cross-resource)
//! - [`effects_modify_append`]: Modify / Append detail compilation
//! - [`metadata`]: annotation accumulation and population
//! - [`utils`]: pure helper functions (path splitting, JSON conversion)

mod conditions;
mod conditions_wildcard;
mod core;
mod count;
mod count_any;
mod count_bindings;
mod effects;
mod effects_modify_append;
mod expressions;
mod fields;
mod metadata;
mod template_dispatch;
mod utils;

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString as _};

use anyhow::Result;

use crate::languages::azure_policy::ast::{PolicyDefinition, PolicyRule};
use crate::rvm::program::Program;
use crate::{Rc, Value};

use self::core::Compiler;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Initialise compiler language metadata and effect annotation.
fn init_effect_annotation(compiler: &mut Compiler, rule: &PolicyRule) {
    compiler.program.metadata.language = "azure_policy".to_string();
    let effect = compiler.resolve_effect_annotation(rule);
    compiler
        .program
        .metadata
        .annotations
        .insert("effect".to_string(), Value::String(effect.as_str().into()));
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// Compile a parsed Azure Policy rule into an RVM program.
pub fn compile_policy_rule(rule: &PolicyRule) -> Result<Rc<Program>> {
    let mut compiler = Compiler::new();
    init_effect_annotation(&mut compiler, rule);
    compiler.compile(rule)
}

/// Compile a parsed Azure Policy rule with alias resolution.
///
/// The `alias_map` maps lowercase fully-qualified alias names to their short
/// names.  Obtain it from
/// [`AliasRegistry::alias_map()`](crate::languages::azure_policy::aliases::AliasRegistry::alias_map).
pub fn compile_policy_rule_with_aliases(
    rule: &PolicyRule,
    alias_map: BTreeMap<String, String>,
    alias_modifiable: BTreeMap<String, bool>,
) -> Result<Rc<Program>> {
    let mut compiler = Compiler::new();
    compiler.alias_map = alias_map;
    compiler.alias_modifiable = alias_modifiable;
    init_effect_annotation(&mut compiler, rule);
    compiler.compile(rule)
}

/// Compile a parsed Azure Policy definition into an RVM program.
///
/// This extracts the `policyRule` from the definition and compiles it.
/// Parameter `defaultValue`s are collected so that later compiler passes
/// (effect compilation, metadata population) can reference them.
pub fn compile_policy_definition(defn: &PolicyDefinition) -> Result<Rc<Program>> {
    let mut compiler = Compiler::new();
    compiler.parameter_defaults = Some(build_parameter_defaults(&defn.parameters)?);
    compiler.populate_definition_metadata(defn);
    init_effect_annotation(&mut compiler, &defn.policy_rule);
    compiler.compile(&defn.policy_rule)
}

/// Compile a parsed Azure Policy definition with alias resolution.
pub fn compile_policy_definition_with_aliases(
    defn: &PolicyDefinition,
    alias_map: BTreeMap<String, String>,
    alias_modifiable: BTreeMap<String, bool>,
) -> Result<Rc<Program>> {
    let mut compiler = Compiler::new();
    compiler.alias_map = alias_map;
    compiler.alias_modifiable = alias_modifiable;
    compiler.parameter_defaults = Some(build_parameter_defaults(&defn.parameters)?);
    compiler.populate_definition_metadata(defn);
    init_effect_annotation(&mut compiler, &defn.policy_rule);
    compiler.compile(&defn.policy_rule)
}

/// Compile a parsed Azure Policy definition with alias resolution and
/// optional fallback behaviour for unknown aliases.
///
/// When `alias_fallback_to_raw` is `true`, field paths that do not resolve to
/// a known alias are silently treated as raw property paths.
pub fn compile_policy_definition_with_aliases_opts(
    defn: &PolicyDefinition,
    alias_map: BTreeMap<String, String>,
    alias_modifiable: BTreeMap<String, bool>,
    alias_fallback_to_raw: bool,
) -> Result<Rc<Program>> {
    let mut compiler = Compiler::new();
    compiler.alias_map = alias_map;
    compiler.alias_modifiable = alias_modifiable;
    compiler.alias_fallback_to_raw = alias_fallback_to_raw;
    compiler.parameter_defaults = Some(build_parameter_defaults(&defn.parameters)?);
    compiler.populate_definition_metadata(defn);
    init_effect_annotation(&mut compiler, &defn.policy_rule);
    compiler.compile(&defn.policy_rule)
}

/// Build a `Value::Object` of `{ param_name: defaultValue }` from
/// the parsed parameter definitions.
fn build_parameter_defaults(
    params: &[crate::languages::azure_policy::ast::ParameterDefinition],
) -> Result<Value> {
    use crate::languages::azure_policy::compiler::utils::json_value_to_runtime;
    let mut obj = Value::new_object();
    let map = obj.as_object_mut()?;
    for param in params {
        if let Some(ref default_val) = param.default_value {
            let runtime_val = json_value_to_runtime(default_val)?;
            map.insert(Value::from(param.name.clone()), runtime_val);
        }
    }
    Ok(obj)
}
