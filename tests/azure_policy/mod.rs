// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! YAML-driven test suite for Azure Policy parsing, compilation, and evaluation.
//!
//! Each YAML file in `tests/azure_policy/cases/` contains a list of test cases.
//! Each case specifies a policy rule JSON string plus the expected parse and
//! evaluation outcomes.
//!
//! The test runner validates:
//! - Successful parsing of policy rule JSON into the AST
//! - Expected parse failures for malformed inputs
//! - Compilation of the AST to RVM bytecode
//! - Evaluation of the compiled policy against the provided resource/parameters
//! - Expected `want_effect` / `want_undefined` results

mod normalization;
mod parser_tests;

use anyhow::{bail, Result};
use regorus::languages::azure_policy::aliases::normalizer;
use regorus::languages::azure_policy::aliases::AliasRegistry;
use regorus::languages::azure_policy::compiler;
use regorus::languages::azure_policy::parser;
use regorus::rvm::RegoVM;
use regorus::Source;
use regorus::Value;
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use test_generator::test_resources;

/// A single test case in the YAML file.
#[derive(Serialize, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct TestCase {
    /// Short identifier for the test case.
    pub note: String,

    /// The Azure Policy `policyRule` JSON string.
    #[serde(default)]
    pub policy_rule: Option<String>,

    /// The full Azure Policy definition JSON string (alternative to `policy_rule`).
    #[serde(default)]
    pub policy_definition: Option<String>,

    /// Resource properties supplied as the evaluation input document.
    #[serde(default)]
    pub resource: Option<serde_yaml::Value>,

    /// Policy parameters supplied to the policy evaluation.
    #[serde(default)]
    pub parameters: Option<serde_yaml::Value>,

    /// Expected effect produced by policy evaluation when the rule matches.
    #[serde(default)]
    pub want_effect: Option<String>,

    /// Expected details object in the structured effect result.
    /// When set, the test verifies `result.details == want_details`.
    #[serde(default)]
    pub want_details: Option<serde_yaml::Value>,

    /// If true, the compilation is expected to fail (e.g. modifiable check).
    #[serde(default)]
    pub want_compile_error: Option<bool>,

    /// If true, evaluation is expected to produce `Value::Undefined`
    /// (the condition does not match and the policy has no effect).
    #[serde(default)]
    pub want_undefined: Option<bool>,

    /// If true, the policy_rule is expected to fail parsing.
    #[serde(default)]
    pub want_parse_error: Option<bool>,

    /// Optional API version for the resource (e.g., "2023-01-01").
    /// When set, injected as `input.resource.apiversion` (lowercased to match
    /// the compiler's lowercased lookup paths) so policies and alias-versioned
    /// path selection can reference it.
    #[serde(default)]
    pub api_version: Option<String>,

    /// Optional request context object for the evaluation.
    /// When set, injected as `context.requestContext`.  Used by policies
    /// that reference `[requestContext().apiVersion]` or other request
    /// infrastructure fields.
    ///
    /// This is distinct from `api_version`, which specifies the resource's
    /// own API version for alias versioned path selection and
    /// `resource.apiVersion`.  When `request_context` is absent but
    /// `api_version` is present, `api_version` is used as a fallback
    /// for `context.requestContext.apiVersion` (backward compatibility).
    #[serde(default)]
    pub request_context: Option<serde_yaml::Value>,

    /// Optional custom context object. Overrides the default test context
    /// (resourceGroup, subscription). Useful for testing `resourceGroup()`,
    /// `subscription()`, and other context-dependent expressions.
    #[serde(default)]
    pub context: Option<serde_yaml::Value>,

    /// Host-await response entries for cross-resource effects
    /// (`auditIfNotExists` / `deployIfNotExists`).
    ///
    /// Each entry maps a request key (describing the lookup) to a response
    /// value.  These are injected into the VM as run-to-completion host
    /// await responses keyed by `"azure.policy.existence_check"`.
    ///
    /// The response should be the related resource object (for found
    /// resources) or `null` (when the resource does not exist).
    #[serde(default)]
    pub host_await: Vec<HostAwaitEntry>,

    /// If true, skip this test case.
    #[serde(default)]
    pub skip: Option<bool>,
}

/// A single host-await response entry.
///
/// ```yaml
/// host_await:
///   - key:
///       operation: "lookup_related_resources"
///       type: "Microsoft.Insights/diagnosticSettings"
///     response:
///       properties:
///         logs:
///           - enabled: true
/// ```
///
/// Use `response: null` when the related resource does not exist.
#[derive(Serialize, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct HostAwaitEntry {
    /// Descriptive key identifying the request (not used at runtime;
    /// serves as documentation in YAML tests).
    #[serde(default)]
    pub key: Option<serde_yaml::Value>,

    /// The fully-qualified ARM resource type of the related resource
    /// (e.g., `"Microsoft.Insights/diagnosticSettings"`).  When an alias
    /// catalog is loaded, the test harness uses this to normalize the
    /// response through the same alias-driven normalization that the
    /// primary resource receives.
    #[serde(default)]
    pub resource_type: Option<String>,

    /// The value the VM receives as the host-await response.
    pub response: serde_yaml::Value,
}

/// Top-level YAML test file structure.
#[derive(Serialize, Deserialize, Debug)]
#[serde(deny_unknown_fields)]
struct YamlTest {
    /// Optional path to an aliases JSON file (relative to
    /// `tests/azure_policy/aliases/`). When present, the alias catalog is
    /// loaded into an `AliasRegistry` and each test case's `resource` is
    /// treated as raw ARM JSON and run through the normalizer (root
    /// `properties` flattening + sub-resource array flattening) before
    /// evaluation.
    #[serde(default)]
    pub aliases: Option<String>,

    /// Optional global policy rule JSON string. Used as the default for test
    /// cases that don't specify their own `policy_rule` or `policy_definition`.
    /// Avoids duplicating the same policy across many test cases.
    #[serde(default)]
    pub policy_rule: Option<String>,

    /// Optional global policy definition JSON string (alternative to `policy_rule`).
    #[serde(default)]
    pub policy_definition: Option<String>,

    pub cases: Vec<TestCase>,
}

/// Filter test cases by the `TEST_CASE_FILTER` environment variable.
fn should_run_test_case(case_note: &str) -> bool {
    if let Ok(filter) = std::env::var("TEST_CASE_FILTER") {
        case_note.contains(&filter)
    } else {
        true
    }
}

/// Run all test cases from a YAML file.
fn yaml_test_impl(file: &str) -> Result<()> {
    let yaml_str = fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    // Load alias registry if an aliases file is specified.
    let alias_registry = if let Some(ref aliases_file) = test.aliases {
        let aliases_dir = Path::new(file)
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .join("../aliases")
            .join(aliases_file);
        let aliases_json = fs::read_to_string(&aliases_dir).map_err(|e| {
            anyhow::anyhow!(
                "Failed to load aliases file {}: {}",
                aliases_dir.display(),
                e
            )
        })?;
        let mut registry = AliasRegistry::new();
        registry.load_from_json(&aliases_json)?;
        Some(registry)
    } else {
        None
    };

    println!("running {file}");
    if let Some(ref reg) = alias_registry {
        println!("  Aliases loaded ({} resource types)", reg.len());
    }
    if let Ok(filter) = std::env::var("TEST_CASE_FILTER") {
        println!("  Test case filter active: '{filter}'");
    }

    let mut executed_count = 0usize;
    let mut skipped_count = 0usize;

    for case in &test.cases {
        if !should_run_test_case(&case.note) {
            println!("  case {} filtered out", case.note);
            skipped_count += 1;
            continue;
        }

        print!("  case {} ", case.note);

        if case.skip == Some(true) {
            println!("skipped");
            skipped_count += 1;
            continue;
        }

        executed_count += 1;

        let expects_parse_error = case.want_parse_error == Some(true);

        // Determine source and parse mode.
        // Case-level policy_definition/policy_rule takes precedence over
        // top-level (global) policy_definition/policy_rule.
        let (source_text, use_definition) = if let Some(ref defn) = case.policy_definition {
            (defn.clone(), true)
        } else if let Some(ref rule) = case.policy_rule {
            (rule.clone(), false)
        } else if let Some(ref defn) = test.policy_definition {
            (defn.clone(), true)
        } else if let Some(ref rule) = test.policy_rule {
            (rule.clone(), false)
        } else {
            bail!(
                "case '{}': must specify either 'policy_rule' or 'policy_definition'",
                case.note
            );
        };

        // Keep a reference for extracting parameter defaults later.
        let source = Source::from_contents(format!("test:{}", case.note), source_text)?;

        // Parse and compile.
        //
        // When the source is a full policy definition we parse to
        // `PolicyDefinition` and compile via `compile_policy_definition*`
        // which bakes parameter `defaultValue`s into the program's literal
        // table.  When it's just a policy rule we parse/compile directly.
        let compile_result: Result<_> = if use_definition {
            match parser::parse_policy_definition(&source) {
                Ok(defn) => {
                    if expects_parse_error {
                        bail!(
                            "case '{}': expected parse error but parsing succeeded",
                            case.note
                        );
                    }
                    if let Some(ref registry) = alias_registry {
                        compiler::compile_policy_definition_with_aliases(
                            &defn,
                            registry.alias_map(),
                            registry.alias_modifiable_map(),
                        )
                    } else {
                        compiler::compile_policy_definition(&defn)
                    }
                }
                Err(e) => {
                    if expects_parse_error {
                        println!("passed (expected parse error: {})", e);
                        continue;
                    }
                    bail!("case '{}': unexpected parse error: {}", case.note, e);
                }
            }
        } else {
            match parser::parse_policy_rule(&source) {
                Ok(ast) => {
                    if expects_parse_error {
                        bail!(
                            "case '{}': expected parse error but parsing succeeded",
                            case.note
                        );
                    }
                    if let Some(ref registry) = alias_registry {
                        compiler::compile_policy_rule_with_aliases(
                            &ast,
                            registry.alias_map(),
                            registry.alias_modifiable_map(),
                        )
                    } else {
                        compiler::compile_policy_rule(&ast)
                    }
                }
                Err(e) => {
                    if expects_parse_error {
                        println!("passed (expected parse error: {})", e);
                        continue;
                    }
                    bail!("case '{}': unexpected parse error: {}", case.note, e);
                }
            }
        };

        let expects_compile_error = case.want_compile_error == Some(true);

        let program = match compile_result {
            Ok(prog) => {
                if expects_compile_error {
                    bail!(
                        "case '{}': expected compile error but compilation succeeded",
                        case.note
                    );
                }
                prog
            }
            Err(e) => {
                if expects_compile_error {
                    println!("passed (expected compile error: {})", e);
                    continue;
                }
                bail!("case '{}': unexpected compile error: {}", case.note, e);
            }
        };

        // Extract the details.type from the policy for host_await
        // normalization (so test authors don't have to repeat it in YAML).
        let details_type = extract_details_resource_type(source.contents(), use_definition);

        // Debug: dump compiled program listing
        if std::env::var("DEBUG_LISTING").is_ok() {
            let listing = regorus::rvm::generate_assembly_listing(
                &program,
                &regorus::rvm::AssemblyListingConfig::default(),
            );
            eprintln!(
                "=== COMPILED LISTING ===\n{}\n========================",
                listing
            );
        }

        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_input(make_input(case, alias_registry.as_ref())?);
        vm.set_context(make_context(case)?);

        // Load host-await responses (for auditIfNotExists / deployIfNotExists policies).
        // When an alias catalog is loaded, the response is normalized through
        // the same alias-driven normalizer that the primary resource receives.
        // The resource type is injected into the response from the policy's
        // `details.type` (or overridden per-entry) so the normalizer can find
        // the right alias entries.
        if !case.host_await.is_empty() {
            let mut responses: BTreeMap<Value, Vec<Value>> = BTreeMap::new();
            for entry in &case.host_await {
                let response_value = if let Some(ref registry) = alias_registry {
                    // Determine the resource type: per-entry override > policy details.type.
                    let effective_type = entry.resource_type.as_deref().or(details_type.as_deref());
                    // Inject the type into object responses so the normalizer
                    // can look up alias entries (real ARM responses always
                    // include a "type" field). Non-object responses (e.g. null)
                    // pass through unchanged.
                    let mut raw = yaml_to_regorus_value(Some(&entry.response))?
                        .unwrap_or_else(Value::new_object);
                    if matches!(&raw, Value::Object(_)) {
                        if let Some(rt) = effective_type {
                            inject_type_field(&mut raw, rt);
                        }
                        normalizer::normalize(&raw, Some(registry), case.api_version.as_deref())
                    } else {
                        raw
                    }
                } else {
                    // No alias registry — lowercase all keys in the
                    // response to match the compiler's lowercased lookups.
                    let raw = yaml_to_regorus_value(Some(&entry.response))?
                        .unwrap_or_else(Value::new_object);
                    lowercase_value_keys(&raw)
                };

                responses
                    .entry(Value::from("azure.policy.existence_check"))
                    .or_default()
                    .push(response_value);
            }
            vm.set_host_await_responses(responses);
        }

        let value = vm.execute_entry_point_by_name("main")?;

        if case.want_undefined == Some(true) {
            assert_eq!(
                value,
                Value::Undefined,
                "case '{}': expected undefined, got {}",
                case.note,
                value
            );
            println!("passed (compiled + undefined)");
            continue;
        }

        if let Some(effect) = &case.want_effect {
            // The compiled result is now a structured object `{ "effect": "...", ... }`.
            // Extract the "effect" field for comparison.
            let effect_value = extract_effect_name(&value);
            let expected = Value::from(effect.clone());
            assert_eq!(
                effect_value, expected,
                "case '{}': expected effect {:?}, got {} (full result: {})",
                case.note, effect, effect_value, value
            );

            // Check details if expected.
            if let Some(ref want_details) = case.want_details {
                let actual_details = extract_details(&value);
                let expected_details =
                    yaml_to_regorus_value(Some(want_details))?.unwrap_or(Value::Undefined);
                assert_eq!(
                    actual_details, expected_details,
                    "case '{}': details mismatch.\n  actual:   {}\n  expected: {}",
                    case.note, actual_details, expected_details
                );
            }

            println!("passed (compiled + effect={})", effect);
        } else {
            println!("passed (compiled)");
        }
    }

    println!(
        "  Summary for {}: {} executed, {} skipped",
        file, executed_count, skipped_count
    );

    Ok(())
}

fn make_input(case: &TestCase, alias_registry: Option<&AliasRegistry>) -> Result<Value> {
    let parameters =
        yaml_to_regorus_value(case.parameters.as_ref())?.unwrap_or_else(Value::new_object);

    let mut resource = if alias_registry.is_some() {
        // When an alias registry is available, run the full normalizer:
        // root-field extraction, `properties` flattening, key lowercasing,
        // alias-specific path resolution.  This mirrors production behaviour
        // where the host normalizes inputs before evaluation.
        let raw = yaml_to_regorus_value(case.resource.as_ref())?.unwrap_or_else(Value::new_object);
        normalizer::normalize(&raw, alias_registry, case.api_version.as_deref())
    } else {
        // No alias registry — tests provide resources in ARM-like shape
        // (e.g. `properties.count` nested under `resource.properties`).
        // We lowercase all object keys so that built-in field lookups
        // (`fullName` → `fullname`, `apiVersion` → `apiversion`, tag names)
        // match the compiler's lowercased lookup paths.
        let raw = yaml_to_regorus_value(case.resource.as_ref())?.unwrap_or_else(Value::new_object);
        lowercase_value_keys(&raw)
    };

    // Inject api_version into the resource if specified.
    // Use lowercase key to match normalizer-lowercased keys and
    // the compiler's lowercased lookup paths.
    if let Some(ref api_ver) = case.api_version {
        let map = resource.as_object_mut()?;
        map.insert(Value::from("apiversion"), Value::from(api_ver.clone()));
    }

    // Inject `fullname` when the resource has a `name` but no explicit
    // `fullname`.  In Azure Policy, `field('fullName')` is a platform-
    // provided built-in that returns the complete ancestor-qualified name.
    // For test resources the YAML `name` already contains the full name
    // (ARM names include ancestor segments for child resources).
    {
        let map = resource.as_object_mut()?;
        if map.get(&Value::from("fullname")).is_none() {
            if let Some(name_val) = map.get(&Value::from("name")).cloned() {
                map.insert(Value::from("fullname"), name_val);
            }
        }
    }

    // Debug: print normalized resource for troubleshooting
    if std::env::var("DEBUG_RESOURCE").is_ok() {
        eprintln!("DEBUG normalized resource: {}", resource);
    }

    let mut input = Value::new_object();
    let map = input.as_object_mut()?;
    map.insert(Value::from("resource"), resource);
    map.insert(Value::from("parameters"), parameters);

    Ok(input)
}

fn make_context(case: &TestCase) -> Result<Value> {
    let mut ctx = if let Some(ref ctx) = case.context {
        yaml_to_regorus_value(Some(ctx))?.unwrap_or_else(Value::new_object)
    } else {
        Value::from_json_str(
            r#"{
                "resourceGroup": {
                    "name": "myResourceGroup",
                    "location": "eastus"
                },
                "subscription": {
                    "subscriptionId": "00000000-0000-0000-0000-000000000000"
                }
            }"#,
        )?
    };

    // Inject requestContext so that `[requestContext().apiVersion]` and other
    // request infrastructure expressions resolve correctly.
    //
    // Priority:
    //   1. Explicit `request_context` YAML field → injected as-is.
    //   2. Fallback: `api_version` → synthesizes `{ apiVersion: "<ver>" }`.
    //
    // In production the host provides the full requestContext; the test
    // harness mirrors the same contract.
    if let Some(ref rc) = case.request_context {
        let rc_val = yaml_to_regorus_value(Some(rc))?.unwrap_or_else(Value::new_object);
        let map = ctx.as_object_mut()?;
        // Only inject if the caller didn't already provide requestContext
        // in the context object, to avoid clobbering custom test setups.
        map.entry(Value::from("requestContext")).or_insert(rc_val);
    } else if let Some(ref api_ver) = case.api_version {
        let map = ctx.as_object_mut()?;
        if let std::collections::btree_map::Entry::Vacant(e) =
            map.entry(Value::from("requestContext"))
        {
            let mut req_ctx = Value::new_object();
            let rc_map = req_ctx.as_object_mut()?;
            rc_map.insert(Value::from("apiVersion"), Value::from(api_ver.clone()));
            e.insert(req_ctx);
        }
    }

    Ok(ctx)
}

fn yaml_to_regorus_value(value: Option<&serde_yaml::Value>) -> Result<Option<Value>> {
    let Some(value) = value else {
        return Ok(None);
    };

    let json = serde_json::to_string(value)?;
    let regorus_value = Value::from_json_str(&json)?;
    Ok(Some(regorus_value))
}

/// Recursively lowercase all object keys in a `Value`.
///
/// Used for tests without an alias registry so that built-in field lookups
/// (e.g. `fullName` → `fullname`, tag names) match the compiler's lowercased
/// lookup paths without running the full normalizer (which also flattens
/// `properties`).
fn lowercase_value_keys(value: &Value) -> Value {
    match value {
        Value::Object(btree) => {
            let mut result = Value::new_object();
            let map = result.as_object_mut().unwrap();
            for (k, v) in btree.iter() {
                let lc_key = match k {
                    Value::String(s) => Value::String(s.to_lowercase().into()),
                    other => other.clone(),
                };
                map.insert(lc_key, lowercase_value_keys(v));
            }
            result
        }
        Value::Array(arr) => {
            let items: Vec<Value> = arr.iter().map(lowercase_value_keys).collect();
            Value::from(items)
        }
        _ => value.clone(),
    }
}

/// Extract the effect name from a VM evaluation result.
///
/// If the value is an object containing `{ "effect": ... }`, returns that
/// field's value. If the value is a plain string (legacy format), returns it
/// directly.
fn extract_effect_name(value: &Value) -> Value {
    if let Ok(obj) = value.as_object() {
        if let Some(effect) = obj.get(&Value::from("effect")) {
            return effect.clone();
        }
    }
    // Legacy: plain string result
    value.clone()
}

/// Extract the details object from a structured result.
fn extract_details(value: &Value) -> Value {
    if let Ok(obj) = value.as_object() {
        if let Some(details) = obj.get(&Value::from("details")) {
            return details.clone();
        }
    }
    Value::Undefined
}

/// Extract the `details.type` resource type from a policy JSON string.
///
/// For AINE/DINE policies, `details.type` specifies the ARM resource type of
/// the related resource that the host must look up.  The test harness uses
/// this to inject the type into host_await responses so the normalizer can
/// find the right alias entries — no need for test authors to repeat the type
/// in each `host_await` entry.
///
/// Handles both full policy definitions (`properties.policyRule.then.details.type`)
/// and standalone policy rules (`then.details.type`).
fn extract_details_resource_type(source_text: &str, is_definition: bool) -> Option<String> {
    let json: serde_json::Value = serde_json::from_str(source_text).ok()?;
    let rule = if is_definition {
        // Try wrapped form first (`properties.policyRule`), fall back to
        // unwrapped (`policyRule` at top level).
        json.get("properties")
            .and_then(|p| p.get("policyRule"))
            .or_else(|| json.get("policyRule"))?
    } else {
        &json
    };
    rule.get("then")?
        .get("details")?
        .get("type")?
        .as_str()
        .map(String::from)
}

/// Inject a `type` field into a regorus Value object.
///
/// Used to add the resource type to host_await responses before normalization,
/// since the normalizer derives the resource type from the resource's `type`
/// field.  Real ARM responses always include `type`; the test YAML omits it
/// for brevity.
fn inject_type_field(value: &mut Value, resource_type: &str) {
    if let Ok(obj) = value.as_object_mut() {
        let key = Value::from("type");
        if obj.get(&key).is_none() {
            obj.insert(key, Value::from(resource_type));
        }
    }
}

#[test_resources("tests/azure_policy/cases/*.yaml")]
fn run_azure_policy_yaml(file: &str) {
    yaml_test_impl(file).unwrap();
}

#[test]
fn test_specific_case() {
    if std::env::var("TEST_CASE_FILTER").is_err() {
        println!("Specific case test skipped - no TEST_CASE_FILTER set");
        println!("  Usage: TEST_CASE_FILTER=\"note substring\" cargo test --features azure_policy test_specific_case -- --nocapture");
        return;
    }

    if let Ok(entries) = fs::read_dir("tests/azure_policy/cases") {
        let mut failures = Vec::new();
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("yaml") {
                if let Err(e) = yaml_test_impl(path.to_str().unwrap()) {
                    failures.push(format!("Error in file {}: {}", path.display(), e));
                }
            }
        }
        if !failures.is_empty() {
            panic!(
                "test_specific_case found {} failing file(s):\n{}",
                failures.len(),
                failures.join("\n")
            );
        }
    }
}
