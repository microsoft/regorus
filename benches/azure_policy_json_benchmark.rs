// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Criterion benchmarks for Azure Policy JSON compilation and evaluation.
//!
//! These benchmarks measure the performance of the Azure Policy JSON pipeline
//! (parse → compile → normalize → VM execute) using the same KeyVault
//! soft-delete policy used by the PolicyTester .NET benchmark.
//!
//! # Running
//!
//! ```sh
//! cargo bench --bench azure_policy_json_benchmark --features azure_policy
//! ```

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use regorus::languages::azure_policy::aliases::normalizer;
use regorus::languages::azure_policy::aliases::AliasRegistry;
use regorus::languages::azure_policy::{compiler, parser};
use regorus::rvm::RegoVM;
use regorus::{Rc, Source, Value};

// ---------------------------------------------------------------------------
// Test data — KeyVault soft-delete policy (same as PolicyTester AuditDeny)
// ---------------------------------------------------------------------------

/// Full Azure Policy definition JSON for "Key vaults should have soft delete enabled".
/// This is the same policy used in the PolicyTester .NET benchmark (AuditDeny.json).
const KEYVAULT_POLICY_DEFINITION: &str = r#"{
  "properties": {
    "displayName": "Key vaults should have soft delete enabled",
    "policyType": "BuiltIn",
    "mode": "Indexed",
    "description": "Deleting a key vault without soft delete enabled permanently deletes all secrets, keys, and certificates stored in the key vault.",
    "metadata": {
      "version": "2.0.0",
      "category": "Key Vault"
    },
    "parameters": {
      "effect": {
        "type": "String",
        "metadata": {
          "displayName": "Effect",
          "description": "Enable or disable the execution of the policy"
        },
        "allowedValues": ["Audit", "Deny", "Disabled"],
        "defaultValue": "Deny"
      }
    },
    "policyRule": {
      "if": {
        "allOf": [
          {
            "field": "type",
            "equals": "Microsoft.KeyVault/vaults"
          },
          {
            "not": {
              "field": "Microsoft.KeyVault/vaults/createMode",
              "equals": "recover"
            }
          },
          {
            "anyOf": [
              {
                "field": "Microsoft.KeyVault/vaults/enableSoftDelete",
                "exists": "false"
              },
              {
                "field": "Microsoft.KeyVault/vaults/enableSoftDelete",
                "equals": "false"
              }
            ]
          }
        ]
      },
      "then": {
        "effect": "[parameters('effect')]"
      }
    }
  },
  "id": "/providers/Microsoft.Authorization/policyDefinitions/1e66c121-a66a-4b1f-9b83-0fd99bf0fc2d",
  "name": "1e66c121-a66a-4b1f-9b83-0fd99bf0fc2d"
}"#;

/// Load the full alias catalog from provider-cache.json — the same alias
/// metadata that the PolicyTester .NET benchmark uses. This ensures an
/// apples-to-apples comparison: identical policy, resource, AND alias set.
///
/// The file is located via the `PROVIDER_CACHE_JSON` environment variable,
/// falling back to `../../provider-cache.json` relative to the repo root.
fn load_aliases() -> AliasRegistry {
    let path = std::env::var("PROVIDER_CACHE_JSON").unwrap_or_else(|_| {
        let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
        // Default: assume provider-cache.json is two levels up (OnCall/)
        repo_root
            .parent()
            .map(|p| p.join("provider-cache.json"))
            .unwrap_or_else(|| repo_root.join("provider-cache.json"))
            .to_string_lossy()
            .into_owned()
    });
    let json =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
    let mut registry = AliasRegistry::new();
    registry
        .load_from_json(&json)
        .unwrap_or_else(|e| panic!("failed to parse aliases from {path}: {e}"));
    eprintln!(
        "Loaded {} resource-type entries from {path}",
        registry.len()
    );
    registry
}

/// Non-compliant resource: KeyVault without soft delete (enableSoftDelete missing).
/// This is the same resource from the PolicyTester AuditDeny.Test.yaml first test case.
const RESOURCE_NONCOMPLIANT: &str = r#"{
    "apiVersion": "2018-02-14",
    "name": "bswantestkv100",
    "location": "westus",
    "type": "Microsoft.KeyVault/vaults",
    "properties": {
        "sku": {
            "name": "Standard",
            "family": "A"
        }
    },
    "tags": {},
    "dependsOn": []
}"#;

/// Compliant resource: KeyVault with soft delete enabled.
const RESOURCE_COMPLIANT: &str = r#"{
    "apiVersion": "2018-02-14",
    "name": "bswantestkv100",
    "location": "westus",
    "type": "Microsoft.KeyVault/vaults",
    "properties": {
        "sku": {
            "name": "Standard",
            "family": "A"
        },
        "enableSoftDelete": true
    },
    "tags": {},
    "dependsOn": []
}"#;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Build the input envelope: `{"resource": <normalized>, "parameters": {...}}`.
fn make_input(resource_json: &str, registry: Option<&AliasRegistry>) -> Value {
    let resource_value =
        Value::from_json_str(resource_json).expect("failed to parse resource JSON");

    let normalized = normalizer::normalize(&resource_value, registry, None);

    // Add fullname from name if present.
    let mut normalized = normalized;
    if let Ok(map) = normalized.as_object_mut() {
        if map.get(&Value::from("fullname")).is_none() {
            if let Some(name_val) = map.get(&Value::from("name")).cloned() {
                map.insert(Value::from("fullname"), name_val);
            }
        }
    }

    let mut input = Value::new_object();
    let map = input.as_object_mut().unwrap();
    map.insert(Value::from("resource"), normalized);
    map.insert(Value::from("parameters"), Value::new_object());
    input
}

// ---------------------------------------------------------------------------
// Benchmark: compile policy definition (parse + compile)
// ---------------------------------------------------------------------------

fn bench_compile(c: &mut Criterion) {
    let mut registry = load_aliases();

    let source = Source::from_contents("keyvault_policy".into(), KEYVAULT_POLICY_DEFINITION.into())
        .expect("failed to create source");

    let defn = parser::parse_policy_definition(&source).expect("failed to parse policy definition");

    let mut group = c.benchmark_group("azure_policy_json/compile");

    group.bench_function("keyvault_softdelete_no_aliases", |b| {
        b.iter(|| {
            black_box(compiler::compile_policy_definition(black_box(&defn)).unwrap());
        })
    });

    group.bench_function("keyvault_softdelete_with_aliases", |b| {
        // Pre-build the alias maps once — in production these are built once
        // and reused across many compilations.
        let alias_map = registry.alias_map();
        let alias_modifiable = registry.alias_modifiable_map();
        b.iter(|| {
            black_box(
                compiler::compile_policy_definition_with_aliases(
                    black_box(&defn),
                    alias_map.clone(),
                    alias_modifiable.clone(),
                )
                .unwrap(),
            );
        })
    });

    // Also measure the alias map construction cost separately.
    group.bench_function("alias_map_construction", |b| {
        b.iter(|| {
            black_box(registry.alias_map());
            black_box(registry.alias_modifiable_map());
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Benchmark: hot eval (pre-compiled, set_input + execute per iteration)
// ---------------------------------------------------------------------------

fn bench_hot_eval(c: &mut Criterion) {
    let mut registry = load_aliases();

    let source = Source::from_contents("keyvault_policy".into(), KEYVAULT_POLICY_DEFINITION.into())
        .expect("failed to create source");
    let defn = parser::parse_policy_definition(&source).expect("failed to parse");

    let program = compiler::compile_policy_definition_with_aliases(
        &defn,
        registry.alias_map(),
        registry.alias_modifiable_map(),
    )
    .expect("failed to compile");

    let input_noncompliant = make_input(RESOURCE_NONCOMPLIANT, Some(&registry));
    let input_compliant = make_input(RESOURCE_COMPLIANT, Some(&registry));

    let mut group = c.benchmark_group("azure_policy_json/hot_eval");

    // Noncompliant resource (should produce deny effect).
    group.bench_function(
        BenchmarkId::new("keyvault_softdelete", "noncompliant"),
        |b| {
            let mut vm = RegoVM::new();
            vm.load_program(Rc::clone(&program));

            // Warm up.
            vm.set_input(input_noncompliant.clone());
            let _warmup = vm.execute_entry_point_by_name("main").unwrap();

            b.iter(|| {
                vm.set_input(black_box(input_noncompliant.clone()));
                black_box(vm.execute_entry_point_by_name("main").unwrap())
            })
        },
    );

    // Compliant resource (should produce undefined).
    group.bench_function(BenchmarkId::new("keyvault_softdelete", "compliant"), |b| {
        let mut vm = RegoVM::new();
        vm.load_program(Rc::clone(&program));

        vm.set_input(input_compliant.clone());
        let _warmup = vm.execute_entry_point_by_name("main").unwrap();

        b.iter(|| {
            vm.set_input(black_box(input_compliant.clone()));
            black_box(vm.execute_entry_point_by_name("main").unwrap())
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Benchmark: cold eval (new VM per iteration)
// ---------------------------------------------------------------------------

fn bench_cold_eval(c: &mut Criterion) {
    let mut registry = load_aliases();

    let source = Source::from_contents("keyvault_policy".into(), KEYVAULT_POLICY_DEFINITION.into())
        .expect("failed to create source");
    let defn = parser::parse_policy_definition(&source).expect("failed to parse");

    let program = compiler::compile_policy_definition_with_aliases(
        &defn,
        registry.alias_map(),
        registry.alias_modifiable_map(),
    )
    .expect("failed to compile");

    let input_noncompliant = make_input(RESOURCE_NONCOMPLIANT, Some(&registry));

    let mut group = c.benchmark_group("azure_policy_json/cold_eval");

    group.bench_function("keyvault_softdelete_noncompliant", |b| {
        b.iter(|| {
            let mut vm = RegoVM::new();
            vm.load_program(black_box(Rc::clone(&program)));
            vm.set_input(black_box(input_noncompliant.clone()));
            black_box(vm.execute_entry_point_by_name("main").unwrap())
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Benchmark: end-to-end (parse + compile + normalize + eval)
// ---------------------------------------------------------------------------

fn bench_end_to_end(c: &mut Criterion) {
    let mut registry = load_aliases();

    let alias_map = registry.alias_map();
    let alias_modifiable = registry.alias_modifiable_map();

    let mut group = c.benchmark_group("azure_policy_json/end_to_end");

    group.bench_function("keyvault_softdelete_noncompliant", |b| {
        b.iter(|| {
            let source =
                Source::from_contents("keyvault_policy".into(), KEYVAULT_POLICY_DEFINITION.into())
                    .expect("failed to create source");

            let defn =
                parser::parse_policy_definition(black_box(&source)).expect("failed to parse");

            let program = compiler::compile_policy_definition_with_aliases(
                black_box(&defn),
                alias_map.clone(),
                alias_modifiable.clone(),
            )
            .expect("failed to compile");

            let resource_value =
                Value::from_json_str(RESOURCE_NONCOMPLIANT).expect("failed to parse resource JSON");
            let normalized = normalizer::normalize(&resource_value, Some(&registry), None);

            let mut input = Value::new_object();
            let map = input.as_object_mut().unwrap();
            map.insert(Value::from("resource"), normalized);
            map.insert(Value::from("parameters"), Value::new_object());

            let mut vm = RegoVM::new();
            vm.load_program(program);
            vm.set_input(black_box(input));
            black_box(vm.execute_entry_point_by_name("main").unwrap())
        })
    });

    group.finish();
}

// ---------------------------------------------------------------------------
// Multi-policy benchmark: diverse real-world policies from the test suite
// ---------------------------------------------------------------------------

/// Minimal YAML test file structure — just enough to extract policy + first resource.
#[derive(serde::Deserialize)]
struct YamlTest {
    #[serde(default)]
    aliases: Option<String>,
    #[serde(default)]
    policy_definition: Option<String>,
    #[serde(default)]
    policy_rule: Option<String>,
    cases: Vec<YamlCase>,
}

#[derive(serde::Deserialize)]
#[allow(dead_code)]
struct YamlCase {
    note: String,
    #[serde(default)]
    resource: Option<serde_yaml::Value>,
    #[serde(default)]
    policy_definition: Option<String>,
    #[serde(default)]
    policy_rule: Option<String>,
    #[serde(default)]
    parameters: Option<serde_yaml::Value>,
    #[serde(default)]
    context: Option<serde_yaml::Value>,
    #[serde(default)]
    api_version: Option<String>,
    #[serde(default)]
    want_effect: Option<String>,
    #[serde(default)]
    want_undefined: Option<bool>,
    #[serde(default)]
    want_compile_error: Option<bool>,
    #[serde(default)]
    want_parse_error: Option<bool>,
    #[serde(default)]
    skip: Option<bool>,
    // Catch-all for fields we don't need.
    #[serde(flatten)]
    _extra: std::collections::HashMap<String, serde_yaml::Value>,
}

/// Convert a serde_yaml::Value to a regorus Value via JSON round-trip.
fn yaml_to_regorus_value(v: &serde_yaml::Value) -> Value {
    let json_str = serde_json::to_string(v).expect("yaml→json serialization failed");
    Value::from_json_str(&json_str).expect("json→regorus value failed")
}

/// A prepared policy for benchmarking.
struct PreparedPolicy {
    name: String,
    program: Rc<regorus::rvm::program::Program>,
    input: Value,
    context: Value,
}

/// Build `input.context` from a test case's context field + api_version.
fn build_context(case: &YamlCase) -> Value {
    let mut ctx = Value::new_object();
    let ctx_map = ctx.as_object_mut().unwrap();

    if let Some(ref context_yaml) = case.context {
        ctx = yaml_to_regorus_value(context_yaml);
    } else {
        // Default context with resourceGroup and subscription.
        let mut rg = Value::new_object();
        let rg_map = rg.as_object_mut().unwrap();
        rg_map.insert(Value::from("name"), Value::from("test-rg"));
        rg_map.insert(Value::from("location"), Value::from("westus"));
        ctx_map.insert(Value::from("resourcegroup"), rg);

        let mut sub = Value::new_object();
        let sub_map = sub.as_object_mut().unwrap();
        sub_map.insert(
            Value::from("subscriptionid"),
            Value::from("00000000-0000-0000-0000-000000000000"),
        );
        sub_map.insert(Value::from("displayname"), Value::from("test-sub"));
        ctx_map.insert(Value::from("subscription"), sub);
    }

    ctx
}

/// Build the input envelope and context from a YAML test case.
/// Returns (input, context) where input has {resource, parameters} and context is separate.
fn make_input_and_context_from_case(
    case: &YamlCase,
    registry: Option<&AliasRegistry>,
) -> (Value, Value) {
    let resource_yaml = case.resource.as_ref().expect("case has no resource");
    let resource_value = yaml_to_regorus_value(resource_yaml);

    let normalized = normalizer::normalize(&resource_value, registry, case.api_version.as_deref());

    let mut normalized = normalized;
    if let Ok(map) = normalized.as_object_mut() {
        if map.get(&Value::from("fullname")).is_none() {
            if let Some(name_val) = map.get(&Value::from("name")).cloned() {
                map.insert(Value::from("fullname"), name_val);
            }
        }
    }

    let mut input = Value::new_object();
    let map = input.as_object_mut().unwrap();
    map.insert(Value::from("resource"), normalized);

    // Parameters.
    if let Some(ref params_yaml) = case.parameters {
        map.insert(
            Value::from("parameters"),
            yaml_to_regorus_value(params_yaml),
        );
    } else {
        map.insert(Value::from("parameters"), Value::new_object());
    }

    let context = build_context(case);

    (input, context)
}

/// Policies to benchmark (path relative to tests/azure_policy/cases/).
const BENCHMARK_POLICIES: &[(&str, &str)] = &[
    ("e2e_nsg_rdp_access.yaml", "NSG RDP (count/wildcards)"),
    (
        "e2e_storage_vnet_rules.yaml",
        "Storage VNet (count/allOf/anyOf)",
    ),
    (
        "e2e_cmk_disk_encryption.yaml",
        "CMK Disk Encrypt (huge anyOf/like/in)",
    ),
    (
        "e2e_cosmos_max_throughput.yaml",
        "Cosmos MaxThroughput (greaterOrEquals)",
    ),
    (
        "e2e_storage_ip_allowlist.yaml",
        "Storage IP Allowlist (count.where/notIn)",
    ),
    (
        "e2e_tags_inherit_modify.yaml",
        "Tags Inherit (modify/resourceGroup)",
    ),
];

/// Load and prepare all benchmark policies.
fn prepare_policies(registry: &mut AliasRegistry) -> Vec<PreparedPolicy> {
    let cases_dir =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/azure_policy/cases");
    let aliases_dir = cases_dir.join("../aliases");

    let alias_map = registry.alias_map();
    let alias_modifiable = registry.alias_modifiable_map();

    let mut prepared = Vec::new();

    for (filename, label) in BENCHMARK_POLICIES {
        let path = cases_dir.join(filename);
        let yaml_str = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
        let test: YamlTest = serde_yaml::from_str(&yaml_str)
            .unwrap_or_else(|e| panic!("failed to parse {}: {e}", path.display()));

        // Load test-specific aliases if needed (for normalization).
        let test_registry = if let Some(ref aliases_file) = test.aliases {
            let aliases_path = aliases_dir.join(aliases_file);
            let aliases_json = std::fs::read_to_string(&aliases_path).unwrap_or_else(|e| {
                panic!("failed to read aliases {}: {e}", aliases_path.display())
            });
            let mut reg = AliasRegistry::new();
            reg.load_from_json(&aliases_json)
                .unwrap_or_else(|e| panic!("failed to parse aliases: {e}"));
            Some(reg)
        } else {
            None
        };

        // Find the first non-skipped case that expects an effect (not a parse/compile error).
        let case = test
            .cases
            .iter()
            .find(|c| {
                c.skip != Some(true)
                    && c.want_parse_error != Some(true)
                    && c.want_compile_error != Some(true)
                    && c.resource.is_some()
            })
            .unwrap_or_else(|| panic!("no benchmarkable case in {filename}"));

        // Get the policy source (case-level overrides top-level).
        let (source_text, use_definition) = if let Some(ref defn) = case.policy_definition {
            (defn.clone(), true)
        } else if let Some(ref rule) = case.policy_rule {
            (rule.clone(), false)
        } else if let Some(ref defn) = test.policy_definition {
            (defn.clone(), true)
        } else if let Some(ref rule) = test.policy_rule {
            (rule.clone(), false)
        } else {
            panic!("no policy in {filename}");
        };

        let source = Source::from_contents(filename.to_string(), source_text)
            .expect("failed to create source");

        // Compile with the full alias catalog.
        let program = if use_definition {
            let defn = parser::parse_policy_definition(&source)
                .unwrap_or_else(|e| panic!("parse failed for {filename}: {e}"));
            compiler::compile_policy_definition_with_aliases(
                &defn,
                Rc::clone(&alias_map),
                Rc::clone(&alias_modifiable),
            )
        } else {
            let ast = parser::parse_policy_rule(&source)
                .unwrap_or_else(|e| panic!("parse failed for {filename}: {e}"));
            compiler::compile_policy_rule_with_aliases(
                &ast,
                Rc::clone(&alias_map),
                Rc::clone(&alias_modifiable),
            )
        }
        .unwrap_or_else(|e| panic!("compile failed for {filename}: {e}"));

        // Build input and context from the first case.
        let (input, context) = make_input_and_context_from_case(case, test_registry.as_ref());

        // Sanity-check: run once to make sure it doesn't crash.
        let mut vm = RegoVM::new();
        vm.load_program(Rc::clone(&program));
        vm.set_input(input.clone());
        vm.set_context(context.clone());
        let result = vm
            .execute_entry_point_by_name("main")
            .unwrap_or_else(|e| panic!("eval failed for {filename}/{}: {e}", case.note));

        let effect_str = if result == Value::Undefined {
            "undefined".to_string()
        } else {
            result.to_json_str().unwrap_or_else(|_| "?".into())
        };
        eprintln!("  {label}: {filename}/{} → {effect_str}", case.note);

        prepared.push(PreparedPolicy {
            name: label.to_string(),
            program,
            input,
            context,
        });
    }

    prepared
}

fn bench_multi_policy_hot_eval(c: &mut Criterion) {
    let mut registry = load_aliases();
    let policies = prepare_policies(&mut registry);

    let mut group = c.benchmark_group("azure_policy_json/multi_policy_hot_eval");

    for policy in &policies {
        group.bench_function(&policy.name, |b| {
            let mut vm = RegoVM::new();
            vm.load_program(Rc::clone(&policy.program));
            vm.set_context(policy.context.clone());
            // Warm up.
            vm.set_input(policy.input.clone());
            let _ = vm.execute_entry_point_by_name("main").unwrap();

            b.iter(|| {
                vm.set_input(black_box(policy.input.clone()));
                black_box(vm.execute_entry_point_by_name("main").unwrap())
            })
        });
    }

    group.finish();
}

fn bench_multi_policy_cold_eval(c: &mut Criterion) {
    let mut registry = load_aliases();
    let policies = prepare_policies(&mut registry);

    let mut group = c.benchmark_group("azure_policy_json/multi_policy_cold_eval");

    for policy in &policies {
        group.bench_function(&policy.name, |b| {
            b.iter(|| {
                let mut vm = RegoVM::new();
                vm.load_program(black_box(Rc::clone(&policy.program)));
                vm.set_context(black_box(policy.context.clone()));
                vm.set_input(black_box(policy.input.clone()));
                black_box(vm.execute_entry_point_by_name("main").unwrap())
            })
        });
    }

    group.finish();
}

// ---------------------------------------------------------------------------
// Criterion harness
// ---------------------------------------------------------------------------

criterion_group!(
    benches,
    bench_compile,
    bench_hot_eval,
    bench_cold_eval,
    bench_end_to_end,
    bench_multi_policy_hot_eval,
    bench_multi_policy_cold_eval,
);
criterion_main!(benches);
