use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use regorus::languages::azure_policy::aliases::{denormalizer, normalizer, AliasRegistry};
use regorus::Value;
use serde_json::json;

// ─── Alias catalog (reused across benchmarks) ───────────────────────────────

const ALIASES_JSON: &str = r#"[
  {
    "namespace": "Microsoft.Network",
    "resourceTypes": [
      {
        "resourceType": "networkSecurityGroups",
        "aliases": [
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].protocol",
            "defaultPath": "properties.securityRules[*].properties.protocol",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].access",
            "defaultPath": "properties.securityRules[*].properties.access",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].priority",
            "defaultPath": "properties.securityRules[*].properties.priority",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].direction",
            "defaultPath": "properties.securityRules[*].properties.direction",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].sourceAddressPrefix",
            "defaultPath": "properties.securityRules[*].properties.sourceAddressPrefix",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].destinationPortRange",
            "defaultPath": "properties.securityRules[*].properties.destinationPortRange",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].name",
            "defaultPath": "properties.securityRules[*].name",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/defaultSecurityRules[*].protocol",
            "defaultPath": "properties.defaultSecurityRules[*].properties.protocol",
            "paths": []
          }
        ]
      }
    ]
  },
  {
    "namespace": "Microsoft.Storage",
    "resourceTypes": [
      {
        "resourceType": "storageAccounts",
        "aliases": [
          {
            "name": "Microsoft.Storage/storageAccounts/supportsHttpsTrafficOnly",
            "defaultPath": "properties.supportsHttpsTrafficOnly",
            "paths": []
          },
          {
            "name": "Microsoft.Storage/storageAccounts/accessTier",
            "defaultPath": "properties.accessTier",
            "paths": []
          },
          {
            "name": "Microsoft.Storage/storageAccounts/isHnsEnabled",
            "defaultPath": "properties.isHnsEnabled",
            "paths": []
          },
          {
            "name": "Microsoft.Storage/storageAccounts/minimumTlsVersion",
            "defaultPath": "properties.minimumTlsVersion",
            "paths": []
          },
          {
            "name": "Microsoft.Storage/storageAccounts/allowBlobPublicAccess",
            "defaultPath": "properties.allowBlobPublicAccess",
            "paths": []
          },
          {
            "name": "Microsoft.Storage/storageAccounts/sku.name",
            "defaultPath": "sku.name",
            "paths": []
          }
        ]
      }
    ]
  }
]"#;

fn build_registry() -> AliasRegistry {
    let mut reg = AliasRegistry::new();
    reg.load_from_json(ALIASES_JSON).unwrap();
    reg
}

/// Convert a serde_json::Value to regorus::Value.
fn to_regorus(v: serde_json::Value) -> Value {
    Value::from(v)
}

// ─── Input resources ────────────────────────────────────────────────────────

fn simple_storage_resource() -> Value {
    to_regorus(json!({
        "name": "myStorageAccount",
        "type": "Microsoft.Storage/storageAccounts",
        "location": "westus2",
        "kind": "StorageV2",
        "sku": { "name": "Standard_LRS", "tier": "Standard" },
        "tags": { "environment": "production", "team": "platform" },
        "properties": {
            "supportsHttpsTrafficOnly": true,
            "accessTier": "Hot",
            "isHnsEnabled": false,
            "minimumTlsVersion": "TLS1_2",
            "allowBlobPublicAccess": false
        }
    }))
}

fn nsg_resource(rule_count: usize) -> Value {
    let rules: Vec<serde_json::Value> = (0..rule_count)
        .map(|i| {
            json!({
                "name": format!("rule-{}", i),
                "properties": {
                    "protocol": "Tcp",
                    "access": if i % 2 == 0 { "Allow" } else { "Deny" },
                    "priority": 100 + i,
                    "direction": "Inbound",
                    "sourceAddressPrefix": format!("10.0.{}.0/24", i % 256),
                    "destinationPortRange": format!("{}", 80 + i)
                }
            })
        })
        .collect();

    to_regorus(json!({
        "name": "myNsg",
        "type": "Microsoft.Network/networkSecurityGroups",
        "location": "eastus",
        "properties": {
            "securityRules": rules
        }
    }))
}

// ─── Benchmarks ─────────────────────────────────────────────────────────────

fn bench_normalize_simple(c: &mut Criterion) {
    let registry = build_registry();
    let resource = simple_storage_resource();

    c.bench_function("normalize/simple_storage", |b| {
        b.iter(|| normalizer::normalize(black_box(&resource), Some(&registry), None))
    });
}

fn bench_normalize_no_aliases(c: &mut Criterion) {
    let resource = simple_storage_resource();

    c.bench_function("normalize/simple_no_aliases", |b| {
        b.iter(|| normalizer::normalize(black_box(&resource), None, None))
    });
}

fn bench_normalize_nsg_scaling(c: &mut Criterion) {
    let registry = build_registry();
    let mut group = c.benchmark_group("normalize/nsg_rules");

    for rule_count in [5, 20, 100] {
        let resource = nsg_resource(rule_count);
        group.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &resource,
            |b, res| b.iter(|| normalizer::normalize(black_box(res), Some(&registry), None)),
        );
    }
    group.finish();
}

fn bench_denormalize_simple(c: &mut Criterion) {
    let registry = build_registry();
    let resource = simple_storage_resource();
    let normalized = normalizer::normalize(&resource, Some(&registry), None);

    c.bench_function("denormalize/simple_storage", |b| {
        b.iter(|| denormalizer::denormalize(black_box(&normalized), Some(&registry), None))
    });
}

fn bench_denormalize_nsg_scaling(c: &mut Criterion) {
    let registry = build_registry();
    let mut group = c.benchmark_group("denormalize/nsg_rules");

    for rule_count in [5, 20, 100] {
        let resource = nsg_resource(rule_count);
        let normalized = normalizer::normalize(&resource, Some(&registry), None);
        group.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &normalized,
            |b, norm| b.iter(|| denormalizer::denormalize(black_box(norm), Some(&registry), None)),
        );
    }
    group.finish();
}

fn bench_round_trip(c: &mut Criterion) {
    let registry = build_registry();
    let resource = nsg_resource(20);

    c.bench_function("round_trip/nsg_20_rules", |b| {
        b.iter(|| {
            let n = normalizer::normalize(black_box(&resource), Some(&registry), None);
            denormalizer::denormalize(&n, Some(&registry), None)
        })
    });
}

fn bench_normalize_and_wrap(c: &mut Criterion) {
    let registry = build_registry();
    let resource = nsg_resource(20);
    let context = to_regorus(json!({"resourceGroup": {"name": "rg1"}}));
    let parameters = to_regorus(json!({"env": "prod"}));

    c.bench_function("normalize_and_wrap/nsg_20_rules", |b| {
        b.iter(|| {
            registry.normalize_and_wrap(
                black_box(&resource),
                None,
                Some(context.clone()),
                Some(parameters.clone()),
            )
        })
    });
}

fn bench_registry_load(c: &mut Criterion) {
    c.bench_function("registry/load_from_json", |b| {
        b.iter(|| {
            let mut reg = AliasRegistry::new();
            reg.load_from_json(black_box(ALIASES_JSON)).unwrap();
            reg
        })
    });
}

// ─── Large-payload benchmarks ───────────────────────────────────────────────
//
// These stress the hot paths identified in the performance analysis:
// - Nested set helpers (alias-heavy catalog with deep properties)
// - Array element remap/cleanup/rewrap (large sub-resource arrays)
// - Scalar denormalization lookups (many aliases × many fields)

/// Build a large alias catalog with `n` scalar aliases for storage accounts.
/// Each alias maps to a nested `properties.section_i.field_j` path, creating
/// deep nested-set workloads.
fn large_alias_catalog(n: usize) -> String {
    let mut aliases = Vec::new();
    for i in 0..n {
        let section = i / 10;
        let field = i % 10;
        aliases.push(format!(
            r#"{{
                "name": "Microsoft.Storage/storageAccounts/section{section}Field{field}",
                "defaultPath": "properties.section{section}.field{field}",
                "paths": []
            }}"#,
        ));
    }
    format!(
        r#"[{{
            "namespace": "Microsoft.Storage",
            "resourceTypes": [{{
                "resourceType": "storageAccounts",
                "aliases": [{aliases}]
            }}]
        }}]"#,
        aliases = aliases.join(",")
    )
}

/// Build a storage account resource whose `properties` contain nested sections
/// matching the large alias catalog.
fn large_storage_resource(alias_count: usize) -> Value {
    let mut sections = serde_json::Map::new();
    for i in 0..alias_count {
        let section = i / 10;
        let field = i % 10;
        let section_key = format!("section{section}");
        let section_obj = sections
            .entry(section_key)
            .or_insert_with(|| serde_json::Value::Object(serde_json::Map::new()));
        if let serde_json::Value::Object(m) = section_obj {
            m.insert(format!("field{field}"), serde_json::Value::from(i));
        }
    }
    Value::from(json!({
        "name": "bigStorage",
        "type": "Microsoft.Storage/storageAccounts",
        "location": "westus2",
        "properties": sections
    }))
}

fn bench_normalize_large_catalog(c: &mut Criterion) {
    let mut group = c.benchmark_group("normalize/large_catalog");
    for alias_count in [50, 200] {
        let catalog_json = large_alias_catalog(alias_count);
        let mut reg = AliasRegistry::new();
        reg.load_from_json(&catalog_json).unwrap();
        let resource = large_storage_resource(alias_count);
        group.bench_with_input(
            BenchmarkId::from_parameter(alias_count),
            &(reg, resource),
            |b, (reg, res)| b.iter(|| normalizer::normalize(black_box(res), Some(reg), None)),
        );
    }
    group.finish();
}

fn bench_denormalize_large_catalog(c: &mut Criterion) {
    let mut group = c.benchmark_group("denormalize/large_catalog");
    for alias_count in [50, 200] {
        let catalog_json = large_alias_catalog(alias_count);
        let mut reg = AliasRegistry::new();
        reg.load_from_json(&catalog_json).unwrap();
        let resource = large_storage_resource(alias_count);
        let normalized = normalizer::normalize(&resource, Some(&reg), None);
        group.bench_with_input(
            BenchmarkId::from_parameter(alias_count),
            &(reg, normalized),
            |b, (reg, norm)| b.iter(|| denormalizer::denormalize(black_box(norm), Some(reg), None)),
        );
    }
    group.finish();
}

fn bench_nsg_large_subarrays(c: &mut Criterion) {
    let registry = build_registry();
    let mut group = c.benchmark_group("round_trip/nsg_sub_resource");
    for rule_count in [50, 200, 500] {
        let resource = nsg_resource(rule_count);
        group.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &resource,
            |b, res| {
                b.iter(|| {
                    let n = normalizer::normalize(black_box(res), Some(&registry), None);
                    denormalizer::denormalize(&n, Some(&registry), None)
                })
            },
        );
    }
    group.finish();
}

// ─── Versioned-path benchmarks ──────────────────────────────────────────────
//
// Exercise the precomputed versioned-path aggregates by building a catalog
// where wildcard (array) aliases have version-specific paths that differ from
// the default, then running normalize/denormalize with an explicit api_version.

/// NSG-like alias catalog where wildcard aliases have versioned paths that
/// differ from the default.  This forces the normalize/denormalize path through
/// the versioned aggregate lookup rather than the default-aggregate fast path.
const VERSIONED_ALIASES_JSON: &str = r#"[
  {
    "namespace": "Microsoft.Network",
    "resourceTypes": [
      {
        "resourceType": "networkSecurityGroups",
        "aliases": [
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].protocol",
            "defaultPath": "properties.securityRules[*].properties.protocol",
            "paths": [
              { "path": "properties.securityRules[*].properties.transportProtocol", "apiVersions": ["2020-01-01"] },
              { "path": "properties.securityRules[*].properties.protocol", "apiVersions": ["2022-01-01"] }
            ]
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].access",
            "defaultPath": "properties.securityRules[*].properties.access",
            "paths": [
              { "path": "properties.securityRules[*].properties.accessLevel", "apiVersions": ["2020-01-01"] },
              { "path": "properties.securityRules[*].properties.access", "apiVersions": ["2022-01-01"] }
            ]
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].priority",
            "defaultPath": "properties.securityRules[*].properties.priority",
            "paths": [
              { "path": "properties.securityRules[*].properties.rulePriority", "apiVersions": ["2020-01-01"] },
              { "path": "properties.securityRules[*].properties.priority", "apiVersions": ["2022-01-01"] }
            ]
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].direction",
            "defaultPath": "properties.securityRules[*].properties.direction",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].sourceAddressPrefix",
            "defaultPath": "properties.securityRules[*].properties.sourceAddressPrefix",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].destinationPortRange",
            "defaultPath": "properties.securityRules[*].properties.destinationPortRange",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/securityRules[*].name",
            "defaultPath": "properties.securityRules[*].name",
            "paths": []
          },
          {
            "name": "Microsoft.Network/networkSecurityGroups/provisioningState",
            "defaultPath": "properties.provisioningState",
            "paths": [
              { "path": "properties.state", "apiVersions": ["2020-01-01"] },
              { "path": "properties.provisioningState", "apiVersions": ["2022-01-01"] }
            ]
          }
        ]
      }
    ]
  }
]"#;

fn build_versioned_registry() -> AliasRegistry {
    let mut reg = AliasRegistry::new();
    reg.load_from_json(VERSIONED_ALIASES_JSON).unwrap();
    reg
}

/// Build an NSG resource for versioned-path benchmarks.
/// Uses the 2020-01-01 field names (`transportProtocol`, `accessLevel`,
/// `rulePriority`) so that versioned path resolution actually differs from
/// the default.
fn nsg_versioned_resource(rule_count: usize) -> Value {
    let rules: Vec<serde_json::Value> = (0..rule_count)
        .map(|i| {
            json!({
                "name": format!("rule-{}", i),
                "properties": {
                    "transportProtocol": "Tcp",
                    "accessLevel": if i % 2 == 0 { "Allow" } else { "Deny" },
                    "rulePriority": 100 + i,
                    "direction": "Inbound",
                    "sourceAddressPrefix": format!("10.0.{}.0/24", i % 256),
                    "destinationPortRange": format!("{}", 80 + i)
                }
            })
        })
        .collect();

    to_regorus(json!({
        "name": "myNsg",
        "type": "Microsoft.Network/networkSecurityGroups",
        "location": "eastus",
        "properties": {
            "state": "Succeeded",
            "securityRules": rules
        }
    }))
}

fn bench_normalize_versioned(c: &mut Criterion) {
    let registry = build_versioned_registry();
    let mut group = c.benchmark_group("normalize_versioned/nsg_rules");

    for rule_count in [5, 20, 100] {
        let resource = nsg_versioned_resource(rule_count);
        group.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &resource,
            |b, res| {
                b.iter(|| {
                    normalizer::normalize(black_box(res), Some(&registry), Some("2020-01-01"))
                })
            },
        );
    }
    group.finish();
}

fn bench_denormalize_versioned(c: &mut Criterion) {
    let registry = build_versioned_registry();
    let mut group = c.benchmark_group("denormalize_versioned/nsg_rules");

    for rule_count in [5, 20, 100] {
        let resource = nsg_versioned_resource(rule_count);
        let normalized = normalizer::normalize(&resource, Some(&registry), Some("2020-01-01"));
        group.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &normalized,
            |b, norm| {
                b.iter(|| {
                    denormalizer::denormalize(black_box(norm), Some(&registry), Some("2020-01-01"))
                })
            },
        );
    }
    group.finish();
}

fn bench_round_trip_versioned(c: &mut Criterion) {
    let registry = build_versioned_registry();
    let mut group = c.benchmark_group("round_trip_versioned/nsg_rules");

    for rule_count in [20, 100] {
        let resource = nsg_versioned_resource(rule_count);
        group.bench_with_input(
            BenchmarkId::from_parameter(rule_count),
            &resource,
            |b, res| {
                b.iter(|| {
                    let n =
                        normalizer::normalize(black_box(res), Some(&registry), Some("2020-01-01"));
                    denormalizer::denormalize(&n, Some(&registry), Some("2020-01-01"))
                })
            },
        );
    }
    group.finish();
}

criterion_group!(
    normalization_benches,
    bench_normalize_simple,
    bench_normalize_no_aliases,
    bench_normalize_nsg_scaling,
    bench_denormalize_simple,
    bench_denormalize_nsg_scaling,
    bench_round_trip,
    bench_normalize_and_wrap,
    bench_registry_load,
    bench_normalize_large_catalog,
    bench_denormalize_large_catalog,
    bench_nsg_large_subarrays,
    bench_normalize_versioned,
    bench_denormalize_versioned,
    bench_round_trip_versioned,
);
criterion_main!(normalization_benches);
