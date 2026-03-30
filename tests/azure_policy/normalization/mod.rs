// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! YAML-driven normalization / denormalization tests.
//!
//! Each YAML file contains a `cases` array.  Every case specifies an `input`
//! JSON value plus optional `aliases` and `api_version`.  The runner then
//! checks whichever of the following fields are present:
//!
//! * `expected_normalized`  – result of normalizing `input`
//! * `expected_denormalized` – result of denormalizing `input`
//! * `round_trip` – normalize then denormalize; compare with `expected_round_trip`
//! * `reverse_round_trip` – denormalize then normalize; compare with
//!   `expected_reverse_round_trip`

use std::path::Path;

use anyhow::{bail, Result};
use serde::Deserialize;
use test_generator::test_resources;

use regorus::languages::azure_policy::aliases::normalizer;
use regorus::languages::azure_policy::aliases::types::ResolvedAliases;
use regorus::languages::azure_policy::aliases::{denormalizer, AliasRegistry};
use regorus::Value;

// ── YAML schema ──────────────────────────────────────────────────────────

#[derive(Deserialize)]
struct YamlTest {
    #[serde(default)]
    aliases_json: Option<String>,
    #[serde(default)]
    aliases_file: Option<String>,
    #[serde(default)]
    data_manifest_json: Option<String>,
    #[serde(default)]
    data_manifest_file: Option<String>,
    cases: Vec<TestCase>,
}

#[derive(Deserialize)]
struct TestCase {
    note: String,
    input: serde_json::Value,
    #[serde(default)]
    api_version: Option<String>,
    #[serde(default)]
    context: Option<serde_json::Value>,
    #[serde(default)]
    parameters: Option<serde_json::Value>,
    #[serde(default)]
    expected_normalized: Option<serde_json::Value>,
    #[serde(default)]
    expected_denormalized: Option<serde_json::Value>,
    #[serde(default)]
    expected_envelope: Option<serde_json::Value>,
    #[serde(default)]
    round_trip: bool,
    #[serde(default)]
    expected_round_trip: Option<serde_json::Value>,
    #[serde(default)]
    reverse_round_trip: bool,
    #[serde(default)]
    expected_reverse_round_trip: Option<serde_json::Value>,
    #[serde(default)]
    aliases_json: Option<String>,
    #[serde(default)]
    sub_resource_arrays: Option<Vec<String>>,
    #[serde(default)]
    resource_type: Option<String>,
    #[serde(default)]
    use_registry_api: bool,
}

// ── Helpers ──────────────────────────────────────────────────────────────

/// Convert a `serde_json::Value` to `regorus::Value`.
fn to_regorus(v: &serde_json::Value) -> Value {
    Value::from(v.clone())
}

fn load_registry(yaml_file: &str, test: &YamlTest) -> Result<Option<AliasRegistry>> {
    let mut reg = AliasRegistry::new();
    let mut loaded = false;

    if let Some(ref inline) = test.aliases_json {
        reg.load_from_json(inline)?;
        loaded = true;
    }
    if let Some(ref relpath) = test.aliases_file {
        let base = Path::new(yaml_file).parent().unwrap_or(Path::new("."));
        let path = base.join(relpath);
        let json = std::fs::read_to_string(&path)?;
        reg.load_from_json(&json)?;
        loaded = true;
    }
    if let Some(ref inline) = test.data_manifest_json {
        reg.load_data_policy_manifest_json(inline)?;
        loaded = true;
    }
    if let Some(ref relpath) = test.data_manifest_file {
        let base = Path::new(yaml_file).parent().unwrap_or(Path::new("."));
        let path = base.join(relpath);
        let json = std::fs::read_to_string(&path)?;
        reg.load_data_policy_manifest_json(&json)?;
        loaded = true;
    }

    Ok(if loaded { Some(reg) } else { None })
}

fn case_override_registry(case: &TestCase) -> Result<Option<AliasRegistry>> {
    if let Some(ref inline) = case.aliases_json {
        let mut reg = AliasRegistry::new();
        reg.load_from_json(inline)?;
        return Ok(Some(reg));
    }
    Ok(None)
}

fn resolve_aliases(
    registry: Option<&AliasRegistry>,
    case: &TestCase,
    input: &serde_json::Value,
) -> Option<ResolvedAliases> {
    let resource_type = case
        .resource_type
        .clone()
        .or_else(|| input.get("type").and_then(|v| v.as_str()).map(String::from));

    if let (Some(reg), Some(rt)) = (registry, resource_type.as_deref()) {
        if let Some(resolved) = reg.get(rt) {
            let mut r = resolved.clone();
            if let Some(ref subs) = case.sub_resource_arrays {
                r.sub_resource_arrays = subs.iter().map(|s| s.to_ascii_lowercase()).collect();
            }
            return Some(r);
        }
    }

    if let Some(ref subs) = case.sub_resource_arrays {
        return Some(ResolvedAliases {
            resource_type: resource_type.unwrap_or_default(),
            entries: Default::default(),
            sub_resource_arrays: subs.iter().map(|s| s.to_ascii_lowercase()).collect(),
            default_aggregates: Default::default(),
            versioned_aggregates: Default::default(),
        });
    }

    None
}

fn pretty_regorus(v: &Value) -> String {
    v.to_json_str().unwrap_or_else(|_| format!("{v:?}"))
}

// ── Runner ───────────────────────────────────────────────────────────────

fn run_yaml_test(file: &str) -> Result<()> {
    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;
    let file_registry = load_registry(file, &test)?;

    for case in &test.cases {
        print!("  case: {} … ", case.note);

        let case_override = case_override_registry(case)?;
        let registry = case_override.as_ref().or(file_registry.as_ref());
        let resolved = resolve_aliases(registry, case, &case.input);
        let api_ver = case.api_version.as_deref();
        let input = to_regorus(&case.input);

        // ── normalize ────────────────────────────────────────────────
        if let Some(ref expected) = case.expected_normalized {
            let expected = to_regorus(expected);
            let actual = if case.use_registry_api {
                normalizer::normalize(&input, registry, api_ver)
            } else {
                normalizer::normalize_with_aliases(&input, resolved.as_ref(), api_ver)
            };
            if actual != expected {
                bail!(
                    "normalize mismatch in '{}':\nexpected:\n{}\nactual:\n{}",
                    case.note,
                    pretty_regorus(&expected),
                    pretty_regorus(&actual),
                );
            }
        }

        // ── denormalize ──────────────────────────────────────────────
        if let Some(ref expected) = case.expected_denormalized {
            let expected = to_regorus(expected);
            let actual = if case.use_registry_api {
                denormalizer::denormalize(&input, registry, api_ver)
            } else {
                denormalizer::denormalize_with_aliases(&input, resolved.as_ref(), api_ver)
            };
            if actual != expected {
                bail!(
                    "denormalize mismatch in '{}':\nexpected:\n{}\nactual:\n{}",
                    case.note,
                    pretty_regorus(&expected),
                    pretty_regorus(&actual),
                );
            }
        }

        // ── envelope ─────────────────────────────────────────────────
        if let Some(ref expected) = case.expected_envelope {
            let expected = to_regorus(expected);
            let actual = if case.use_registry_api {
                if let Some(reg) = registry {
                    reg.normalize_and_wrap(
                        &input,
                        api_ver,
                        case.context.as_ref().map(to_regorus),
                        case.parameters.as_ref().map(to_regorus),
                    )
                } else {
                    let norm = normalizer::normalize(&input, None, api_ver);
                    normalizer::build_input_envelope(
                        norm,
                        case.context.as_ref().map(to_regorus),
                        case.parameters.as_ref().map(to_regorus),
                    )
                }
            } else {
                let norm = normalizer::normalize_with_aliases(&input, resolved.as_ref(), api_ver);
                normalizer::build_input_envelope(
                    norm,
                    case.context.as_ref().map(to_regorus),
                    case.parameters.as_ref().map(to_regorus),
                )
            };
            if actual != expected {
                bail!(
                    "envelope mismatch in '{}':\nexpected:\n{}\nactual:\n{}",
                    case.note,
                    pretty_regorus(&expected),
                    pretty_regorus(&actual),
                );
            }
        }

        // ── round-trip ───────────────────────────────────────────────
        if case.round_trip {
            let (normalized, denormalized) = if case.use_registry_api {
                let n = normalizer::normalize(&input, registry, api_ver);
                let d = denormalizer::denormalize(&n, registry, api_ver);
                (n, d)
            } else {
                let n = normalizer::normalize_with_aliases(&input, resolved.as_ref(), api_ver);
                let d = denormalizer::denormalize_with_aliases(&n, resolved.as_ref(), api_ver);
                (n, d)
            };
            let _ = normalized;
            if let Some(ref expected) = case.expected_round_trip {
                let expected = to_regorus(expected);
                if denormalized != expected {
                    bail!(
                        "round-trip mismatch in '{}':\nexpected:\n{}\nactual:\n{}",
                        case.note,
                        pretty_regorus(&expected),
                        pretty_regorus(&denormalized),
                    );
                }
            } else if denormalized != input {
                bail!(
                    "round-trip mismatch in '{}' (expected original input):\ninput:\n{}\nresult:\n{}",
                    case.note,
                    pretty_regorus(&input),
                    pretty_regorus(&denormalized),
                );
            }
        }

        // ── reverse round-trip ─────────────────────────────────────
        if case.reverse_round_trip {
            let (denormalized, renormalized) = if case.use_registry_api {
                let d = denormalizer::denormalize(&input, registry, api_ver);
                let n = normalizer::normalize(&d, registry, api_ver);
                (d, n)
            } else {
                let d = denormalizer::denormalize_with_aliases(&input, resolved.as_ref(), api_ver);
                let n = normalizer::normalize_with_aliases(&d, resolved.as_ref(), api_ver);
                (d, n)
            };
            let _ = denormalized;
            if let Some(ref expected) = case.expected_reverse_round_trip {
                let expected = to_regorus(expected);
                if renormalized != expected {
                    bail!(
                        "reverse round-trip mismatch in '{}':\nexpected:\n{}\nactual:\n{}",
                        case.note,
                        pretty_regorus(&expected),
                        pretty_regorus(&renormalized),
                    );
                }
            } else if renormalized != input {
                bail!(
                    "reverse round-trip mismatch in '{}' (expected original input):\ninput:\n{}\nresult:\n{}",
                    case.note,
                    pretty_regorus(&input),
                    pretty_regorus(&renormalized),
                );
            }
        }

        println!("ok");
    }

    println!("  {} cases passed in {file}", test.cases.len());
    Ok(())
}

#[test_resources("tests/azure_policy/normalization/cases/**/*.yaml")]
fn run(path: &str) {
    run_yaml_test(path).unwrap()
}
