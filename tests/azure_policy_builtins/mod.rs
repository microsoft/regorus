// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! YAML-based test runner for Azure Policy builtins.
//!
//! Each YAML file contains a `builtin` field naming the function under test
//! and a list of `cases`.  Every case specifies `args` (positional arguments)
//! and either `want` (expected return value) or `want_undefined` (the builtin
//! should return `Value::Undefined`).
//!
//! Tests call builtins directly via the registry (`BUILTINS` map) instead of
//! going through Rego evaluation.  This avoids issues with builtin names that
//! collide with Rego keywords (e.g. `azure.policy.if`).

use anyhow::{bail, Result};
use regorus::unstable::{Source, Span, BUILTINS};
use regorus::Value;
use serde::Deserialize;
use test_generator::test_resources;

// ── YAML schema ───────────────────────────────────────────────────────

#[derive(Debug, Deserialize)]
struct YamlTestFile {
    /// Dotted builtin name, e.g. `azure.policy.fn.split`.
    builtin: String,
    cases: Vec<TestCase>,
}

#[derive(Debug, Deserialize)]
struct TestCase {
    /// Short human-readable label.
    note: String,
    /// Positional arguments fed to the builtin.
    args: Vec<serde_yaml::Value>,
    /// Expected return value (`null` for JSON null).
    want: Option<serde_yaml::Value>,
    /// If true, the builtin is expected to return null.
    /// (Needed because `want: null` in YAML deserializes as Option::None.)
    #[serde(default)]
    want_null: bool,
    /// If true, the builtin is expected to produce Undefined (no result).
    #[serde(default)]
    want_undefined: bool,
    /// If set, the builtin should return an error containing this substring.
    want_error: Option<String>,
    /// Skip this case.
    #[serde(default)]
    skip: bool,
}

// ── Helpers ───────────────────────────────────────────────────────────

/// Convert a serde_yaml::Value to a regorus Value.
fn yaml_to_value(v: &serde_yaml::Value) -> Value {
    match v {
        serde_yaml::Value::Null => Value::Null,
        serde_yaml::Value::Bool(b) => Value::Bool(*b),
        serde_yaml::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                Value::from(i)
            } else if let Some(f) = n.as_f64() {
                Value::from(f)
            } else {
                panic!("unsupported YAML numeric representation: {n:?}")
            }
        }
        serde_yaml::Value::String(s) => Value::String(s.as_str().into()),
        serde_yaml::Value::Sequence(items) => {
            let vals: Vec<Value> = items.iter().map(yaml_to_value).collect();
            Value::from(vals)
        }
        serde_yaml::Value::Mapping(map) => {
            let mut obj = Value::new_object();
            {
                let m = obj.as_object_mut().unwrap();
                for (k, v) in map {
                    m.insert(yaml_to_value(k), yaml_to_value(v));
                }
            }
            obj
        }
        serde_yaml::Value::Tagged(t) => yaml_to_value(&t.value),
    }
}

/// Create a dummy Span for calling builtins outside of normal evaluation.
fn dummy_span() -> Span {
    let source = Source::from_contents("<test>".to_string(), String::new())
        .expect("creating dummy source should not fail");
    Span {
        source,
        line: 1,
        col: 1,
        start: 0,
        end: 0,
    }
}

// ── Test runner ───────────────────────────────────────────────────────

fn run_yaml_test(path: &str) -> Result<()> {
    let content = std::fs::read_to_string(path)?;
    let test_file: YamlTestFile = serde_yaml::from_str(&content)?;

    let filter = std::env::var("TEST_CASE_FILTER").ok();

    // Look up the builtin function once for all cases.
    let builtin_entry = BUILTINS.get(test_file.builtin.as_str()).unwrap_or_else(|| {
        panic!(
            "builtin {:?} not found in BUILTINS registry",
            test_file.builtin
        )
    });

    let builtin_fn = builtin_entry.0;
    let span = dummy_span();

    for case in &test_file.cases {
        if case.skip {
            continue;
        }
        if let Some(ref f) = filter {
            if !case.note.contains(f.as_str()) {
                continue;
            }
        }

        // Convert YAML args to Value args.
        let args: Vec<Value> = case.args.iter().map(yaml_to_value).collect();

        // Call the builtin directly.
        let call_result = builtin_fn(&span, &[], &args, false);

        // Check error expectations.
        if let Some(ref want_err) = case.want_error {
            match call_result {
                Err(e) => {
                    let msg = format!("{e:#}");
                    assert!(
                        msg.contains(want_err.as_str()),
                        "[{builtin} / {note}] expected error containing {want_err:?}, got: {msg}",
                        builtin = test_file.builtin,
                        note = case.note,
                    );
                }
                Ok(ref v) if matches!(v, Value::Undefined) => {
                    // `want_error` specifically expects an error message string;
                    // Undefined is not acceptable here — bail.
                    bail!(
                        "[{builtin} / {note}] expected error containing {want_err:?} but got Undefined",
                        builtin = test_file.builtin,
                        note = case.note,
                    );
                }
                Ok(v) => {
                    bail!(
                        "[{builtin} / {note}] expected error containing {want_err:?} but got: {v}",
                        builtin = test_file.builtin,
                        note = case.note,
                    );
                }
            }
            continue;
        }

        // Not expecting an error — unwrap the result.
        let actual = call_result.map_err(|e| {
            anyhow::anyhow!(
                "[{builtin} / {note}] builtin returned error: {e:#}",
                builtin = test_file.builtin,
                note = case.note,
            )
        })?;

        if case.want_undefined {
            assert!(
                actual == Value::Undefined,
                "[{builtin} / {note}] expected Undefined but got: {actual}",
                builtin = test_file.builtin,
                note = case.note,
            );
            continue;
        }

        // We expect a concrete result.
        let expected = if case.want_null {
            Value::Null
        } else {
            let want = case.want.as_ref().unwrap_or_else(|| {
                panic!(
                    "[{} / {}] test case must have `want`, `want_null`, or `want_undefined`",
                    test_file.builtin, case.note
                )
            });
            yaml_to_value(want)
        };

        assert!(
            actual == expected,
            "[{builtin} / {note}]\n  expected: {expected}\n  actual:   {actual}",
            builtin = test_file.builtin,
            note = case.note,
        );
    }

    Ok(())
}

// ── Test entry point ──────────────────────────────────────────────────

#[test_resources("tests/azure_policy_builtins/cases/*.yaml")]
fn azure_policy_builtin_yaml(path: &str) {
    run_yaml_test(path).unwrap();
}
