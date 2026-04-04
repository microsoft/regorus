// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! YAML-driven test suite for Azure Policy constraint parser.
//!
//! Each YAML file in `tests/azure_policy/parser_tests/cases/` contains a list
//! of test cases. Each case specifies a `policy_rule` JSON string with
//! `"if"` / `"then"` structure. The test runner extracts the `"if"` constraint
//! JSON and parses it with `parse_constraint`.

use anyhow::Result;
use regorus::languages::azure_policy::parser;
use regorus::Source;
use serde::{Deserialize, Serialize};
use std::fs;
use test_generator::test_resources;

/// A single test case in the YAML file.
#[derive(Serialize, Deserialize, Debug)]
struct TestCase {
    /// Short identifier for the test case.
    pub note: String,

    /// The Azure Policy `policyRule` JSON string.
    #[serde(default)]
    pub policy_rule: Option<String>,

    /// If true, the constraint is expected to fail parsing.
    #[serde(default)]
    pub want_parse_error: Option<bool>,

    /// If true, skip this test case.
    #[serde(default)]
    pub skip: Option<bool>,

    /// Parsing level: `"constraint"` (default) extracts the `"if"` block and
    /// calls `parse_constraint`; `"policy_rule"` calls `parse_policy_rule` on
    /// the full JSON; `"policy_definition"` calls `parse_policy_definition`
    /// on the full JSON.
    #[serde(default)]
    pub parse_level: Option<String>,
}

/// Top-level YAML test file structure.
#[derive(Serialize, Deserialize, Debug)]
struct YamlTest {
    /// Optional global policy rule JSON string.
    #[serde(default)]
    pub policy_rule: Option<String>,

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

/// Extract the `"if"` sub-object from a policy rule JSON string.
///
/// Returns `None` if parsing fails or there is no `"if"` key (the caller
/// should feed the raw string to `parse_constraint` for error tests).
fn extract_if_json(policy_rule_json: &str) -> Option<String> {
    let v: serde_json::Value = serde_json::from_str(policy_rule_json).ok()?;
    let if_value = v.get("if")?;
    Some(if_value.to_string())
}

/// Run all test cases from a YAML file.
fn yaml_test_impl(file: &str) -> Result<()> {
    let yaml_str = fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    println!("running {file}");
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

        let input_json = if let Some(ref rule) = case.policy_rule {
            rule.clone()
        } else if let Some(ref rule) = test.policy_rule {
            rule.clone()
        } else {
            panic!("case '{}': must specify 'policy_rule'", case.note);
        };

        let parse_level = case.parse_level.as_deref().unwrap_or("constraint");

        let parse_result = match parse_level {
            "policy_rule" => {
                // Parse the full policy_rule JSON with parse_policy_rule.
                let source = Source::from_contents(format!("test:{}", case.note), input_json)?;
                parser::parse_policy_rule(&source).map(|_| ())
            }
            "policy_definition" => {
                // Parse the full policy definition JSON with parse_policy_definition.
                let source = Source::from_contents(format!("test:{}", case.note), input_json)?;
                parser::parse_policy_definition(&source).map(|_| ())
            }
            "constraint" => {
                // Extract the "if" constraint JSON. If extraction fails
                // (malformed JSON or missing "if" key), feed the raw
                // input to parse_constraint — it should fail,
                // matching want_parse_error.
                let constraint_json = match extract_if_json(&input_json) {
                    Some(json) => json,
                    None => input_json,
                };
                let source = Source::from_contents(format!("test:{}", case.note), constraint_json)?;
                parser::parse_constraint(&source).map(|_| ())
            }
            other => {
                panic!("case '{}': unknown parse_level '{}'", case.note, other);
            }
        };

        match parse_result {
            Ok(()) => {
                if expects_parse_error {
                    panic!(
                        "case '{}': expected parse error but parsing succeeded",
                        case.note
                    );
                }
                println!("passed (parsed ok)");
            }
            Err(e) => {
                if expects_parse_error {
                    println!("passed (expected parse error: {})", e);
                } else {
                    panic!("case '{}': unexpected parse error: {}", case.note, e);
                }
            }
        }
    }

    println!(
        "  Summary: {executed_count} executed, {skipped_count} skipped, {} total",
        test.cases.len()
    );
    Ok(())
}

#[test_resources("tests/azure_policy/parser_tests/cases/**/*.yaml")]
fn yaml_test(file: &str) {
    yaml_test_impl(file).unwrap();
}

/// Test duplicate-key detection directly (bypassing serde_json which
/// silently deduplicates keys).
#[test]
fn duplicate_key_in_condition() {
    // Two "field" keys in a single condition object.
    let json = r#"{"field": "type", "field": "name", "equals": "X"}"#;
    let source = Source::from_contents("test:dup_field".to_string(), json.to_string()).unwrap();
    let err = parser::parse_constraint(&source).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("duplicate key"),
        "expected duplicate key error, got: {msg}"
    );
}

#[test]
fn duplicate_key_in_count() {
    // Two "field" keys inside a count block.
    let json = r#"{"count": {"field": "a[*]", "field": "b[*]"}, "equals": 0}"#;
    let source =
        Source::from_contents("test:dup_count_field".to_string(), json.to_string()).unwrap();
    let err = parser::parse_constraint(&source).unwrap_err();
    let msg = err.to_string();
    assert!(
        msg.contains("duplicate key"),
        "expected duplicate key error, got: {msg}"
    );
}
