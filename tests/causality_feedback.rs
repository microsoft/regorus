// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Regression tests for the causality / partial-eval feedback items
//! filed against the `causality` branch.  Each test corresponds to a
//! numbered item in the feedback and asserts that the issue no longer
//! reproduces.

#![cfg(all(feature = "rvm", feature = "explanations"))]

use regorus::*;

fn run_causality_full(policy: &str, input_json: &str, entrypoint_str: &str) -> serde_json::Value {
    let mut engine = Engine::new();
    engine
        .add_policy("test.rego".into(), policy.into())
        .unwrap();

    let entrypoint: Rc<str> = entrypoint_str.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .unwrap();

    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        scope: evaluation_trace::ExplanationScope::AllEmissions,
        detail: evaluation_trace::ExplanationDetail::Full,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: false,
        eval_mode: evaluation_trace::EvaluationMode::Causality,
        ..Default::default()
    });

    let input: Value = serde_json::from_str(input_json).unwrap();
    vm.set_input(input);
    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();
    let report = vm.take_causality_report(value).unwrap();
    serde_json::from_str(&report).unwrap()
}

/// Find the first condition whose `text` contains `needle` anywhere in the
/// report's per-rule per-definition conditions array.
fn find_condition<'a>(
    report: &'a serde_json::Value,
    needle: &str,
) -> Option<&'a serde_json::Value> {
    let rules = report.get("rules")?.as_array()?;
    for rule in rules {
        let defs = rule.get("definitions")?.as_array()?;
        for def in defs {
            let conditions = def.get("conditions")?.as_array()?;
            for cond in conditions {
                if cond
                    .get("text")
                    .and_then(|t| t.as_str())
                    .is_some_and(|t| t.contains(needle))
                {
                    return Some(cond);
                }
            }
        }
    }
    None
}

/// Collect every condition across every (rule, definition).
fn all_conditions(report: &serde_json::Value) -> Vec<&serde_json::Value> {
    let mut out = Vec::new();
    if let Some(rules) = report.get("rules").and_then(|v| v.as_array()) {
        for rule in rules {
            if let Some(defs) = rule.get("definitions").and_then(|v| v.as_array()) {
                for def in defs {
                    if let Some(conds) = def.get("conditions").and_then(|v| v.as_array()) {
                        out.extend(conds.iter());
                    }
                }
            }
        }
    }
    out
}

// ===========================================================================
// Causality-2:  `not X == Y` should carry operator/operand provenance
// ===========================================================================
#[test]
fn causality_2_not_equals_carries_structure() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    not resource.allowSharedKeyAccess == false
    msg := sprintf("Storage '%s' must set allowSharedKeyAccess to false", [resource.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "badStorage",
            "properties": { "minimumTlsVersion": "TLS1_2" }
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not resource.allowSharedKeyAccess")
        .unwrap_or_else(|| panic!("missing condition; report: {report:#?}"));

    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("negation"),
        "not <comparison> should carry kind=negation, not truthiness; got: {cond:#?}"
    );
    assert_eq!(
        cond.get("operator").and_then(|v| v.as_str()),
        Some("=="),
        "inner operator should be preserved; got: {cond:#?}"
    );

    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains("allowSharedKeyAccess"),
        "left.provenance should resolve to the LHS input path; got '{left_prov}' in {cond:#?}"
    );
}

// ===========================================================================
// Causality-1:  `not <builtin>(...)` should at least carry input provenance
// ===========================================================================
#[test]
fn causality_1_not_builtin_carries_inner_provenance() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    not contains(resource.location, "us")
    msg := sprintf("Resource '%s' in disallowed region '%s'", [resource.name, resource.location])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "euStorage",
            "location": "westeurope",
            "properties": {}
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");
    let cond = find_condition(&report, "not contains(resource.location")
        .unwrap_or_else(|| panic!("missing condition; report: {report:#?}"));

    assert_eq!(
        cond.get("kind").and_then(|v| v.as_str()),
        Some("negation"),
        "not <builtin> should be reported as kind=negation, not truthiness; got: {cond:#?}"
    );

    // For builtin-call negations we may not surface an operator, but we
    // should at least attach the input-rooted provenance of the argument
    // (resource.location) somewhere — either as left.provenance or on the
    // condition's checked path.
    let left_prov = cond
        .get("left")
        .and_then(|l| l.get("provenance"))
        .and_then(|v| v.as_str())
        .unwrap_or("");
    assert!(
        left_prov.contains("location"),
        "left.provenance should point at resource.location; got '{left_prov}' in {cond:#?}"
    );
}

// ===========================================================================
// Causality-3:  rule.definitions[] must contain one entry per *evaluated*
// definition, not just the last one to run.
// ===========================================================================
#[test]
fn causality_3_multiple_definitions_each_reported() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    r.properties.supportsHttpsTrafficOnly == false
    msg := sprintf("Storage '%s' must enable HTTPS", [r.name])
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    r.properties.allowBlobPublicAccess == true
    msg := sprintf("Storage '%s' must not allow public blobs", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "demoissue7",
            "properties": {
                "supportsHttpsTrafficOnly": false,
                "allowBlobPublicAccess": true
            }
        }]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");

    let rule = report
        .get("rules")
        .and_then(|r| r.as_array())
        .and_then(|r| {
            r.iter()
                .find(|r| r.get("name").and_then(|n| n.as_str()) == Some("data.bicep.deny"))
        })
        .unwrap_or_else(|| panic!("missing data.bicep.deny rule in report: {report:#?}"));

    let defs = rule
        .get("definitions")
        .and_then(|v| v.as_array())
        .unwrap_or_else(|| panic!("missing definitions; rule: {rule:#?}"));

    // Both definitions fire, so both must be represented.
    assert_eq!(
        defs.len(),
        2,
        "expected 2 definition entries (one per fired deny block), got {}: {:#?}",
        defs.len(),
        defs
    );

    let mut indices: Vec<u64> = defs
        .iter()
        .filter_map(|d| d.get("index").and_then(|v| v.as_u64()))
        .collect();
    indices.sort_unstable();
    assert_eq!(
        indices,
        vec![0, 1],
        "definition entries should cover indices 0 and 1; got {indices:?}"
    );
}

// ===========================================================================
// Causality-4:  Undefined LHS in `X == Y` must use the resolved iterator
// index in provenance, not the `[_]` wildcard.
// ===========================================================================
#[test]
fn causality_4_undefined_lhs_uses_resolved_iterator_index() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    resource.properties.minimumTlsVersion == "TLS1_2"
    msg := sprintf("Storage '%s' is fine", [resource.name])
}
"#;
    let input = r#"{
        "resources": [
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "storageA",
                "properties": { "minimumTlsVersion": "TLS1_2" }
            },
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "storageB",
                "properties": {}
            },
            {
                "type": "Microsoft.Storage/storageAccounts",
                "name": "storageC",
                "properties": { "minimumTlsVersion": "TLS1_0" }
            }
        ]
    }"#;

    let report = run_causality_full(policy, input, "data.bicep.deny");

    // Find every comparison frame for resource.properties.minimumTlsVersion
    // across all iterations.
    let conds: Vec<_> = all_conditions(&report)
        .into_iter()
        .filter(|c| {
            c.get("text")
                .and_then(|t| t.as_str())
                .is_some_and(|t| t.contains("resource.properties.minimumTlsVersion"))
        })
        .collect();

    assert_eq!(
        conds.len(),
        3,
        "expected 3 comparison frames (one per iteration), got {}; report: {:#?}",
        conds.len(),
        report
    );

    for cond in &conds {
        let prov = cond
            .get("left")
            .and_then(|l| l.get("provenance"))
            .and_then(|v| v.as_str())
            .unwrap_or("");
        assert!(
            !prov.contains("[_]"),
            "iterator should be resolved to a concrete index, not [_]; got '{prov}' in {cond:#?}"
        );
        assert!(
            prov.starts_with("input.resources["),
            "provenance should be rooted at input.resources[N]; got '{prov}'"
        );
    }
}

// ===========================================================================
// PE test helpers
// ===========================================================================
fn run_pe(policy: &str, input_json: &str, entrypoint_str: &str) -> serde_json::Value {
    let mut engine = Engine::new();
    engine
        .add_policy("policy.rego".into(), policy.into())
        .unwrap();

    let entrypoint: Rc<str> = entrypoint_str.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program =
        languages::rego::compiler::Compiler::compile_from_policy(&compiled, &[entrypoint.as_ref()])
            .unwrap();

    let mut vm = rvm::RegoVM::new_with_policy(compiled);
    vm.load_program(program);
    vm.set_explanation_settings(evaluation_trace::ExplanationSettings {
        enabled: true,
        value_mode: evaluation_trace::ValueMode::Full,
        condition_mode: evaluation_trace::ConditionMode::AllContributing,
        scope: evaluation_trace::ExplanationScope::AllEmissions,
        detail: evaluation_trace::ExplanationDetail::Full,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: true,
        eval_mode: evaluation_trace::EvaluationMode::PartialEval,
        unknowns: vec!["input.deployment".into()],
    });

    let input: Value = serde_json::from_str(input_json).unwrap();
    vm.set_input(input);

    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();
    let report = vm.take_partial_eval_result(value).unwrap();
    serde_json::from_str(&report).unwrap()
}

// ===========================================================================
// PE-1: residual conditions carry source attribution (rule name + location).
// ===========================================================================
#[test]
fn pe_1_residual_conditions_carry_source_attribution() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    input.deployment.resourceGroupName == "prod-rg"
    r.properties.supportsHttpsTrafficOnly == false
    msg := sprintf("[https] Storage '%s' in prod-rg must enable HTTPS", [r.name])
}

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    input.deployment.location == "eastus"
    r.properties.allowBlobPublicAccess == true
    msg := sprintf("[blob] Storage '%s' in eastus must not allow public blobs", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "demoissue1",
            "location": "eastus",
            "properties": {
                "supportsHttpsTrafficOnly": false,
                "allowBlobPublicAccess": true
            }
        }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"]
        .as_array()
        .unwrap_or_else(|| panic!("missing residual_queries; got: {result:#?}"));

    assert!(
        !queries.is_empty(),
        "expected at least one residual disjunct; got: {result:#?}"
    );

    // Every condition in every disjunct must carry source attribution.
    for (i, disjunct) in queries.iter().enumerate() {
        for (j, cond) in disjunct.as_array().unwrap().iter().enumerate() {
            assert!(
                cond.get("source_rule")
                    .and_then(|v| v.as_str())
                    .is_some_and(|s| s == "data.bicep.deny"),
                "disjunct {i}, condition {j}: source_rule missing or wrong; got: {cond:#?}"
            );
            assert!(
                cond.get("source_file")
                    .and_then(|v| v.as_str())
                    .is_some_and(|s| s == "policy.rego"),
                "disjunct {i}, condition {j}: source_file missing or wrong; got: {cond:#?}"
            );
            assert!(
                cond.get("source_row").and_then(|v| v.as_u64()).is_some(),
                "disjunct {i}, condition {j}: source_row missing; got: {cond:#?}"
            );
        }
    }
}

// ===========================================================================
// PE-2: a concretely-firing rule no longer emits an empty negation_holds
// placeholder.
// ===========================================================================
#[test]
fn pe_2_concrete_rule_omits_empty_negation_placeholder() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.DocumentDB/databaseAccounts"
    not r.properties.disableLocalAuth == true
    msg := sprintf("Cosmos '%s' must disable local auth", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.DocumentDB/databaseAccounts",
            "name": "demoissue2",
            "location": "eastus",
            "properties": {
                "databaseAccountOfferType": "Standard"
            }
        }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"].as_array().unwrap();

    // None of the disjuncts may contain an empty negation_holds placeholder
    // (kind=negation_holds with no condition text, no input_path, no inner).
    for (i, disjunct) in queries.iter().enumerate() {
        for cond in disjunct.as_array().unwrap() {
            let kind = cond.get("kind").and_then(|v| v.as_str()).unwrap_or("");
            if kind == "negation_holds" {
                let has_condition = cond
                    .get("condition")
                    .and_then(|v| v.as_str())
                    .is_some_and(|s| !s.is_empty());
                let has_path = cond.get("input_path").is_some();
                let has_inner = cond
                    .get("negated_conditions")
                    .and_then(|v| v.as_array())
                    .is_some_and(|a| !a.is_empty());
                assert!(
                    has_condition || has_path || has_inner,
                    "disjunct {i} contains an empty negation_holds placeholder: {cond:#?}"
                );
            }
        }
    }
}

// ===========================================================================
// PE-3: trailing Rego comments are stripped from rendered condition strings.
// ===========================================================================
#[test]
fn pe_3_inline_comments_stripped_from_rendered_condition() {
    let policy = r#"
package bicep
import rego.v1

deny contains msg if {
    some r in input.resources
    r.type == "Microsoft.Storage/storageAccounts"
    input.deployment.location == "eastus"   # forces residual to remain (unknown)
    msg := sprintf("Storage '%s' violates", [r.name])
}
"#;
    let input = r#"{
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "demoissue3comment",
            "location": "eastus",
            "properties": {}
        }]
    }"#;

    let result = run_pe(policy, input, "data.bicep.deny");
    let queries = result["residual_queries"].as_array().unwrap();

    let mut found_location_cond = false;
    for disjunct in queries {
        for cond in disjunct.as_array().unwrap() {
            let text = cond.get("condition").and_then(|v| v.as_str()).unwrap_or("");
            if text.contains("input.deployment.location") {
                found_location_cond = true;
                assert!(
                    !text.contains('#'),
                    "rendered condition still contains trailing comment: '{text}' in {cond:#?}"
                );
            }
        }
    }
    assert!(
        found_location_cond,
        "expected a residual condition referencing input.deployment.location; got: {result:#?}"
    );
}
