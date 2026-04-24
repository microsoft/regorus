#![cfg(all(feature = "rvm", feature = "explanations"))]

//! Tests for partial evaluation mode.
//!
//! Each test loads a policy with unknown input (or partially known input),
//! runs evaluation in `PartialEval` mode with `assume_unknown_input = true`,
//! and verifies that the resulting `PartialEvalResult` contains the expected
//! residual queries (disjuncts of conditions).

use regorus::*;

/// Helper: build a VM in PE mode, run the query, and return the PE JSON result.
fn run_pe(
    policy: &str,
    input_json: Option<&str>,
    data_json: Option<&str>,
    entrypoint_str: &str,
) -> serde_json::Value {
    run_pe_with_unknowns(policy, input_json, data_json, entrypoint_str, None)
}

/// Like `run_pe` but accepts custom unknowns (None = default `["input"]`).
fn run_pe_with_unknowns(
    policy: &str,
    input_json: Option<&str>,
    data_json: Option<&str>,
    entrypoint_str: &str,
    unknowns: Option<Vec<String>>,
) -> serde_json::Value {
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
        assume_unknown_input: true,
        eval_mode: evaluation_trace::EvaluationMode::PartialEval,
        unknowns: unknowns.unwrap_or_else(|| vec!["input".into()]),
    });

    let input = match input_json {
        Some(j) => serde_json::from_str(j).unwrap(),
        None => Value::new_object(),
    };
    vm.set_input(input);

    if let Some(d) = data_json {
        let data: Value = serde_json::from_str(d).unwrap();
        let _ = vm.set_data(data);
    }

    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();

    let report_json = vm.take_partial_eval_result(value).unwrap();
    serde_json::from_str(&report_json).unwrap()
}

/// Helper: build a VM in Causality mode, run the query, and return the causality JSON report.
fn run_causality(
    policy: &str,
    input_json: Option<&str>,
    data_json: Option<&str>,
    entrypoint_str: &str,
) -> serde_json::Value {
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
        assume_unknown_input: true,
        eval_mode: evaluation_trace::EvaluationMode::Causality,
        ..Default::default()
    });

    let input = match input_json {
        Some(j) => serde_json::from_str(j).unwrap(),
        None => Value::new_object(),
    };
    vm.set_input(input);

    if let Some(d) = data_json {
        let data: Value = serde_json::from_str(d).unwrap();
        let _ = vm.set_data(data);
    }

    let value = vm.execute_entry_point_by_name(entrypoint_str).unwrap();
    let report_json = vm.take_causality_report(value).unwrap();
    serde_json::from_str(&report_json).unwrap()
}

// ---------------------------------------------------------------------------
// PE Test Cases
// ---------------------------------------------------------------------------

/// Case 01: Simple ABAC — two disjuncts, each with one condition.
#[test]
fn pe_01_simple_abac() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { input.document.status == "public" }
"#;
    let input = r#"{"user": {"role": "viewer"}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // Should have at least 1 disjunct (the user.role one may fail since viewer != admin,
    // but document.status is unknown and should be assumed).
    assert!(
        !queries.is_empty(),
        "should have residual queries, got: {result}"
    );
    // At least one disjunct should mention "input.document" (the unknown path)
    let has_document = queries.iter().any(|disjunct| {
        disjunct.as_array().unwrap().iter().any(|cond| {
            cond["input_path"]
                .as_str()
                .is_some_and(|p| p.contains("input.document"))
        })
    });
    assert!(
        has_document,
        "should have a condition about input.document, got: {result}"
    );
}

/// Case 02: Multi-branch ABAC — PE mode should explore all branches (not short-circuit).
#[test]
fn pe_02_multi_branch_abac() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if {
    input.document.status == "public"
    input.document.department == input.user.department
}
allow if { input.document.owner_id == input.user.id }
"#;
    let input = r#"{"user": {"id": "alice", "role": "viewer", "department": "engineering"}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // In PE mode, we should get multiple disjuncts:
    // - Branch 2: document.status == "public" AND document.department == "engineering"
    // - Branch 3: document.owner_id == "alice"
    // Branch 1 fails genuinely (viewer != admin).
    assert!(
        queries.len() >= 2,
        "PE mode should produce at least 2 disjuncts for multi-branch ABAC, got {} in: {}",
        queries.len(),
        result
    );
}

/// Case 03: Known iteration — roles are known, document required_role is unknown.
#[test]
fn pe_03_known_iteration() {
    let policy = r#"
package test
import data.user_roles
allow if {
    some role in user_roles[input.user.id]
    role == input.document.required_role
}
"#;
    let input = r#"{"user": {"id": "alice"}}"#;
    let data = r#"{"user_roles": {"alice": ["editor", "viewer", "reviewer"], "bob": ["viewer"]}}"#;
    let result = run_pe(policy, Some(input), Some(data), "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // Should have 3 disjuncts — one per role (editor, viewer, reviewer).
    assert_eq!(
        queries.len(),
        3,
        "PE should produce 3 disjuncts for 3-role iteration, got {}: {}",
        queries.len(),
        serde_json::to_string_pretty(&result).unwrap()
    );
    // Each disjunct should involve input.document (the unknown path)
    for disjunct in queries {
        let conds = disjunct.as_array().unwrap();
        let has_document = conds.iter().any(|c| {
            c["input_path"]
                .as_str()
                .is_some_and(|p| p.contains("input.document"))
                || c["condition"]
                    .as_str()
                    .is_some_and(|t| t.contains("required_role"))
        });
        assert!(
            has_document,
            "each disjunct should reference input.document or required_role"
        );
    }
}

/// Case 04: Nested iteration — known data, unknown document type.
#[test]
fn pe_04_nested_iteration() {
    let policy = r#"
package test
import data.user_roles
import data.role_permissions
allow if {
    some role in user_roles[input.user.id]
    some perm in role_permissions[role]
    perm.action == input.action
    perm.resource_type == input.document.type
}
"#;
    let input = r#"{"user": {"id": "alice"}, "action": "read"}"#;
    let data = r#"{
        "user_roles": {"alice": ["editor", "viewer"]},
        "role_permissions": {
            "editor": [
                {"action": "read", "resource_type": "document"},
                {"action": "write", "resource_type": "document"},
                {"action": "read", "resource_type": "image"}
            ],
            "viewer": [
                {"action": "read", "resource_type": "document"},
                {"action": "read", "resource_type": "image"}
            ]
        }
    }"#;
    let result = run_pe(policy, Some(input), Some(data), "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // Should produce 4 disjuncts: each matching role×perm combo where action=="read".
    // editor: (read,document), (read,image); viewer: (read,document), (read,image)
    assert!(
        queries.len() >= 4,
        "PE should produce at least 4 disjuncts for nested iteration, got {}: {}",
        queries.len(),
        serde_json::to_string_pretty(&result).unwrap()
    );
    // Verify that the conditions reference input.document (the unknown path)
    let has_doc = queries.iter().any(|disjunct| {
        disjunct.as_array().unwrap().iter().any(|c| {
            c["input_path"]
                .as_str()
                .is_some_and(|p| p.contains("input.document"))
                || c["condition"]
                    .as_str()
                    .is_some_and(|t| t.contains("document.type"))
        })
    });
    assert!(has_doc, "should reference input.document, got: {result}");
}

/// Case 06: Negation — `not blocked(input.document)` with unknown document.
#[test]
fn pe_06_negation() {
    let policy = r#"
package test
default allow = false
allow if { not blocked(input.document) }
blocked(doc) if { doc.status == "restricted" }
blocked(doc) if { doc.classification > 5 }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(queries.len(), 1, "should have 1 disjunct");
    let conj = queries[0].as_array().unwrap();
    assert_eq!(
        conj.len(),
        1,
        "should have 1 condition (the negation_holds)"
    );
    assert_eq!(conj[0]["kind"], "negation_holds");
    // The negation should wrap the inner rule's conditions.
    let inner = conj[0]["negated_conditions"].as_array().unwrap();
    assert!(
        !inner.is_empty(),
        "negation_holds should have inner conditions from blocked() rule"
    );
    // Inner conditions should include the blocked rule's body conditions.
    let has_status = inner
        .iter()
        .any(|c| c["kind"] == "condition_holds" && c["operator"] == "==");
    let has_classification = inner
        .iter()
        .any(|c| c["kind"] == "condition_holds" && c["operator"] == ">");
    assert!(has_status, "inner should have status == restricted");
    assert!(has_classification, "inner should have classification > 5");
}

/// Case 07: Helper rules — PE should inline through helper rules and produce multiple disjuncts.
#[test]
fn pe_07_helper_rules() {
    let policy = r#"
package test
default allow = false
allow if { is_owner(input.user, input.document) }
allow if {
    is_department_member(input.user, input.document)
    input.document.status == "published"
}
is_owner(user, doc) if { doc.owner_id == user.id }
is_department_member(user, doc) if { doc.department == user.department }
"#;
    let input = r#"{"user": {"id": "alice", "role": "viewer", "department": "engineering"}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // Should produce at least 2 disjuncts:
    // - owner_id == "alice"
    // - department == "engineering" AND status == "published"
    assert!(
        queries.len() >= 2,
        "PE should produce at least 2 disjuncts for helper rules, got {} in: {}",
        queries.len(),
        result
    );
}

/// Case 08: Collection membership — check if document has required tags.
#[test]
fn pe_08_collection_membership() {
    let policy = r#"
package test
import data.required_tags
allow if {
    some tag in required_tags
    tag in input.document.tags
}
"#;
    let data = r#"{"required_tags": ["confidential", "internal", "public"]}"#;
    let result = run_pe(policy, None, Some(data), "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // Should have 3 disjuncts — one per tag (confidential, internal, public).
    assert_eq!(
        queries.len(),
        3,
        "PE should produce 3 disjuncts for 3-tag membership, got {}: {}",
        queries.len(),
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 09: Nested negation — negation with nested unknown dependency.
#[test]
fn pe_09_nested_negation() {
    let policy = r#"
package test
default allow = false
allow if {
    input.user.role == "viewer"
    not is_restricted(input.document)
}
allow if { input.user.role == "admin" }
is_restricted(doc) if {
    doc.status == "restricted"
    not doc.override == true
}
"#;
    let input = r#"{"user": {"role": "viewer"}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");

    // The admin branch should fail: viewer != admin.
    // The viewer branch should succeed with negation assumed.
    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        1,
        "should have 1 disjunct (viewer branch only)"
    );
    let conj = queries[0].as_array().unwrap();
    // Should contain a negation_holds wrapping the is_restricted inner conditions.
    let has_negation = conj.iter().any(|c| c["kind"] == "negation_holds");
    assert!(
        has_negation,
        "should have negation_holds for not is_restricted(doc)"
    );
    // The negation_holds should have nested inner conditions.
    let neg = conj.iter().find(|c| c["kind"] == "negation_holds").unwrap();
    let inner = neg["negated_conditions"].as_array().unwrap();
    assert!(
        !inner.is_empty(),
        "negation_holds should have inner conditions from is_restricted()"
    );
}

// ---------------------------------------------------------------------------
// Causality mode tests with the same scenarios
// ---------------------------------------------------------------------------

/// Causality mode: Case 01 — verify assumptions list includes the assumed condition.
#[test]
fn causality_01_simple_abac() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { input.document.status == "public" }
"#;
    let input = r#"{"user": {"role": "viewer"}}"#;
    let report = run_causality(policy, Some(input), None, "data.test.allow");

    assert_eq!(report["query_result"], true);
    let assumptions = report["assumptions"].as_array().unwrap();
    assert!(!assumptions.is_empty(), "should have assumptions");
}

/// Causality mode: Case 03 — known iteration with unknown required_role.
#[test]
fn causality_03_known_iteration() {
    let policy = r#"
package test
import data.user_roles
allow if {
    some role in user_roles[input.user.id]
    role == input.document.required_role
}
"#;
    let input = r#"{"user": {"id": "alice"}}"#;
    let data = r#"{"user_roles": {"alice": ["editor", "viewer", "reviewer"]}}"#;
    let report = run_causality(policy, Some(input), Some(data), "data.test.allow");

    assert_eq!(report["query_result"], true);
    let assumptions = report["assumptions"].as_array().unwrap();
    assert!(
        !assumptions.is_empty(),
        "should have assumptions about required_role"
    );
    let has_document = assumptions.iter().any(|a| {
        a["input_path"]
            .as_str()
            .is_some_and(|p| p.contains("input.document"))
            || a["assumed_holds"]
                .as_str()
                .is_some_and(|t| t.contains("required_role"))
    });
    assert!(
        has_document,
        "should mention input.document or required_role"
    );
}

/// Causality mode: Case 07 — helper rules with unknown document.
#[test]
fn causality_07_helper_rules() {
    let policy = r#"
package test
default allow = false
allow if { is_owner(input.user, input.document) }
allow if {
    is_department_member(input.user, input.document)
    input.document.status == "published"
}
is_owner(user, doc) if { doc.owner_id == user.id }
is_department_member(user, doc) if { doc.department == user.department }
"#;
    let input = r#"{"user": {"id": "alice", "role": "viewer", "department": "engineering"}}"#;
    let report = run_causality(policy, Some(input), None, "data.test.allow");

    assert_eq!(report["query_result"], true);
    let assumptions = report["assumptions"].as_array().unwrap();
    assert!(!assumptions.is_empty(), "should have assumptions");
}

/// Case 10: Comprehension + count — comprehension body succeeds via assumptions,
/// count threshold may be unsound. Should produce a soundness warning.
#[test]
fn pe_10_comprehension_count_threshold() {
    let policy = r#"
package test
import data.user_roles
import data.role_permissions
allow if {
    actions := {perm.action |
        some role in user_roles[input.user.id]
        some perm in role_permissions[role]
        perm.resource_type == input.document.type
    }
    count(actions) >= 2
}
"#;
    let input = r#"{"user": {"id": "alice"}}"#;
    let data = r#"{
        "user_roles": {"alice": ["editor", "viewer"]},
        "role_permissions": {
            "editor": [
                {"action": "read", "resource_type": "document"},
                {"action": "write", "resource_type": "document"},
                {"action": "read", "resource_type": "image"}
            ],
            "viewer": [
                {"action": "read", "resource_type": "document"},
                {"action": "read", "resource_type": "image"}
            ]
        }
    }"#;
    let result = run_pe(policy, Some(input), Some(data), "data.test.allow");

    // The comprehension body succeeds via assumptions about input.document.type.
    // The count threshold may pass trivially — this is unsound.
    // We expect a warning about comprehension soundness.
    let warnings = result["warnings"].as_array();
    assert!(
        warnings.is_some_and(|w| !w.is_empty()),
        "should have comprehension soundness warning, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    let has_comprehension_warning = warnings.unwrap().iter().any(|w| {
        w.as_str()
            .is_some_and(|s| s.contains("comprehension") && s.contains("conditional"))
    });
    assert!(
        has_comprehension_warning,
        "should warn about comprehension being conditional on assumed inputs"
    );
}

/// Case 11: `every` over unknown collection — should produce a warning about vacuous truth
/// and record a CollectionExists assumption.
#[test]
fn pe_11_every_unknown_collection() {
    let policy = r#"
package test
import data.blocked_tags
default allow = false
allow if {
    every tag in input.document.tags {
        not tag in blocked_tags
    }
}
"#;
    let data = r#"{"blocked_tags": ["malware", "exploit"]}"#;
    let result = run_pe(policy, None, Some(data), "data.test.allow");

    // `every` over an unknown collection is vacuously true.
    // Phase 2A should record a CollectionExists assumption and a warning.
    assert_eq!(
        result["result"], true,
        "every over unknown should still be vacuously true, got: {result}"
    );

    // Should have a warning about vacuous truth
    let warnings = result["warnings"].as_array();
    assert!(
        warnings.is_some_and(|w| !w.is_empty()),
        "should have a warning about every over unknown collection, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    let has_every_warning = warnings.unwrap().iter().any(|w| {
        w.as_str()
            .is_some_and(|s| s.contains("every") && s.contains("unknown collection"))
    });
    assert!(
        has_every_warning,
        "should warn about every over unknown collection, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );

    // Should have residual queries with a CollectionExists assumption
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "should have residual queries with collection_exists assumption, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    let has_collection_exists = queries.iter().any(|disjunct| {
        disjunct.as_array().unwrap().iter().any(|c| {
            c["kind"] == "collection_exists"
                && c["input_path"]
                    .as_str()
                    .is_some_and(|p| p.contains("input.document"))
        })
    });
    assert!(
        has_collection_exists,
        "should have collection_exists assumption for input.document.tags, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 12: Builtins with unknown args — `startswith` and `contains` on unknown input
/// should produce assumptions instead of silently failing.
#[test]
fn pe_12_builtin_unknown_args() {
    let policy = r#"
package test
default allow = false
allow if {
    startswith(input.document.path, "/public/")
}
allow if {
    contains(input.document.name, "report")
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");

    assert_eq!(
        result["result"], true,
        "builtins on unknown args should succeed with assumptions, got: {result}"
    );
    let queries = result["residual_queries"].as_array().unwrap();
    // Should have 2 disjuncts — one for startswith, one for contains.
    assert!(
        queries.len() >= 2,
        "PE should produce at least 2 disjuncts for builtin assumptions, got {}: {}",
        queries.len(),
        serde_json::to_string_pretty(&result).unwrap()
    );
    // At least one disjunct should reference input.document.path or input.document.name
    let has_document = queries.iter().any(|disjunct| {
        disjunct.as_array().unwrap().iter().any(|c| {
            c["input_path"]
                .as_str()
                .is_some_and(|p| p.contains("input.document"))
        })
    });
    assert!(
        has_document,
        "should have assumptions about input.document paths, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 13: Deep nested path iteration — 5+ level nesting should still
/// produce assumptions (provenance chain must survive through chained index).
#[test]
fn pe_13_deep_path_iteration() {
    let policy = r#"
package test
default allow = false
allow if {
    some group in input.request.context.auth.claims.groups
    group == "security"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");

    assert_eq!(
        result["result"], true,
        "deep path iteration over unknowns should succeed with assumptions, got: {result}"
    );
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "should have residual queries for deep path, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    // The assumption should reference the deeply-nested input path
    let has_deep_path = queries.iter().any(|disjunct| {
        disjunct.as_array().unwrap().iter().any(|c| {
            c["input_path"]
                .as_str()
                .is_some_and(|p| p.starts_with("input.request"))
        })
    });
    assert!(
        has_deep_path,
        "should have assumptions about deeply nested input path, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 14: Virtual doc (partial object) with unknown key lookup — should produce
/// assumptions about the unknown key instead of silently returning Undefined.
#[test]
fn pe_14_virtual_doc_unknown_key() {
    let policy = r#"
package test

permissions["document"] := "write"
permissions["report"] := "read"

default allow = false
allow if {
    permissions[input.document.type] == "write"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");

    assert_eq!(
        result["result"], true,
        "virtual doc with unknown key should succeed with assumptions, got: {result}"
    );
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "should have residual queries for virtual doc unknown key, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    // The assumption should reference the input path
    let has_input = queries.iter().any(|disjunct| {
        disjunct.as_array().unwrap().iter().any(|c| {
            c["input_path"]
                .as_str()
                .is_some_and(|p| p.contains("input.document"))
        })
    });
    assert!(
        has_input,
        "should have assumptions about input.document.type, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

// ---------------------------------------------------------------------------
// Case 15: Selective unknowns — only specified prefixes produce assumptions
// ---------------------------------------------------------------------------
#[test]
fn pe_15_selective_unknowns() {
    // Two independent rules check different input branches.
    // With selective unknowns, only paths under the specified prefix produce assumptions.
    let policy = r#"
package test

default allow = false

# Rule A: checks input.document (will be in unknowns)
allow if {
    input.document.level == "public"
}

# Rule B: checks input.action (will NOT be in unknowns)
allow if {
    input.action == "read"
}
"#;

    // With default unknowns (["input"]) — both rules produce assumptions → 2 disjuncts.
    let result_all = run_pe(policy, None, None, "data.test.allow");
    assert_eq!(
        result_all["result"], true,
        "default unknowns should succeed"
    );
    let queries_all = result_all["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries_all.len(),
        2,
        "default unknowns should produce 2 disjuncts (one per rule), got: {}",
        serde_json::to_string_pretty(&result_all).unwrap()
    );

    // With selective unknowns (["input.document"]) — only rule A produces assumptions.
    // Rule B fails genuinely since input.action is not under any unknown prefix.
    let result_selective = run_pe_with_unknowns(
        policy,
        None,
        None,
        "data.test.allow",
        Some(vec!["input.document".into()]),
    );
    assert_eq!(
        result_selective["result"],
        true,
        "selective unknowns: rule A should still succeed, got: {}",
        serde_json::to_string_pretty(&result_selective).unwrap()
    );
    let queries_sel = result_selective["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries_sel.len(),
        1,
        "selective unknowns should produce exactly 1 disjunct (only rule A), got: {}",
        serde_json::to_string_pretty(&result_selective).unwrap()
    );
    // The single disjunct should reference input.document, not input.action.
    let cond = &queries_sel[0].as_array().unwrap()[0];
    assert!(
        cond["input_path"]
            .as_str()
            .is_some_and(|p| p.starts_with("input.document")),
        "the residual should reference input.document, got: {}",
        serde_json::to_string_pretty(&cond).unwrap()
    );
}

// ---------------------------------------------------------------------------
// Case 16: Else — primary body known false, else has unknown → else fires
// ---------------------------------------------------------------------------
#[test]
fn pe_16_else_fallthrough_to_unknown() {
    // Primary body uses a known-false condition, so it fails definitively.
    // Else body checks unknown input → should produce an assumption.
    let policy = r#"
package test

authz := "admin" if {
    1 == 2
} else := "reviewer" if {
    input.user.role == "reviewer"
}
"#;
    let result = run_pe(policy, None, None, "data.test.authz");
    eprintln!(
        "pe_16 result: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );

    // The primary body (1==2) always fails → falls through to else.
    // The else body has unknown input → assumed true → result is "reviewer".
    assert_eq!(
        result["result"],
        "reviewer",
        "else body should fire when primary is known-false, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "should have residual queries from else body"
    );
}

// ---------------------------------------------------------------------------
// Case 17: Else — primary body has unknown (assumed true) → else skipped
// ---------------------------------------------------------------------------
#[test]
fn pe_17_else_primary_unknown_succeeds() {
    // Primary body checks unknown input → assumed true → succeeds.
    // Current behavior: else body is skipped (the `break` in the inner loop).
    // This is conservative — we get the primary's assumption but not the else alternative.
    let policy = r#"
package test

authz := "admin" if {
    input.user.is_admin == true
} else := "reviewer" if {
    input.user.role == "reviewer"
} else := "deny"
"#;
    let result = run_pe(policy, None, None, "data.test.authz");
    eprintln!(
        "pe_17 result: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );

    // Primary body assumed true → result is "admin".
    assert_eq!(
        result["result"],
        "admin",
        "primary body should succeed with assumption, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "should have residual queries from primary body"
    );
    // Verify the assumption is about is_admin, not role.
    let has_admin = queries.iter().any(|d| {
        d.as_array().unwrap().iter().any(|c| {
            c["condition"]
                .as_str()
                .is_some_and(|t| t.contains("is_admin"))
        })
    });
    assert!(has_admin, "assumption should reference is_admin");
}

// ---------------------------------------------------------------------------
// Case 18: Else — primary known false, else known false, final else (no condition) → value
// ---------------------------------------------------------------------------
#[test]
fn pe_18_else_chain_falls_to_default() {
    // All conditional branches fail definitively (no unknowns involved).
    // The final else with no condition → value is "deny".
    let policy = r#"
package test

authz := "admin" if {
    1 == 2
} else := "reviewer" if {
    3 == 4
} else := "deny"
"#;
    let result = run_pe(policy, None, None, "data.test.authz");
    eprintln!(
        "pe_18 result: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );

    assert_eq!(
        result["result"],
        "deny",
        "should fall through to unconditional else, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        queries.is_empty(),
        "no unknowns involved → no residual queries, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

// ---------------------------------------------------------------------------
// Case 19: Else — mixed: primary known false, else unknown, final else default
// ---------------------------------------------------------------------------
#[test]
fn pe_19_else_mixed_known_unknown_default() {
    // Primary: known false. Else: unknown input → assumed true → "reviewer".
    // The unconditional else := "deny" should NOT be reached.
    let policy = r#"
package test

authz := "admin" if {
    1 == 2
} else := "reviewer" if {
    input.user.department == "security"
} else := "deny"
"#;
    let result = run_pe(policy, None, None, "data.test.authz");
    eprintln!(
        "pe_19 result: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );

    // Primary fails → else with unknown → assumed true → "reviewer"
    assert_eq!(
        result["result"],
        "reviewer",
        "should get reviewer from else body with assumption, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "should have residual for the department check"
    );
    let has_dept = queries.iter().any(|d| {
        d.as_array().unwrap().iter().any(|c| {
            c["input_path"]
                .as_str()
                .is_some_and(|p| p.contains("input.user"))
        })
    });
    assert!(has_dept, "residual should reference input.user.department");
}

// ===========================================================================
// Complex partial evaluation scenarios
// ===========================================================================

// ---------------------------------------------------------------------------
// Case 20: Multiple definitions — independent rules contributing disjuncts
// ---------------------------------------------------------------------------
#[test]
fn pe_20_multiple_definitions_disjuncts() {
    // Three separate rule definitions for `allow`, each checking different
    // unknown input paths. Should produce 3 independent disjuncts.
    let policy = r#"
package test

default allow = false

allow if {
    input.user.role == "admin"
}

allow if {
    input.user.role == "editor"
    input.resource.public == true
}

allow if {
    input.user.department == "legal"
    input.resource.classification == "internal"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_20: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // 3 definitions → 3 disjuncts
    assert_eq!(
        queries.len(),
        3,
        "3 definitions should produce 3 disjuncts, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
    // First disjunct: 1 condition (role==admin)
    assert_eq!(queries[0].as_array().unwrap().len(), 1);
    // Second disjunct: 2 conditions (role==editor AND resource.public==true)
    assert_eq!(queries[1].as_array().unwrap().len(), 2);
    // Third disjunct: 2 conditions (department==legal AND classification==internal)
    assert_eq!(queries[2].as_array().unwrap().len(), 2);
}

// ---------------------------------------------------------------------------
// Case 21: Set comprehension with unknown iteration — comprehension warning
// ---------------------------------------------------------------------------
#[test]
fn pe_21_set_comprehension_unknown() {
    // A set comprehension iterates over unknown input collection.
    // The comprehension itself may produce warnings about soundness.
    let policy = r#"
package test

default allow = false

matching_tags := {tag |
    some tag in input.document.tags
    tag in {"confidential", "restricted"}
}

allow if {
    count(matching_tags) > 0
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_21: {}", serde_json::to_string_pretty(&result).unwrap());

    // The comprehension iterates over unknown collection. Some result is expected.
    // Check that warnings are surfaced about comprehension soundness.
    let warnings = result["warnings"].as_array();
    eprintln!("pe_21 warnings: {:?}", warnings);
}

// ---------------------------------------------------------------------------
// Case 22: Object comprehension with known keys, unknown values
// ---------------------------------------------------------------------------
#[test]
fn pe_22_object_comprehension_unknown_values() {
    // Build an object from known iteration but with values derived from unknown input.
    let policy = r#"
package test

roles := ["admin", "editor", "viewer"]

access_map := {role: level |
    some role in roles
    level := input.permissions[role]
}

allow if {
    access_map["admin"] == "full"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_22: {}", serde_json::to_string_pretty(&result).unwrap());

    // The comprehension depends on unknown input.permissions, so we should get
    // a residual with an exists condition.
    let queries = result["residual_queries"]
        .as_array()
        .expect("residual_queries");
    assert!(
        !queries.is_empty(),
        "expected at least one residual disjunct"
    );
    let disjunct = queries[0].as_array().expect("disjunct");
    assert!(!disjunct.is_empty(), "expected at least one condition");
    assert_eq!(disjunct[0]["kind"], "exists");
    assert_eq!(disjunct[0]["input_path"], "input.permissions");
}

// ---------------------------------------------------------------------------
// Case 23: Nested function call — function checks unknown input
// ---------------------------------------------------------------------------
#[test]
fn pe_23_function_with_unknown_arg() {
    // A helper function receives unknown input as argument and checks it.
    // The assumption should propagate through the function call.
    let policy = r#"
package test

default allow = false

is_authorized(user, action) if {
    user.role == "admin"
}

is_authorized(user, action) if {
    user.role == "editor"
    action == "read"
}

allow if {
    is_authorized(input.user, input.action)
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_23: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // Function has 2 definitions → should produce assumptions
    assert!(
        !queries.is_empty(),
        "function call with unknown args should produce residuals"
    );
}

// ---------------------------------------------------------------------------
// Case 24: Deeply nested object access — 6+ levels
// ---------------------------------------------------------------------------
#[test]
fn pe_24_deeply_nested_object() {
    // Access a very deeply nested unknown input path.
    let policy = r#"
package test

default allow = false

allow if {
    input.request.context.auth.claims.groups.primary == "security-team"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_24: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(queries.len(), 1);
    // Should reference the deep path
    let path = queries[0].as_array().unwrap()[0]["input_path"]
        .as_str()
        .unwrap();
    eprintln!("pe_24 path: {}", path);
    assert!(
        path.starts_with("input.request"),
        "should reference deep input path, got: {path}"
    );
}

// ---------------------------------------------------------------------------
// Case 25: Array index access with unknown input
// ---------------------------------------------------------------------------
#[test]
fn pe_25_array_index_unknown() {
    // Access a specific array index from unknown input.
    let policy = r#"
package test

default allow = false

allow if {
    input.users[0].role == "admin"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_25: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "should produce residuals for array index access"
    );
}

// ---------------------------------------------------------------------------
// Case 26: Mixed known data + unknown input — partial object lookup
// ---------------------------------------------------------------------------
#[test]
fn pe_26_mixed_known_data_unknown_input() {
    // Data contains a mapping from role→permissions. Input provides the role.
    // The lookup should work with known data but unknown key.
    let policy = r#"
package test

default allow = false

allow if {
    data.role_permissions[input.user.role] == "write"
}
"#;
    let data = r#"{"role_permissions": {"admin": "write", "editor": "read", "viewer": "none"}}"#;
    let result = run_pe(policy, None, Some(data), "data.test.allow");
    eprintln!("pe_26: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(queries.len(), 1, "should produce 1 disjunct");
    let conj = queries[0].as_array().unwrap();
    assert_eq!(conj.len(), 1, "should produce 1 condition");
    // Data lookup inverted: data has {"admin":"write",...} so input.user.role must be "admin".
    assert_eq!(conj[0]["kind"], "condition_holds");
    assert_eq!(conj[0]["input_path"], "input.user.role");
    assert_eq!(conj[0]["operator"], "==");
    assert_eq!(conj[0]["value"], "admin");
}

// ---------------------------------------------------------------------------
// Case 27: Iteration over known set with unknown input comparison
// ---------------------------------------------------------------------------
#[test]
fn pe_27_known_iteration_unknown_comparison() {
    // Iterate over a known set of allowed actions, compare each against unknown input.
    let policy = r#"
package test

default allow = false

allowed_actions := {"read", "list", "describe"}

allow if {
    some action in allowed_actions
    input.request.action == action
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_27: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // 3 known actions → 3 disjuncts (one per iteration)
    assert_eq!(
        queries.len(),
        3,
        "3 known actions should produce 3 disjuncts, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

// ---------------------------------------------------------------------------
// Case 28: Nested iteration — known outer × unknown inner condition
// ---------------------------------------------------------------------------
#[test]
fn pe_28_nested_known_outer_unknown_inner() {
    // Outer loop over known data, inner condition on unknown input.
    let policy = r#"
package test

default allow = false

resources := ["db", "cache", "queue"]

allow if {
    some res in resources
    input.permissions[res] == "allow"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_28: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // 3 resources × unknown permission check → 3 disjuncts
    assert_eq!(
        queries.len(),
        3,
        "3 resources should produce 3 disjuncts, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

// ---------------------------------------------------------------------------
// Case 29: Multiple builtins — startswith, endswith, regex.match
// ---------------------------------------------------------------------------
#[test]
fn pe_29_multiple_builtins_unknown() {
    // Multiple builtin calls with unknown input arguments.
    let policy = r#"
package test

default allow = false

allow if {
    startswith(input.request.path, "/api/")
    endswith(input.request.path, "/read")
}

allow if {
    startswith(input.request.path, "/public/")
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_29: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // 2 definitions → 2 disjuncts
    // First disjunct has 2 conditions (startswith AND endswith)
    // Second disjunct has 1 condition (startswith)
    assert_eq!(queries.len(), 2, "should produce 2 disjuncts");
}

// ---------------------------------------------------------------------------
// Case 30: Partial rule (set) with unknown membership test
// ---------------------------------------------------------------------------
#[test]
fn pe_30_partial_set_unknown_membership() {
    // A partial set rule collects known values. Then we test membership
    // of an unknown input value in that set.
    let policy = r#"
package test

default allow = false

privileged_users contains user if {
    some user in {"alice", "bob", "charlie"}
}

allow if {
    input.user.name in privileged_users
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_30: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "membership test with unknown input should produce residuals"
    );
}

// ---------------------------------------------------------------------------
// Case 31: Partial object rule with multiple entries + unknown key lookup
// ---------------------------------------------------------------------------
#[test]
fn pe_31_partial_object_multi_entries() {
    // A partial object has multiple key-value entries defined by separate rules.
    // Looking up with an unknown key should still produce assumptions.
    let policy = r#"
package test

default allow = false

permissions["documents"] := "read"
permissions["reports"] := "write"
permissions["settings"] := "admin"

allow if {
    permissions[input.resource.type] == "write"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_31: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "partial object with unknown key should produce residuals"
    );
}

// ---------------------------------------------------------------------------
// Case 32: Negation with unknown — `not input.x`
// ---------------------------------------------------------------------------
#[test]
fn pe_32_negation_unknown_direct() {
    // `not` applied to a condition involving unknown input.
    let policy = r#"
package test

default allow = false

allow if {
    not input.user.blocked
    input.user.role == "member"
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(queries.len(), 1, "should have 1 disjunct");
    let conj = queries[0].as_array().unwrap();
    assert_eq!(
        conj.len(),
        2,
        "should have 2 conditions: negation_holds + role check"
    );
    // One condition should be the negation.
    let neg = conj.iter().find(|c| c["kind"] == "negation_holds");
    assert!(
        neg.is_some(),
        "should have negation_holds for not input.user.blocked"
    );
    let neg = neg.unwrap();
    // The negation should wrap an inner Exists condition for the blocked path.
    let inner = neg["negated_conditions"].as_array().unwrap();
    assert!(
        !inner.is_empty(),
        "negation_holds should have inner exists condition for input.user.blocked"
    );
    assert_eq!(inner[0]["kind"], "exists");
    // The other condition should be the role check.
    let role = conj.iter().find(|c| c["kind"] == "condition_holds");
    assert!(
        role.is_some(),
        "should have condition_holds for role == member"
    );
}

// ---------------------------------------------------------------------------
// Case 33: Chained helper rules — A calls B calls C, all with unknowns
// ---------------------------------------------------------------------------
#[test]
fn pe_33_chained_helper_rules() {
    // Three levels of helper rule calls, each adding conditions.
    let policy = r#"
package test

default allow = false

is_valid_request if {
    input.request.method == "GET"
}

is_authorized_user if {
    input.user.active == true
    is_valid_request
}

allow if {
    is_authorized_user
    input.resource.public == true
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_33: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        3,
        "chained helpers produce separate conjunctions per rule call"
    );
    // Each conjunction should have 1 condition
    for (i, q) in queries.iter().enumerate() {
        let conditions = q.as_array().unwrap();
        assert_eq!(
            conditions.len(),
            1,
            "conjunction {} should have 1 condition, got: {}",
            i,
            serde_json::to_string_pretty(q).unwrap()
        );
    }
}

// ---------------------------------------------------------------------------
// Case 34: Function returning value used in comparison
// ---------------------------------------------------------------------------
#[test]
fn pe_34_function_return_value() {
    // A function computes a value from known data. The result is compared
    // against unknown input.
    let policy = r#"
package test

default allow = false

min_level := 3

required_clearance(resource) := 5 if {
    resource == "top-secret"
} else := 3 if {
    resource == "confidential"
} else := 1

allow if {
    input.user.clearance >= required_clearance(input.resource.classification)
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_34: {}", serde_json::to_string_pretty(&result).unwrap());
    // This is a complex case — the function arg is unknown, so the function
    // result is unknown, and then >= comparison has both sides unknown.
}

// ---------------------------------------------------------------------------
// Case 35: `every` with known collection + unknown body condition
// ---------------------------------------------------------------------------
#[test]
fn pe_35_every_known_collection_unknown_body() {
    // `every` iterates over a known collection, but the body checks unknown input.
    let policy = r#"
package test

default allow = false

required_approvals := {"manager", "director", "vp"}

allow if {
    every role in required_approvals {
        role in input.document.approvals
    }
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_35: {}", serde_json::to_string_pretty(&result).unwrap());

    // `every` over known collection with unknown body should produce
    // assumptions for each iteration.
    assert_eq!(result["result"], true);
}

// ---------------------------------------------------------------------------
// Case 36: `in` operator — unknown value in known set
// ---------------------------------------------------------------------------
#[test]
fn pe_36_unknown_in_known_set() {
    let policy = r#"
package test

default allow = false

allowed_regions := {"us-east-1", "us-west-2", "eu-west-1"}

allow if {
    input.request.region in allowed_regions
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_36: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "`in` with unknown value should produce residuals"
    );
}

// ---------------------------------------------------------------------------
// Case 37: Complex RBAC — roles from data, permissions from data, user from input
// ---------------------------------------------------------------------------
#[test]
fn pe_37_rbac_data_roles_unknown_user() {
    // Realistic RBAC: roles and permissions in data, user identity in input.
    let policy = r#"
package test

default allow = false

user_roles[role] if {
    some role in data.role_bindings[input.user.name]
}

allow if {
    some role in user_roles
    some perm in data.role_permissions[role]
    perm == input.request.action
}
"#;
    let data = r#"{
        "role_bindings": {
            "alice": ["admin", "editor"],
            "bob": ["viewer"]
        },
        "role_permissions": {
            "admin": ["read", "write", "delete"],
            "editor": ["read", "write"],
            "viewer": ["read"]
        }
    }"#;
    let result = run_pe(policy, None, Some(data), "data.test.allow");
    eprintln!("pe_37: {}", serde_json::to_string_pretty(&result).unwrap());
}

// ---------------------------------------------------------------------------
// Case 38: Combination — multiple definitions with different patterns
// ---------------------------------------------------------------------------
#[test]
fn pe_38_combined_patterns() {
    // One rule uses iteration, another uses negation, another uses builtins.
    let policy = r#"
package test

default allow = false

# Definition 1: role-based with iteration
allow if {
    some role in {"admin", "superuser"}
    input.user.role == role
}

# Definition 2: path-based with builtin
allow if {
    startswith(input.request.path, "/public/")
}

# Definition 3: negation-based
allow if {
    not input.user.suspended
    input.user.verified == true
}
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_38: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // Definition 1: 2 iterations → 2 disjuncts
    // Definition 2: 1 disjunct (builtin)
    // Definition 3: 1 or 2 disjuncts (negation + verified)
    // Total: at least 4 disjuncts
    assert!(
        queries.len() >= 4,
        "combined patterns should produce at least 4 disjuncts, got {}: {}",
        queries.len(),
        serde_json::to_string_pretty(&result).unwrap()
    );
}

// ---------------------------------------------------------------------------
// Case 39: Known input partially provided — only unknown fields assumed
// ---------------------------------------------------------------------------
#[test]
fn pe_39_partially_known_input() {
    // Some input fields are provided (known), others are absent (unknown).
    // Only the unknown fields should produce assumptions.
    let policy = r#"
package test

default allow = false

allow if {
    input.user.role == "admin"
    input.resource.owner == input.user.name
}
"#;
    // Provide user.role="admin" but NOT resource.owner or user.name
    let input = r#"{"user": {"role": "admin"}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");
    eprintln!("pe_39: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    // role=="admin" is satisfied by known input → no assumption for it.
    // resource.owner == user.name has unknowns → should produce assumption.
    assert_eq!(queries.len(), 1, "should have 1 disjunct");
    // The assumptions should NOT reference input.user.role (it's known)
    let has_role_assumption = queries[0].as_array().unwrap().iter().any(|c| {
        c["condition"]
            .as_str()
            .is_some_and(|t| t.contains("role") && t.contains("admin"))
    });
    assert!(
        !has_role_assumption,
        "known input.user.role should NOT produce an assumption, got: {}",
        serde_json::to_string_pretty(&queries[0]).unwrap()
    );
}

// ---------------------------------------------------------------------------
// Case 40: Nested comprehension — set of sets
// ---------------------------------------------------------------------------
#[test]
fn pe_40_nested_comprehension() {
    // A comprehension builds a set, then another rule checks its count.
    let policy = r#"
package test

default deny = false

violations contains msg if {
    input.resource.public == false
    msg := "resource is not public"
}

violations contains msg if {
    input.user.mfa_enabled == false
    msg := "MFA not enabled"
}

deny if {
    count(violations) > 0
}
"#;
    let result = run_pe(policy, None, None, "data.test.deny");
    eprintln!("pe_40: {}", serde_json::to_string_pretty(&result).unwrap());
}

// ---------------------------------------------------------------------------
// Case 41: `with` keyword — override data in-policy
// ---------------------------------------------------------------------------
#[test]
fn pe_41_walk_simulation() {
    // Use object.keys to iterate over unknown nested object.
    // This tests how builtins that take object args interact with unknowns.
    let policy = r#"
package test

default allow = false

allow if {
    input.metadata.labels.env == "production"
    input.metadata.labels.team == "platform"
}
"#;
    // Provide partial metadata
    let input = r#"{"metadata": {"labels": {"env": "production"}}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");
    eprintln!("pe_41: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(queries.len(), 1);
    // Only team should be unknown
    let conditions = queries[0].as_array().unwrap();
    assert_eq!(
        conditions.len(),
        1,
        "only the unknown field (team) should produce an assumption, got: {}",
        serde_json::to_string_pretty(&queries[0]).unwrap()
    );
}

// ===========================================================================
// Cases 42–60: PE definitiveness — suppress residuals when result is determined
// ===========================================================================

/// Case 42: Jamie's bug — one disjunct resolves concretely, the other has assumptions.
/// The result is definitive; residuals should be empty.
#[test]
fn pe_42_definitive_one_branch_concrete() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { input.resource.is_public == true }
"#;
    let input = r#"{"resource": {"is_public": true}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");
    eprintln!("pe_42: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "result is definitive (second def concrete) — no residuals expected, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 43: All definitions have unknowns — residuals should be returned.
#[test]
fn pe_43_definitive_all_unknown() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { input.resource.is_public == true }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_43: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        2,
        "both defs have unknowns — 2 disjuncts expected, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 44: Concrete definition comes first (order shouldn't matter).
#[test]
fn pe_44_definitive_concrete_first_def() {
    let policy = r#"
package test
default allow = false
allow if { input.resource.is_public == true }
allow if { input.user.role == "admin" }
"#;
    let input = r#"{"resource": {"is_public": true}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");
    eprintln!("pe_44: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "first def concrete — result definitive, no residuals expected"
    );
}

/// Case 45: Three definitions, one is always-true (no unknowns at all).
#[test]
fn pe_45_definitive_three_defs_one_always_true() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { input.user.department == "legal" }
allow if { true }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_45: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "third def is always true — result definitive"
    );
}

/// Case 46: Default + unknowns only — no definition succeeds concretely.
#[test]
fn pe_46_definitive_default_false_all_unknown() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { input.user.department == "legal" }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_46: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        queries.len() >= 2,
        "no concrete def — residuals expected, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 47: Helper rule has assumptions, but another definition of `allow`
/// succeeds concretely → result is definitive.
#[test]
fn pe_47_definitive_helper_rule_concrete() {
    let policy = r#"
package test
default allow = false
allow if { is_admin }
allow if { input.resource.is_public == true }
is_admin if { input.user.role == "admin" }
"#;
    let input = r#"{"resource": {"is_public": true}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");
    eprintln!("pe_47: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "second def concrete — result definitive despite helper assumptions"
    );
}

/// Case 48: Single definition calls helper with unknowns — not definitive.
#[test]
fn pe_48_definitive_helper_transitive() {
    let policy = r#"
package test
default allow = false
allow if { is_privileged }
is_privileged if { input.user.role == "admin" }
is_privileged if { input.user.role == "superuser" }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_48: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "helper has unknowns — residuals expected, got: {}",
        serde_json::to_string_pretty(&result).unwrap()
    );
}

/// Case 49: One def concrete + one def uses negation with unknown.
#[test]
fn pe_49_definitive_with_negation_concrete() {
    let policy = r#"
package test
default allow = false
allow if { input.resource.is_public == true }
allow if { not input.user.blocked }
"#;
    let input = r#"{"resource": {"is_public": true}}"#;
    let result = run_pe(policy, Some(input), None, "data.test.allow");
    eprintln!("pe_49: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "first def concrete — definitive despite negation assumption in second"
    );
}

/// Case 50: Both defs have unknowns (including negation) — not definitive.
#[test]
fn pe_50_definitive_negation_no_concrete() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { not input.user.blocked }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_50: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(queries.len() >= 2, "no concrete def — residuals expected");
}

/// Case 51: Partial set — one def concrete, one depends on unknown.
/// When input is fully unknown, both defs resolve (unknown becomes undefined),
/// so result is definitive.
#[test]
fn pe_51_definitive_partial_set_mixed() {
    let policy = r#"
package test
allowed contains x if { x := "read" }
allowed contains x if { x := input.extra_perm }
"#;
    let result = run_pe(policy, None, None, "data.test.allowed");
    eprintln!("pe_51: {}", serde_json::to_string_pretty(&result).unwrap());

    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "both defs resolve concretely — no residuals"
    );
}

/// Case 52: Partial set — all definitions concrete.
#[test]
fn pe_52_definitive_partial_set_all_concrete() {
    let policy = r#"
package test
allowed contains x if { x := "read" }
allowed contains x if { x := "write" }
"#;
    let result = run_pe(policy, None, None, "data.test.allowed");
    eprintln!("pe_52: {}", serde_json::to_string_pretty(&result).unwrap());

    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "all defs concrete — no additional values possible"
    );
}

/// Case 53: Partial object — one def concrete, one depends on unknown.
/// When input is fully unknown, both defs resolve concretely.
#[test]
fn pe_53_definitive_partial_object_mixed() {
    let policy = r#"
package test
perms[key] := val if {
    key := "read"
    val := true
}
perms[key] := val if {
    key := input.extra_key
    val := true
}
"#;
    let result = run_pe(policy, None, None, "data.test.perms");
    eprintln!("pe_53: {}", serde_json::to_string_pretty(&result).unwrap());

    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "both defs resolve concretely — no residuals"
    );
}

/// Case 54: Partial object — all definitions concrete.
#[test]
fn pe_54_definitive_partial_object_all_concrete() {
    let policy = r#"
package test
perms[key] := val if {
    key := "read"
    val := true
}
perms[key] := val if {
    key := "write"
    val := false
}
"#;
    let result = run_pe(policy, None, None, "data.test.perms");
    eprintln!("pe_54: {}", serde_json::to_string_pretty(&result).unwrap());

    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(queries.len(), 0, "all defs concrete — no residuals");
}

/// Case 55: Loop with unknown + always-true second def → definitive.
#[test]
fn pe_55_definitive_loop_then_concrete() {
    let policy = r#"
package test
default allow = false
allow if {
    some role in data.roles
    role == input.user.role
}
allow if { true }
"#;
    let data = r#"{"roles": ["admin", "editor"]}"#;
    let result = run_pe(policy, None, Some(data), "data.test.allow");
    eprintln!("pe_55: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "second def always-true — result definitive"
    );
}

/// Case 56: Comprehension with known data (concrete) + unknown override → definitive.
#[test]
fn pe_56_definitive_comprehension_concrete() {
    let policy = r#"
package test
default allow = false
allow if {
    count([x | some x in data.items; x > 0]) > 0
}
allow if { input.override == true }
"#;
    let data = r#"{"items": [1, 2, 3]}"#;
    let result = run_pe(policy, None, Some(data), "data.test.allow");
    eprintln!("pe_56: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "first def concrete via comprehension — result definitive"
    );
}

/// Case 57: Else chain (unknown primary) + always-true second def → definitive.
#[test]
fn pe_57_definitive_else_plus_concrete_def() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" } else := false if { true }
allow if { true }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_57: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "second definition always-true — result definitive"
    );
}

/// Case 58: Inconsistent values from two definitions — should not crash.
#[test]
fn pe_58_definitive_inconsistent_no_crash() {
    let policy = r#"
package test
level := "high" if { input.x == 1 }
level := "low" if { true }
"#;
    let result = run_pe(policy, None, None, "data.test.level");
    eprintln!("pe_58: {}", serde_json::to_string_pretty(&result).unwrap());
    // Just verify it doesn't crash — the exact behavior with inconsistency is
    // implementation-defined. The key is no panic.
}

/// Case 59: Function call — inner function has unknown + concrete defs.
/// Inner assumptions still count in the outer scope (conservative).
#[test]
fn pe_59_definitive_function_transitive() {
    let policy = r#"
package test
default allow = false
allow if { check("admin") }
check(role) if { role == input.user.role }
check(role) if { role == "admin" }
"#;
    let result = run_pe(policy, None, None, "data.test.allow");
    eprintln!("pe_59: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert!(
        !queries.is_empty(),
        "inner function assumptions count in outer scope — residuals expected"
    );
}

/// Case 60: Selective unknowns — only `input.user` is unknown; resource is known.
#[test]
fn pe_60_definitive_selective_unknowns() {
    let policy = r#"
package test
default allow = false
allow if { input.user.role == "admin" }
allow if { input.resource.public == true }
"#;
    let input = r#"{"resource": {"public": true}}"#;
    let result = run_pe_with_unknowns(
        policy,
        Some(input),
        None,
        "data.test.allow",
        Some(vec!["input.user".into()]),
    );
    eprintln!("pe_60: {}", serde_json::to_string_pretty(&result).unwrap());

    assert_eq!(result["result"], true);
    let queries = result["residual_queries"].as_array().unwrap();
    assert_eq!(
        queries.len(),
        0,
        "second def uses known input.resource — result definitive"
    );
}
