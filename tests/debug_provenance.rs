#![cfg(all(feature = "rvm", feature = "explanations"))]

#[test]
fn causality_report_with_assume_unknown_input() {
    use regorus::*;

    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            r#"
package test
default allow = false
allow if { input.role == "admin" }
"#
            .into(),
        )
        .unwrap();

    let entrypoint: Rc<str> = "data.test.allow".into();
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
    });
    vm.set_input(Value::new_object());

    let value = vm.execute_entry_point_by_name("data.test.allow").unwrap();
    assert_eq!(value, Value::Bool(true));

    let report_json = vm.take_causality_report(value).unwrap();
    let report: serde_json::Value = serde_json::from_str(&report_json).unwrap();

    // Verify query_result
    assert_eq!(report["query_result"], true);

    // Verify rules are populated
    let rules = report["rules"].as_array().unwrap();
    assert!(!rules.is_empty(), "rules should not be empty");
    assert_eq!(rules[0]["name"], "data.test.allow");
    assert_eq!(rules[0]["result"], true);

    // Verify assumptions are populated
    let assumptions = report["assumptions"].as_array().unwrap();
    assert!(!assumptions.is_empty(), "assumptions should not be empty");
    assert_eq!(assumptions[0]["input_path"], "input.role");
    assert_eq!(assumptions[0]["operator"], "==");
    assert_eq!(assumptions[0]["assumed_value"], "admin");
}

#[test]
fn assumptions_follow_local_aliases() {
    use regorus::*;

    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            r#"
package test
default allow = false

role := input.identity.role
expected_role := "release-admin"

allow if {
    er := expected_role
    role == er
}
"#
            .into(),
        )
        .unwrap();

    let entrypoint: Rc<str> = "data.test.allow".into();
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
    });
    vm.set_input(serde_json::from_str(r#"{"identity": {"name": "alex"}}"#).unwrap());

    let value = vm.execute_entry_point_by_name("data.test.allow").unwrap();
    assert_eq!(value, Value::Bool(true));

    let report_json = vm.take_causality_report(value).unwrap();
    let report: serde_json::Value = serde_json::from_str(&report_json).unwrap();

    let assumptions = report["assumptions"].as_array().unwrap();
    assert!(!assumptions.is_empty(), "assumptions should not be empty");
    assert_eq!(assumptions[0]["input_path"], "input.identity.role");
    assert_eq!(assumptions[0]["operator"], "==");
    assert_eq!(assumptions[0]["assumed_value"], "release-admin");

    let rules = report["rules"].as_array().unwrap();
    let allow_rule = rules
        .iter()
        .find(|rule| rule["name"] == "data.test.allow")
        .unwrap();
    // Find the comparison condition (not the binding condition)
    let conditions = allow_rule["definitions"][0]["conditions"]
        .as_array()
        .unwrap();
    let comparison_cond = conditions
        .iter()
        .find(|c| c["kind"] == "comparison")
        .expect("should have a comparison condition");
    let left = &comparison_cond["left"];
    assert_eq!(left["provenance"], "input.identity.role");
}

#[test]
fn assumptions_follow_function_argument_aliases() {
    use regorus::*;

    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            r#"
package test
default allow = false

normalize_role(role) := normalized if {
    normalized := role
}

allow if {
    role := normalize_role(input.identity.role)
    role == "release-admin"
}
"#
            .into(),
        )
        .unwrap();

    let entrypoint: Rc<str> = "data.test.allow".into();
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
    });
    vm.set_input(Value::new_object());

    let value = vm.execute_entry_point_by_name("data.test.allow").unwrap();
    assert_eq!(value, Value::Bool(true));

    let report_json = vm.take_causality_report(value).unwrap();
    let report: serde_json::Value = serde_json::from_str(&report_json).unwrap();

    let assumptions = report["assumptions"].as_array().unwrap();
    assert!(!assumptions.is_empty(), "assumptions should not be empty");
    assert_eq!(assumptions[0]["kind"], "exists");
    assert_eq!(assumptions[0]["input_path"], "input.identity");
    assert!(assumptions[0]["operator"].is_null());
    assert!(assumptions[0]["assumed_value"].is_null());
}

#[test]
fn causality_report_includes_loop_witness() {
    use regorus::*;

    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            r#"
package test
default allow = false

allow if {
    n := input.values[_]
    n > 1
    n < 3
}
"#
            .into(),
        )
        .unwrap();

    let entrypoint: Rc<str> = "data.test.allow".into();
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
        detail: evaluation_trace::ExplanationDetail::Standard,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: false,
    });

    let mut input_obj = Value::new_object();
    let values = Value::from_json_str("[0, 2, 4]").unwrap();
    input_obj
        .as_object_mut()
        .unwrap()
        .insert("values".into(), values);
    vm.set_input(input_obj);

    let value = vm.execute_entry_point_by_name("data.test.allow").unwrap();
    assert_eq!(value, Value::Bool(true));

    let report_json = vm.take_causality_report(value).unwrap();
    let report: serde_json::Value = serde_json::from_str(&report_json).unwrap();

    // The report should contain rules with conditions that have loop witness data
    let rules = report["rules"].as_array().expect("rules should be present");
    assert!(!rules.is_empty(), "rules should not be empty");

    // Find a condition with a witness in any definition's conditions
    let mut found_witness = false;
    for rule in rules {
        if let Some(definitions) = rule["definitions"].as_array() {
            for def in definitions {
                if let Some(conditions) = def["conditions"].as_array() {
                    for cond in conditions {
                        if !cond["witness"].is_null() {
                            found_witness = true;
                            let witness = &cond["witness"];
                            // Verify witness structure has the expected fields
                            assert!(
                                witness["total_iterations"].is_number(),
                                "witness should have total_iterations, got: {witness}"
                            );
                            assert!(
                                witness["success_count"].is_number(),
                                "witness should have success_count, got: {witness}"
                            );
                            // With input [0, 2, 4], the loop iterates 3 times,
                            // and value 2 passes both n > 1 and n < 3.
                            let total = witness["total_iterations"].as_u64().unwrap();
                            assert!(total > 0, "total_iterations should be > 0, got {total}");
                        }
                    }
                }
            }
        }
    }

    assert!(found_witness, "expected at least one condition with a loop witness in the report.\nFull report:\n{report_json}");
}

#[test]
fn causality_report_array_iteration_has_concrete_index() {
    use regorus::*;

    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            r#"
package test
default allow = false

allow if {
    container := input.containers[_]
    container.privileged == true
}
"#
            .into(),
        )
        .unwrap();

    let entrypoint: Rc<str> = "data.test.allow".into();
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
        detail: evaluation_trace::ExplanationDetail::Standard,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: false,
    });

    let input_json = r#"{"containers": [{"name": "safe", "privileged": false}, {"name": "evil", "privileged": true}]}"#;
    vm.set_input(Value::from_json_str(input_json).unwrap());

    let value = vm.execute_entry_point_by_name("data.test.allow").unwrap();
    assert_eq!(value, Value::Bool(true));

    let report_json = vm.take_causality_report(value).unwrap();

    // The provenance paths should contain concrete indices like input.containers[1],
    // NOT wildcard paths like input.containers[_].
    // Note: source text like "container := input.containers[_]" naturally contains [_];
    // we only assert that provenance paths (in "provenance" fields) use concrete indices.
    assert!(
        report_json.contains("input.containers[1]"),
        "expected concrete index input.containers[1] in provenance paths.\nReport:\n{report_json}"
    );

    let report: serde_json::Value = serde_json::from_str(&report_json).unwrap();
    let conditions = report["rules"][0]["definitions"][0]["conditions"]
        .as_array()
        .unwrap();
    for cond in conditions {
        if let Some(prov) = cond["left"]["provenance"].as_str() {
            assert!(
                !prov.contains("[_]"),
                "provenance path should not have wildcard [_]: {prov}"
            );
        }
    }
}

#[test]
fn causality_report_includes_binding_names() {
    use regorus::*;

    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            r#"
package test
allow if {
    role := input.role
    role == "admin"
}
"#
            .into(),
        )
        .unwrap();

    let entrypoint: Rc<str> = "data.test.allow".into();
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
        detail: evaluation_trace::ExplanationDetail::Standard,
        emission_index: None,
        emission_value: None,
        assume_unknown_input: false,
    });

    let input_json = r#"{"role": "admin"}"#;
    vm.set_input(Value::from_json_str(input_json).unwrap());

    let value = vm.execute_entry_point_by_name("data.test.allow").unwrap();
    assert_eq!(value, Value::Bool(true));

    let report_json = vm.take_causality_report(value).unwrap();

    // The report should include the binding name "role"
    assert!(
        report_json.contains("\"binding_name\": \"role\""),
        "expected binding_name 'role' in causality report.\nReport:\n{report_json}"
    );
}

/// When `assume_unknown_input` is true but the input value IS provided and
/// simply doesn't match (e.g. "dev-rg" != "prod-rg"), the engine should NOT
/// assume the condition holds. Only truly missing/undefined input should be
/// assumed.
#[test]
fn no_assumption_when_input_present_but_mismatched() {
    use regorus::*;

    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            r#"
package test

deny contains msg if {
    input.deployment.resourceGroupName == "prod-rg"
    some resource in input.resources
    resource.type == "Microsoft.Storage/storageAccounts"
    resource.properties.allowBlobPublicAccess == true
    msg := sprintf("Storage account '%s' must not allow public blob access", [resource.name])
}
"#
            .into(),
        )
        .unwrap();

    let entrypoint: Rc<str> = "data.test.deny".into();
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
    });

    // Input provides resourceGroupName = "dev-rg", NOT "prod-rg".
    // The comparison should genuinely fail, not be assumed.
    let input_json = r#"{
        "deployment": { "resourceGroupName": "dev-rg" },
        "resources": [{
            "type": "Microsoft.Storage/storageAccounts",
            "name": "teststorage",
            "properties": { "allowBlobPublicAccess": true }
        }]
    }"#;
    vm.set_input(Value::from_json_str(input_json).unwrap());

    let value = vm.execute_entry_point_by_name("data.test.deny").unwrap();

    // deny should produce an empty set — the condition fails because
    // "dev-rg" != "prod-rg", not assumed away.
    let set = value.as_set().expect("deny should be a set");
    assert!(
        set.is_empty(),
        "deny should be empty when resourceGroupName is 'dev-rg', got: {value}"
    );

    let report_json = vm.take_causality_report(value).unwrap();
    let report: serde_json::Value = serde_json::from_str(&report_json).unwrap();

    // There should be NO assumptions about resourceGroupName since the value
    // was provided (just didn't match).
    let empty = vec![];
    let assumptions = report["assumptions"].as_array().unwrap_or(&empty);
    for assumption in assumptions {
        let path = assumption["input_path"].as_str().unwrap_or("");
        assert!(
            !path.contains("resourceGroupName"),
            "should not assume resourceGroupName when it is provided in input.\nAssumptions: {assumptions:?}"
        );
    }
}
