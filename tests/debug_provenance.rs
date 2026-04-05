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
