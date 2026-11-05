// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Rc, Value};
use serde::Deserialize;
use std::sync::Arc;

mod native_depth_support;

#[derive(Deserialize)]
struct Scenarios {
    cases: Vec<Scenario>,
}

#[derive(Deserialize)]
struct Scenario {
    note: String,
    modules: Vec<String>,
    query: String,
    input: Option<Value>,
    execution_mode: Option<String>,
    want_error: Option<String>,
    want_result: Option<Value>,
}

fn compile_case(case: &Scenario) -> Arc<Program> {
    let mut engine = Engine::new();
    for (index, module) in case.modules.iter().enumerate() {
        engine
            .add_policy(format!("native-depth-{index}.rego"), module.clone())
            .unwrap();
    }
    let policy = engine
        .compile_with_entrypoint(&Rc::from(case.query.as_str()))
        .unwrap();
    Compiler::compile_from_policy(&policy, &[&case.query, "data.probe.safe"]).unwrap()
}

fn check_lifecycle(case: &Scenario, step_mode: bool) {
    eprintln!("lifecycle: {}, step={step_mode}", case.note);
    let mut vm = RegoVM::new();
    vm.load_program(compile_case(case));
    vm.set_execution_mode(match case.execution_mode.as_deref() {
        None => ExecutionMode::RunToCompletion,
        Some("suspendable") => ExecutionMode::Suspendable,
        other => panic!("unsupported execution mode: {other:?}"),
    });
    vm.set_input(case.input.clone().unwrap_or(Value::Null));
    for _ in 0..if case.want_error.is_some() { 2 } else { 1 } {
        vm.set_step_mode(step_mode);
        let mut result = vm.execute_entry_point_by_name(&case.query);
        if step_mode {
            let mut resumed_active_rule = false;
            for _ in 0..10_000 {
                if !matches!(vm.execution_state(), ExecutionState::Suspended { .. }) {
                    break;
                }
                resumed_active_rule |= !vm.get_call_stack().is_empty();
                result = vm.resume(None);
            }
            assert!(resumed_active_rule, "must resume inside an active rule");
        }
        if case.want_error.is_some() {
            assert!(
                matches!(
                    result,
                    Err(VmError::RuleCallDepthExceeded { limit: 16, .. })
                ),
                "{result:?}"
            );
            assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
        } else {
            assert_eq!(Some(result.unwrap()), case.want_result);
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Completed { .. }
            ));
        }
        assert!(vm.get_call_stack().is_empty());
        vm.set_step_mode(false);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
            Value::from(7)
        );
    }
}

fn check_configuration(scenarios: &Scenarios) {
    let case = scenarios
        .cases
        .iter()
        .find(|case| case.note == "native-depth/rules-17-error-not-default")
        .unwrap();
    let program = compile_case(case);
    let mut configured = RegoVM::new();
    let mut default = RegoVM::new();
    assert_eq!(configured.max_native_rule_call_depth(), 16);
    configured.set_max_native_rule_call_depth(17);
    for _ in 0..2 {
        configured.load_program(program.clone());
        assert_eq!(configured.max_native_rule_call_depth(), 17);
        assert_eq!(
            configured.execute_entry_point_by_name(&case.query).unwrap(),
            Value::from(42)
        );
        assert_eq!(configured.max_native_rule_call_depth(), 17);
        assert_eq!(
            configured
                .execute_entry_point_by_name("data.probe.safe")
                .unwrap(),
            Value::from(7)
        );
        assert_eq!(configured.max_native_rule_call_depth(), 17);
        default.load_program(program.clone());
        assert_eq!(default.max_native_rule_call_depth(), 16);
        assert!(matches!(
            default.execute_entry_point_by_name(&case.query),
            Err(VmError::RuleCallDepthExceeded { limit: 16, .. })
        ));
    }

    configured.set_max_native_rule_call_depth(1);
    assert!(matches!(
        configured.execute_entry_point_by_name(&case.query),
        Err(VmError::RuleCallDepthExceeded { limit: 1, .. })
    ));
    assert_eq!(
        configured
            .execute_entry_point_by_name("data.probe.safe")
            .unwrap(),
        Value::from(7)
    );
    configured.set_max_native_rule_call_depth(0);
    assert!(matches!(
        configured.execute_entry_point_by_name("data.probe.safe"),
        Err(VmError::RuleCallDepthExceeded { limit: 0, .. })
    ));
    configured.set_execution_mode(ExecutionMode::Suspendable);
    assert_eq!(
        configured.execute_entry_point_by_name(&case.query).unwrap(),
        Value::from(42)
    );

    let case = scenarios
        .cases
        .iter()
        .find(|case| case.note == "native-depth/virtual-leaf-suspendable-16-succeed")
        .unwrap();
    configured.load_program(compile_case(case));
    configured.set_input(case.input.clone().unwrap());
    configured.set_max_native_rule_call_depth(16);
    configured.set_step_mode(true);
    configured.execute_entry_point_by_name(&case.query).unwrap();
    configured.set_max_native_rule_call_depth(0);
    let mut result = Ok(Value::Undefined);
    for _ in 0..10_000 {
        if !matches!(
            configured.execution_state(),
            ExecutionState::Suspended { .. }
        ) {
            break;
        }
        result = configured.resume(None);
    }
    assert!(matches!(
        result,
        Err(VmError::RuleCallDepthExceeded { limit: 0, .. })
    ));
    assert!(matches!(
        configured.execution_state(),
        ExecutionState::Error { .. }
    ));
    assert!(configured.get_call_stack().is_empty());
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn native_depth_lifecycle() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess("native_depth_lifecycle");
        return;
    }
    let scenarios: Scenarios =
        yaml_serde::from_str(include_str!("rvm/rego/cases/native_depth.yaml")).unwrap();
    check_configuration(&scenarios);
    for case in &scenarios.cases {
        if case.want_error.is_some() {
            check_lifecycle(case, false);
        }
        if case.execution_mode.as_deref() == Some("suspendable")
            && (case.want_error.is_some() || case.note.contains("virtual-"))
        {
            check_lifecycle(case, true);
        }
    }
}
