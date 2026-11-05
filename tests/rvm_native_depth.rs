// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Rc, Value};
use serde::Deserialize;

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

fn check_lifecycle(case: &Scenario, step_mode: bool) {
    eprintln!("lifecycle: {}, step={step_mode}", case.note);
    let mut engine = Engine::new();
    for (index, module) in case.modules.iter().enumerate() {
        engine
            .add_policy(format!("native-depth-{index}.rego"), module.clone())
            .unwrap();
    }
    let policy = engine
        .compile_with_entrypoint(&Rc::from(case.query.as_str()))
        .unwrap();
    let program =
        Compiler::compile_from_policy(&policy, &[&case.query, "data.probe.safe"]).unwrap();
    let mut vm = RegoVM::new();
    vm.load_program(program);
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

#[test]
fn native_depth_lifecycle() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess("native_depth_lifecycle");
        return;
    }
    let scenarios: Scenarios =
        yaml_serde::from_str(include_str!("rvm/rego/cases/native_depth.yaml")).unwrap();
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
