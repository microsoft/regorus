// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Rc, Value};

// YAML scenarios cover policy results; this checks reuse of the same VM after
// a conflict, including one reached after a host-await suspension.
#[test]
fn conflicts_allow_fresh_execution_but_not_resume() -> anyhow::Result<()> {
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for expression in ["q", "{\"k\": x | some x in input.values}"] {
            for await_response in [false, true] {
                let condition = if await_response {
                    "__builtin_host_await(\"ready\", \"gate\")"
                } else {
                    "true"
                };
                let mut engine = Engine::new();
                engine.add_policy(
                    "conflict.rego".into(),
                    format!(
                        "package test\nq := x if some x in input.values\n\
                         p := {expression} if {condition}"
                    ),
                )?;
                let policy = engine.compile_with_entrypoint(&Rc::from("data.test.p"))?;
                let program = Compiler::compile_from_policy(&policy, &["data.test.p"])?;
                let mut vm = RegoVM::new();
                vm.load_program(program);
                vm.set_execution_mode(mode);

                for (input, conflicting) in [("[1,2]", true), ("[1,1]", false)] {
                    vm.set_input(Value::from_json_str(&format!("{{\"values\":{input}}}"))?);
                    if await_response && mode == ExecutionMode::RunToCompletion {
                        vm.set_host_await_responses([(
                            Value::from("gate"),
                            vec![Value::Bool(true)],
                        )]);
                    }
                    let mut result = vm.execute_entry_point_by_name("data.test.p");
                    if await_response && mode == ExecutionMode::Suspendable {
                        assert_eq!(result?, Value::Undefined);
                        assert!(matches!(
                            vm.execution_state(),
                            ExecutionState::Suspended { .. }
                        ));
                        result = vm.resume(Some(Value::Bool(true)));
                    }
                    if conflicting {
                        assert!(matches!(result, Err(VmError::EvaluationConflict { .. })));
                        assert!(matches!(
                            vm.execution_state(),
                            ExecutionState::Error {
                                error: VmError::EvaluationConflict { .. }
                            }
                        ));
                        if mode == ExecutionMode::Suspendable {
                            assert!(matches!(
                                vm.resume(Some(Value::Bool(true))),
                                Err(VmError::InvalidResumeState { .. })
                            ));
                        }
                    } else {
                        let expected = if expression == "q" {
                            Value::from(1)
                        } else {
                            Value::from_json_str(r#"{"k":1}"#)?
                        };
                        assert_eq!(result?, expected);
                    }
                }
            }
        }
    }
    Ok(())
}
