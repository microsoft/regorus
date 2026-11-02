// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::rvm::Instruction;
use regorus::{Engine, Rc, Value};

fn evaluate(module: &str, strict: bool, mode: ExecutionMode) -> anyhow::Result<Value> {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(strict);
    engine.add_policy("conflict.rego".into(), format!("package test\n{module}"))?;
    let policy = engine.compile_with_entrypoint(&Rc::from("data.test.p"))?;
    let program = Compiler::compile_from_policy(&policy, &["data.test.p"])?;
    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let bytes = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let DeserializationResult::Complete(program) =
        Program::deserialize_binary(&bytes).map_err(anyhow::Error::msg)?
    else {
        anyhow::bail!("program round trip failed");
    };
    let mut vm = RegoVM::new();
    vm.load_program(std::sync::Arc::new(program));
    vm.set_strict_builtin_errors(strict);
    vm.set_execution_mode(mode);
    Ok(vm.execute_entry_point_by_name("data.test.p")?)
}

fn interpret(module: &str, strict: bool) -> anyhow::Result<Value> {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(strict);
    engine.add_policy("conflict.rego".into(), format!("package test\n{module}"))?;
    engine.eval_rule("data.test.p".into())
}

#[test]
fn evaluation_conflicts_propagate_in_both_modes() {
    let policies = [
        "p := 1\np := 2",
        "q := 1\nq := 2\np if not q",
        "default p := 42\np := 1\np := 2",
        "q := 1\nq := 2\np := q",
        "q := 1\nq := 2\np := 1 if q else := 2",
        "f(x) := 1\nf(x) := 2\np := f(0)",
        "p := x if some x in [1, 2]",
        "f(a) := x if some x in [1, 2]\np := f(0)",
        "p := {\"k\": x | some x in [1, 2]}",
        "p[k] := x if { k := \"k\"; some x in [1, 2] }",
        "p[k] := 1 if k := \"k\"\np[k] := 2 if k := \"k\"",
        "q := 1\nq := 2\np := [q | true]",
        "q := {\"k\": x | some x in [1, 2]}\np if not q",
    ];
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            for policy in policies {
                let error = evaluate(policy, strict, mode).unwrap_err();
                assert!(
                    matches!(
                        error.downcast_ref::<VmError>(),
                        Some(VmError::EvaluationConflict { .. })
                    ),
                    "{policy}: {error} (strict={strict}, mode={mode:?})"
                );
                assert!(interpret(policy, strict).is_err(), "{policy}");
            }
        }
    }
}

#[test]
fn equal_outputs_and_ordinary_undefined_remain_valid() {
    let policies = [
        ("p := 1\np := 1", Value::from(1)),
        ("p := x if some x in [1, 1]", Value::from(1)),
        ("f(x) := 1\nf(x) := 1\np := f(0)", Value::from(1)),
        ("f(a) := x if some x in [1, 1]\np := f(0)", Value::from(1)),
        (
            "p := {\"k\": x | some x in [1, 1]}",
            Value::from_json_str(r#"{"k":1}"#).unwrap(),
        ),
        (
            "p[k] := 1 if k := \"k\"\np[k] := 1 if k := \"k\"",
            Value::from_json_str(r#"{"k":1}"#).unwrap(),
        ),
        ("p := 1 if false", Value::Undefined),
        ("default p := 42\np := 1 if false", Value::from(42)),
        ("f(x) := x\np if not f(input.missing)", Value::Bool(true)),
        ("p := x if { some x in [1, 2]; x == 2 }", Value::from(2)),
    ];
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            for (policy, expected) in &policies {
                assert_eq!(
                    evaluate(policy, strict, mode).unwrap_or_else(|error| panic!(
                        "{policy} (strict={strict}, mode={mode:?}): {error}"
                    )),
                    *expected,
                    "{policy} (strict={strict}, mode={mode:?})"
                );
                assert_eq!(
                    interpret(policy, strict).unwrap(),
                    *expected,
                    "interpreter: {policy} (strict={strict})"
                );
            }
        }
    }
}

#[test]
fn missing_candidates_cannot_hide_conflicts() {
    let conflicting = [
        "p := x.k if some x in [{\"k\":1}, {}, {\"k\":2}]",
        "p[k] := x.k if { k := \"k\"; some x in [{\"k\":1}, {}, {\"k\":2}] }",
        "p := {\"k\":x.k | some x in [{\"k\":1}, {}, {\"k\":2}]}",
    ];
    let controls = [
        ("p := x.k if some x in [{\"k\":1}, {}]", Value::from(1)),
        ("p := x.k if some x in [{}, {\"k\":1}]", Value::from(1)),
        (
            "p[k] := x.k if { k := \"k\"; some x in [{\"k\":1}, {}] }",
            Value::from_json_str(r#"{"k":1}"#).unwrap(),
        ),
        (
            "p := {\"k\":x.k | some x in [{\"k\":1}, {}]}",
            Value::from_json_str(r#"{"k":1}"#).unwrap(),
        ),
        (
            "p := {\"k\":x.missing | true} if some x in [{}]",
            Value::new_object(),
        ),
        (
            "p := {x.missing:1 | true} if some x in [{}]",
            Value::new_object(),
        ),
        (
            "p := {x.missing | true} if some x in [{}]",
            Value::new_set(),
        ),
        (
            "p := {\"k\":x.k | some x in [{\"k\":false}, {}]}",
            Value::from_json_str(r#"{"k":false}"#).unwrap(),
        ),
    ];
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            for policy in conflicting {
                let error = evaluate(policy, strict, mode).unwrap_err();
                assert!(
                    matches!(
                        error.downcast_ref::<VmError>(),
                        Some(VmError::EvaluationConflict { .. })
                    ),
                    "{policy}: {error} (strict={strict}, mode={mode:?})"
                );
            }
            for (policy, expected) in &controls {
                assert_eq!(
                    evaluate(policy, strict, mode).unwrap(),
                    *expected,
                    "{policy} (strict={strict}, mode={mode:?})"
                );
            }
        }
    }
}

#[test]
fn failed_evaluations_release_state_and_allow_reexecution() -> anyhow::Result<()> {
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for expression in [
            "q",
            "{\"k\": x | some x in input.values}",
            "to_number(input.number)",
        ] {
            let module =
                format!("package test\nq := x if some x in input.values\np := {expression}");
            let mut engine = Engine::new();
            engine.set_strict_builtin_errors(true);
            engine.add_policy("reexecute.rego".into(), module)?;
            let policy = engine.compile_with_entrypoint(&Rc::from("data.test.p"))?;
            let program = Compiler::compile_from_policy(&policy, &["data.test.p"])?;
            let mut vm = RegoVM::new();
            vm.load_program(program);
            vm.set_strict_builtin_errors(true);
            vm.set_execution_mode(mode);
            vm.set_input(Value::from_json_str(
                r#"{"values":[1,2],"number":"invalid"}"#,
            )?);
            assert!(vm.execute_entry_point_by_name("data.test.p").is_err());
            assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
            assert!(vm.get_registers().is_empty(), "{expression} {mode:?}");
            vm.set_input(Value::from_json_str(r#"{"values":[1,1],"number":"1"}"#)?);
            let expected = if expression.starts_with('{') {
                Value::from_json_str(r#"{"k":1}"#)?
            } else {
                Value::from(1)
            };
            assert_eq!(vm.execute_entry_point_by_name("data.test.p")?, expected);
        }
    }
    Ok(())
}

#[test]
fn noncollection_iteration_preserves_existing_vm_behavior() {
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            assert_eq!(
                evaluate("p := x if some x in 1", strict, mode).unwrap(),
                Value::Undefined
            );
            assert_eq!(
                evaluate("p := [x | some x in 1]", strict, mode).unwrap(),
                Value::new_array()
            );
        }
    }
}

#[test]
fn check_conflict_validates_register_operands() {
    let mut program = Program::new();
    program.dispatch_window_size = 1;
    program.max_rule_window_size = 1;
    program.add_instruction(Instruction::CheckConflict { left: 0, right: 3 }, None);
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(std::sync::Arc::new(program.clone()));
        vm.set_execution_mode(mode);
        assert!(matches!(
            vm.execute(),
            Err(VmError::RegisterIndexOutOfBounds { index: 3, .. })
        ));
    }
}

#[test]
fn operator_type_errors_respect_strictness_at_source() {
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for expression in ["1 + \"x\"", "1 - false", "true * 2", "null / 2", "1.5 % 2"] {
            let policy = format!("q := {expression}\np if not q");
            assert!(evaluate(&policy, true, mode).is_err(), "{policy} {mode:?}");
            assert_eq!(
                evaluate(&policy, false, mode).unwrap(),
                Value::Bool(true),
                "{policy} {mode:?}"
            );
        }
    }
}

#[test]
fn strict_errors_do_not_reject_valid_rego_ordering() {
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            for policy in [
                "p := x < \"x\" if some x in [1]",
                "p := x <= \"x\" if some x in [1]",
                "p := \"x\" > x if some x in [1]",
                "p := \"x\" >= x if some x in [1]",
            ] {
                assert_eq!(evaluate(policy, strict, mode).unwrap(), Value::Bool(true));
                assert_eq!(interpret(policy, strict).unwrap(), Value::Bool(true));
            }
            assert_eq!(
                evaluate("default p := false\np if \"x\" < 1", strict, mode).unwrap(),
                Value::Bool(false)
            );
        }
    }
}

#[cfg(feature = "azure_policy")]
#[test]
fn rego_error_normalization_preserves_azure_arithmetic_errors() -> anyhow::Result<()> {
    use regorus::languages::azure_policy::{compiler, parser};
    use regorus::Source;

    for operation in ["add", "sub", "mul"] {
        let text = format!(
            r#"{{"if":{{"value":"[{operation}('x',1)]","equals":2}},"then":{{"effect":"deny"}}}}"#
        );
        let source = Source::from_contents("arithmetic.json".into(), text)?;
        let rule =
            parser::parse_policy_rule(&source).map_err(|error| anyhow::anyhow!("{error:?}"))?;
        let program = compiler::compile_policy_rule(&rule)?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for strict in [false, true] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                vm.set_strict_builtin_errors(strict);
                let error = vm.execute().unwrap_err();
                assert!(
                    matches!(
                        (operation, &error),
                        ("add", VmError::InvalidAddition { .. })
                            | ("sub", VmError::InvalidSubtraction { .. })
                            | ("mul", VmError::InvalidMultiplication { .. })
                    ),
                    "{operation}: {error} (strict={strict}, mode={mode:?})"
                );
            }
        }
    }
    Ok(())
}

#[test]
fn strict_builtin_errors_are_not_rule_failures() {
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for policy in [
            "p := to_number(\"invalid\")",
            "q := to_number(\"invalid\")\np if not q",
            "default p := 42\np := to_number(\"invalid\")",
            "p := [to_number(\"invalid\") | true]",
        ] {
            assert!(evaluate(policy, true, mode).is_err(), "{policy} {mode:?}");
        }
        assert_eq!(
            evaluate("q := to_number(\"invalid\")\np if not q", false, mode).unwrap(),
            Value::Bool(true)
        );
        assert_eq!(
            evaluate("default p := 42\np := to_number(\"invalid\")", false, mode).unwrap(),
            Value::from(42)
        );
    }
}
