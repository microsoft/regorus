// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::rvm::Instruction;
use regorus::{Engine, Rc, Value};
use std::process::{Command, Stdio};
use std::sync::Arc;
use std::time::{Duration, Instant};

fn compile(source: &str, entries: &[&str]) -> anyhow::Result<Arc<Program>> {
    let mut engine = Engine::new();
    engine.add_policy("recursion.rego".into(), source.into())?;
    let policy = engine.compile_with_entrypoint(&Rc::from(entries[0]))?;
    Ok(Compiler::compile_from_policy(&policy, entries)?)
}

#[test]
fn source_cycles_are_rejected() {
    for source in [
        "package probe\nresult := result",
        "package probe\np := p\nresult := p",
        "package probe\np := q\nq := p\nresult := p",
        "package probe\nf(x) := g(x)\ng(x) := f(x)\nresult := f(1)",
        "package probe\nf(x) := f(x)\nresult := f(1)",
        "package probe\nresult := data.probe",
        "package probe\nresult := data.probe[`result`]",
        "package probe\nresult := data.probe[\"result\"]",
        "package probe\nresult := [p, q]\np := q\nq := p",
        "package probe\nresult := data.probe.nested\nnested.p := nested.q\nnested.q := nested.p",
    ] {
        let error = compile(source, &["data.probe.result"]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("Compile-time recursion detected"),
            "{source}: {error:#}"
        );
    }
}

#[test]
fn unused_cycles_do_not_reject_entrypoint() {
    compile(
        "package probe\np := p\nresult := 42",
        &["data.probe.result"],
    )
    .unwrap();
}

#[test]
fn package_materialization_excludes_uncalled_functions() {
    for function in ["f(x) := f(x)", "f(x) := data.app.result"] {
        let mut engine = Engine::new();
        engine
            .add_policy("app.rego".into(), "package app\nresult := data.lib".into())
            .unwrap();
        engine
            .add_policy(
                "lib.rego".into(),
                format!("package lib\nsafe := 42\n{function}"),
            )
            .unwrap();
        let policy = engine
            .compile_with_entrypoint(&Rc::from("data.app.result"))
            .unwrap();
        let program = Compiler::compile_from_policy(&policy, &["data.app.result"]).unwrap();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name("data.app.result").unwrap(),
                Value::from_json_str(r#"{"safe":42}"#).unwrap()
            );
        }
    }
}

fn run_runtime_cases() {
    // Mutate a valid program to exercise the VM independently of compiler rejection.
    for source in [
        "package probe\nresult := input.value\nsafe := 42",
        "package probe\nresult := p\np := input.value\nsafe := 42",
        "package probe\nresult := f(1)\nf(x) := x\nsafe := 42",
    ] {
        let base = compile(source, &["data.probe.result", "data.probe.safe"]).unwrap();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut program = (*base).clone();
            let target = program
                .rule_infos
                .iter()
                .find(|rule| rule.name == "data.probe.p" || rule.name == "data.probe.f")
                .unwrap_or(&program.rule_infos[0]);
            let body = target.definitions[0][0] as usize;
            program.instructions[body] = if target.function_info.is_some() {
                *program
                    .instructions
                    .iter()
                    .find(|instruction| matches!(instruction, Instruction::FunctionCall { .. }))
                    .unwrap()
            } else {
                Instruction::CallRule {
                    dest: 0,
                    rule_index: 0,
                }
            };
            let bytes = program.serialize_binary().unwrap();
            let program = match Program::deserialize_binary(&bytes).unwrap() {
                DeserializationResult::Complete(program) => Arc::new(program),
                other => panic!("unexpected deserialization: {other:?}"),
            };
            let mut vm = RegoVM::new();
            vm.set_execution_mode(mode);
            vm.load_program(program);
            for _ in 0..2 {
                let error = vm
                    .execute_entry_point_by_name("data.probe.result")
                    .unwrap_err();
                assert!(
                    matches!(error, VmError::RecursiveRuleEvaluation { .. }),
                    "{mode:?}: {error}"
                );
                assert!(vm.get_call_stack().is_empty());
                assert_eq!(
                    vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
                    Value::from(42)
                );
            }
            if mode == ExecutionMode::Suspendable {
                vm.set_step_mode(true);
                vm.execute_entry_point_by_name("data.probe.result").unwrap();
                let mut saw_active_call = false;
                let mut saw_recursion = false;
                for _ in 0..100 {
                    assert!(matches!(
                        vm.execution_state(),
                        ExecutionState::Suspended { .. }
                    ));
                    saw_active_call |= !vm.get_call_stack().is_empty();
                    match vm.resume(None) {
                        Ok(_) => {}
                        Err(error) => {
                            assert!(matches!(error, VmError::RecursiveRuleEvaluation { .. }));
                            assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
                            assert!(vm.get_call_stack().is_empty());
                            saw_recursion = true;
                            break;
                        }
                    }
                }
                assert!(saw_active_call, "test must resume inside an active rule");
                assert!(saw_recursion, "resumed execution must detect recursion");
                vm.set_step_mode(false);
                assert_eq!(
                    vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
                    Value::from(42)
                );
            }
        }
    }

    for (source, cyclic_input) in [
        (
            "package probe\nresult := data.probe[input.key]\nsafe := 42",
            r#"{"key":"result"}"#,
        ),
        (
            "package probe\nresult := data.probe[input.key]\nsafe := 42\nunused := unused",
            r#"{"key":"unused"}"#,
        ),
        (
            "package probe\nresult := data.probe[input.key]\nsafe := 42\nindirect := result",
            r#"{"key":"indirect"}"#,
        ),
        (
            "package probe\nresult := data.probe[input.key]\nsafe := 42\na := b\nb := a",
            r#"{"key":"a"}"#,
        ),
        (
            "package probe\ndefault result := false\nresult := data.probe[input.key]\nsafe := 42",
            r#"{"key":"result"}"#,
        ),
    ] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let program = compile(source, &["data.probe.result", "data.probe.safe"]).unwrap();
            let mut vm = RegoVM::new();
            vm.load_program(program);
            vm.set_execution_mode(mode);
            for _ in 0..2 {
                vm.set_input(Value::from_json_str(r#"{"key":"safe"}"#).unwrap());
                assert_eq!(
                    vm.execute_entry_point_by_name("data.probe.result").unwrap(),
                    Value::from(42)
                );
                vm.set_input(Value::from_json_str(cyclic_input).unwrap());
                assert!(matches!(
                    vm.execute_entry_point_by_name("data.probe.result"),
                    Err(VmError::RecursiveRuleEvaluation { .. })
                ));
                assert!(vm.get_call_stack().is_empty());
            }
            if mode == ExecutionMode::Suspendable {
                vm.set_step_mode(true);
                vm.execute_entry_point_by_name("data.probe.result").unwrap();
                let mut saw_recursion = false;
                for _ in 0..100 {
                    if let Err(error) = vm.resume(None) {
                        assert!(matches!(error, VmError::RecursiveRuleEvaluation { .. }));
                        assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
                        assert!(vm.get_call_stack().is_empty());
                        saw_recursion = true;
                        break;
                    }
                }
                assert!(saw_recursion, "dynamic recursion must survive step/resume");
                vm.set_step_mode(false);
                vm.set_input(Value::from_json_str(r#"{"key":"safe"}"#).unwrap());
                assert_eq!(
                    vm.execute_entry_point_by_name("data.probe.result").unwrap(),
                    Value::from(42)
                );
            }
        }
    }

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let program = compile(
            "package probe\nresult := data.probe[input.key]\na := b\nb := 42",
            &["data.probe.result"],
        )
        .unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(r#"{"key":"a"}"#).unwrap());
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.result").unwrap(),
            Value::from(42)
        );
    }

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let program = compile(
            "package probe\nf(x) := x + 1\nresult := [f(1), f(2)]",
            &["data.probe.result"],
        )
        .unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_execution_mode(mode);
        for _ in 0..2 {
            assert_eq!(
                vm.execute_entry_point_by_name("data.probe.result").unwrap(),
                Value::from_json_str("[2,3]").unwrap()
            );
        }
    }
}

#[test]
fn runtime_recursion_child() {
    if std::env::var_os("REGORUS_RECURSION_CHILD").is_some() {
        run_runtime_cases();
    }
}

#[test]
fn runtime_backstop_is_bounded() {
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "runtime_recursion_child", "--nocapture"])
        .env("REGORUS_RECURSION_CHILD", "1")
        .env("RUST_MIN_STACK", "2097152")
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(status.success(), "recursion subprocess failed: {status}");
            break;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("recursion subprocess exceeded deadline");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}
