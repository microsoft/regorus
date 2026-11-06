// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::instructions::LiteralOrRegister;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
use regorus::{Engine, Rc, Value};
use std::sync::Arc;

#[test]
fn namespace_assembly_failure_preserves_rule_fallback() {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(false);
    engine
        .add_policy(
            "probe.rego".into(),
            "package probe\n\
             default result := 99\n\
             result := data.catalog\n\
             safe := 7"
                .into(),
        )
        .unwrap();
    engine
        .add_policy("catalog.rego".into(), "package catalog\np := 7".into())
        .unwrap();
    let policy = engine
        .compile_with_entrypoint(&Rc::from("data.probe.result"))
        .unwrap();
    let program =
        Compiler::compile_from_policy(&policy, &["data.probe.result", "data.probe.safe"]).unwrap();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.set_data(Value::from_json_str(r#"{"catalog":1}"#).unwrap())
            .unwrap();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_strict_builtin_errors(false);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.result").unwrap(),
            Value::from(99),
            "{mode:?}"
        );
        if mode == ExecutionMode::Suspendable {
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Completed { .. }
            ));
        }
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
            Value::from(7)
        );
    }
}

#[test]
fn loaded_dynamic_lookup_preserves_host_resume_contract() {
    const ENTRY: &str = "data.framework.result";
    let mut engine = Engine::new();
    for (name, module) in [
        (
            "framework.rego",
            "package framework\n\
             default result := 99\n\
             result := data.config[input.namespace].record",
        ),
        (
            "config.rego",
            "package config.target\n\
             record := __builtin_host_await(input.subject, \"selected\")",
        ),
    ] {
        engine.add_policy(name.into(), module.into()).unwrap();
    }
    let policy = engine.compile_with_entrypoint(&Rc::from(ENTRY)).unwrap();
    let mut program = (*Compiler::compile_from_policy(&policy, &[ENTRY]).unwrap()).clone();
    assert_eq!(
        program
            .instruction_data
            .virtual_data_document_lookup_params
            .len(),
        1
    );
    // Isolate VM suffix indexing from the separate compiler rule-prefix lookup fix.
    for key in ["a", "b"] {
        let literal = u16::try_from(program.literals.len()).unwrap();
        program.literals.push(Value::from(key));
        program
            .instruction_data
            .virtual_data_document_lookup_params
            .first_mut()
            .unwrap()
            .path_components
            .push(LiteralOrRegister::Literal(literal));
    }
    let program = Arc::new(program);
    let json = Arc::new(Program::deserialize_json(&program.serialize_json().unwrap()).unwrap());
    let binary = match Program::deserialize_binary(&program.serialize_binary().unwrap()).unwrap() {
        DeserializationResult::Complete(program) => Arc::new(program),
        DeserializationResult::Partial(_) => panic!("current program must round-trip"),
    };

    for program in [program, json, binary] {
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.set_strict_builtin_errors(false);
        vm.set_input(Value::from_json_str(r#"{"namespace":"target","subject":"dummy"}"#).unwrap());
        vm.execute_entry_point_by_name(ENTRY).unwrap();
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Suspended {
                reason: SuspendReason::HostAwait { identifier, argument, .. }, ..
            } if identifier == &Value::from("selected") && argument == &Value::from("dummy")
        ));
        let suspended = vm.execution_state().clone();
        assert!(matches!(
            vm.resume(None),
            Err(VmError::MissingResumeValue { .. })
        ));
        assert_eq!(vm.execution_state(), &suspended);
        assert_eq!(
            vm.resume(Some(Value::from_json_str(r#"{"a":{"b":7}}"#).unwrap()))
                .unwrap(),
            Value::from(7)
        );
        assert_eq!(
            vm.execution_state(),
            &ExecutionState::Completed {
                result: Value::from(7)
            }
        );
    }
}
