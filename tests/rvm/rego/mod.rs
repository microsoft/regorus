// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
use regorus::{Engine, Rc, Value};
use std::sync::Arc;
#[cfg(any(feature = "test-utils", all(feature = "yaml", feature = "std")))]
use test_generator::test_resources;

mod comprehension_failure_differential;
mod every_binding_differential;

#[cfg(any(feature = "test-utils", all(feature = "yaml", feature = "std")))]
mod yaml_harness;

#[test]
fn namespace_entrypoint_roundtrips_and_reuses_vm_state() -> Result<()> {
    let entrypoint = "data.graph.defUniqueName[\"1.0.0\"].deny";
    let mut engine = Engine::new();
    engine.add_policy(
        "namespace.rego".to_string(),
        r#"
        package graph.defUniqueName["1.0.0"]

        default deny := false
        deny := true if { input.blocked == true }
        "#
        .to_string(),
    )?;
    let entrypoint_ref: Rc<str> = entrypoint.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint_ref)?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;

    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => {
            anyhow::bail!("binary namespace program unexpectedly needs recompilation")
        }
    };

    for (program, mode) in [
        (json_program, ExecutionMode::RunToCompletion),
        (binary_program, ExecutionMode::Suspendable),
    ] {
        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        vm.set_data(Value::new_object())?;
        vm.set_execution_mode(mode);

        vm.set_input(Value::from_json_str(r#"{"blocked":true}"#)?);
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            Value::Bool(true)
        );

        vm.set_input(Value::from_json_str(r#"{"blocked":false}"#)?);
        assert_eq!(vm.execute_entry_point_by_index(0)?, Value::Bool(false));

        vm.set_input(Value::Undefined);
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            Value::Bool(false)
        );
    }

    Ok(())
}

#[test]
fn numeric_namespace_selectors_keep_string_identity_on_reused_vm() -> Result<()> {
    let entrypoint = "data.consumer.result";
    let mut engine = Engine::new();
    engine.add_data(Value::from_json_str(
        r#"{"graph":{"1":{"extra":9},"1.0":{"extra":90}}}"#,
    )?)?;
    engine.add_policy(
        "namespace.rego".to_string(),
        r#"
        package graph["1"]
        value := 7
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "decimal_namespace.rego".to_string(),
        r#"
        package graph["1.0"]
        value := 70
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        result := data.graph[input.selector]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let cases = [
        (r#"{"selector":"1"}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":1}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":1.0}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":"1.0"}"#, r#"{"extra":90,"value":70}"#),
        (r#"{"selector":1.0}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":"1"}"#, r#"{"extra":9,"value":7}"#),
        (r#"{"selector":"1.0"}"#, r#"{"extra":90,"value":70}"#),
    ];

    for (input_json, expected_json) in cases {
        let input = Value::from_json_str(input_json)?;
        let expected = Value::from_json_str(expected_json)?;
        engine.set_input(input);
        assert_eq!(
            engine.eval_rule(entrypoint.to_string())?,
            expected,
            "interpreter result for input {input_json}"
        );
    }

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);

        for (input_json, expected_json) in cases {
            vm.set_input(Value::from_json_str(input_json)?);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                Value::from_json_str(expected_json)?,
                "{mode:?} result for input {input_json}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_namespace_package_prefetch_matches_in_both_vm_modes() -> Result<()> {
    let entrypoint = "data.framework.allow";
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        r#"
        package framework
        default allow := true
        allow := false if {
            cfg := data.config[input.namespace]
            cfg.blocked
        }
        "#
        .to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package config.target\nblocked := true".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let cases = [
        (
            Value::from_json_str(r#"{"namespace":"target"}"#)?,
            Value::Bool(false),
        ),
        (Value::new_object(), Value::Bool(true)),
        (Value::Undefined, Value::Bool(true)),
        (
            Value::from_json_str(r#"{"namespace":"target"}"#)?,
            Value::Bool(false),
        ),
    ];

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);

        for (input, expected) in &cases {
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                *expected,
                "{mode:?} result for input {input:?}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_namespace_selected_package_defaults_follow_normal_rules_in_both_vm_modes() -> Result<()>
{
    let entrypoint = "data.framework.allow";

    for default_first in [true, false] {
        let mut engine = Engine::new();
        engine.add_policy(
            "framework.rego".to_string(),
            r#"
            package framework
            default allow := true
            allow := false if {
                cfg := data.config[input.namespace]
                cfg.blocked
            }
            "#
            .to_string(),
        )?;

        let default_policy = "package config.target\ndefault blocked := false".to_string();
        let ordinary_policy = "package config.target\nblocked := true".to_string();
        if default_first {
            engine.add_policy("default.rego".to_string(), default_policy)?;
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
        } else {
            engine.add_policy("ordinary.rego".to_string(), ordinary_policy)?;
            engine.add_policy("default.rego".to_string(), default_policy)?;
        }

        let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
        let data = engine.get_data();

        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_data(data.clone())?;
            vm.set_execution_mode(mode);
            vm.set_input(Value::from_json_str(r#"{"namespace":"target"}"#)?);
            assert_eq!(
                vm.execute_entry_point_by_name(entrypoint)?,
                Value::Bool(false),
                "{mode:?} result with default_first={default_first}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_namespace_lookup_does_not_prefetch_a_trailing_sibling_rule() -> Result<()> {
    let entrypoint = "data.framework.result";
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        "package framework\nresult := data[input.namespace].value".to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nvalue := 7\nunrelated := data.framework.result".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            Value::from(7),
            "{mode:?} result"
        );
    }

    Ok(())
}

#[test]
fn dynamic_namespace_lookup_materializes_a_trailing_subpackage_without_parent_siblings(
) -> Result<()> {
    let entrypoint = "data.framework.config";
    let mut engine = Engine::new();
    engine.add_policy(
        "framework.rego".to_string(),
        "package framework\nconfig := data[input.namespace].nested".to_string(),
    )?;
    engine.add_policy(
        "target.rego".to_string(),
        "package target\nunrelated := data.framework.config".to_string(),
    )?;
    engine.add_policy(
        "nested.rego".to_string(),
        "package target.nested\nvalue := 7".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let input = Value::from_json_str(r#"{"namespace":"target"}"#)?;
    let expected = Value::from_json_str(r#"{"value":7}"#)?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entrypoint)?,
            expected,
            "{mode:?} result"
        );
    }

    Ok(())
}

#[test]
fn rvm_compiler_rejects_large_entrypoints_with_many_components() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "base.rego".to_string(),
        "package base\nvalue := true".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&"data.base.value".into())?;
    let paths = [
        format!("data{}", ".a".repeat(300_000)),
        format!("data{}", r#"["a"]"#.repeat(180_000)),
    ];

    for path in &paths {
        assert!(path.len() < 1024 * 1024);
        assert!(Compiler::compile_from_policy(&compiled, &[path]).is_err());
    }

    Ok(())
}

#[test]
fn numeric_object_selectors_do_not_use_data_namespace_fallback() -> Result<()> {
    let entrypoint = "data.consumer.result";
    let mut engine = Engine::new();
    engine.add_policy(
        "consumer.rego".to_string(),
        r#"
        package consumer
        result := input.object[input.selector]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&entrypoint.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entrypoint])?;
    let data = engine.get_data();
    let cases = [
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1"}"#,
            Value::String("integer string".into()),
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":1}"#,
            Value::Undefined,
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":1.0}"#,
            Value::Undefined,
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1.0"}"#,
            Value::String("decimal string".into()),
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":1.0}"#,
            Value::Undefined,
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1"}"#,
            Value::String("integer string".into()),
        ),
        (
            r#"{"object":{"1":"integer string","1.0":"decimal string"},"selector":"1.0"}"#,
            Value::String("decimal string".into()),
        ),
    ];

    for (input_json, expected) in &cases {
        engine.set_input(Value::from_json_str(input_json)?);
        let actual = engine.eval_rule(entrypoint.to_string())?;
        assert_eq!(
            &actual, expected,
            "interpreter result for input {input_json}"
        );
    }

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(data.clone())?;
        vm.set_execution_mode(mode);

        for (input_json, expected) in &cases {
            vm.set_input(Value::from_json_str(input_json)?);
            let actual = vm.execute_entry_point_by_name(entrypoint)?;
            assert_eq!(&actual, expected, "{mode:?} result for input {input_json}");
        }
    }

    Ok(())
}

#[test]
fn bracketed_identifier_entrypoint_roundtrips_and_executes_by_name_and_index() -> Result<()> {
    let requested_entrypoint = "data.graph[\"version\"].value";
    let mut engine = Engine::new();
    engine.add_policy(
        "namespace.rego".to_string(),
        "package graph.version\nvalue := 7".to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&"data.graph.version.value".into())?;
    for invalid_entrypoint in [
        "data.graph[1].value",
        "data.graph.version.value trailing",
        "data.graph.missing.value",
    ] {
        assert!(Compiler::compile_from_policy(&compiled, &[invalid_entrypoint]).is_err());
    }
    let program = Compiler::compile_from_policy(&compiled, &[requested_entrypoint])?;

    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => {
            anyhow::bail!("binary identifier program unexpectedly needs recompilation")
        }
    };

    for program in [json_program, binary_program] {
        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        vm.set_data(Value::new_object())?;
        assert_eq!(
            vm.execute_entry_point_by_name(requested_entrypoint)?,
            Value::from(7)
        );
        assert_eq!(vm.execute_entry_point_by_index(0)?, Value::from(7));
    }

    Ok(())
}

#[test]
fn bracketed_entrypoints_match_dotted_paths_at_supported_depths_and_reuse_vm() -> Result<()> {
    for (package_component_count, rule_component_count) in [(31, 1), (32, 1), (32, 32)] {
        let package_components = (0..package_component_count)
            .map(|index| format!("p{index}"))
            .collect::<Vec<_>>();
        let rule_components = (0..rule_component_count)
            .map(|index| format!("r{index}"))
            .collect::<Vec<_>>();
        let package_path = package_components.join(".");
        let rule_path = rule_components.join(".");
        let dotted_path = format!("data.{package_path}.{rule_path}");
        let mut bracketed_path = String::from("data");
        for component in package_components.iter().chain(&rule_components) {
            bracketed_path.push_str(&format!("[\"{component}\"]"));
        }

        let mut engine = Engine::new();
        engine.add_policy(
            "deep.rego".to_string(),
            format!("package {package_path}\n{rule_path} := 7"),
        )?;
        let dotted_entrypoint: Rc<str> = dotted_path.into();
        let compiled = engine.compile_with_entrypoint(&dotted_entrypoint)?;
        let program = Compiler::compile_from_policy(&compiled, &[bracketed_path.as_str()])?;

        let json = program.serialize_json().map_err(anyhow::Error::msg)?;
        let json_program = Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;
        let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
        let binary_program =
            match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
                DeserializationResult::Complete(program) => program,
                DeserializationResult::Partial(_) => {
                    anyhow::bail!("deep namespace program unexpectedly needs recompilation")
                }
            };

        for (program, mode) in [
            (json_program, ExecutionMode::RunToCompletion),
            (binary_program, ExecutionMode::Suspendable),
        ] {
            let mut vm = RegoVM::new();
            vm.load_program(Arc::new(program));
            vm.set_data(Value::new_object())?;
            vm.set_execution_mode(mode);
            for _ in 0..2 {
                assert_eq!(
                    vm.execute_entry_point_by_name(&bracketed_path)?,
                    Value::from(7),
                    "{mode:?} named path with {package_component_count} package and {rule_component_count} rule components"
                );
                assert_eq!(
                    vm.execute_entry_point_by_index(0)?,
                    Value::from(7),
                    "{mode:?} indexed path with {package_component_count} package and {rule_component_count} rule components"
                );
            }
        }
    }

    Ok(())
}

#[cfg(any(feature = "test-utils", all(feature = "yaml", feature = "std")))]
#[test_resources("tests/rvm/rego/cases/*.yaml")]
fn run_rego_compiler_yaml(file: &str) {
    yaml_harness::yaml_test_impl(file).unwrap();
}

#[test]
fn registered_host_await_vm_reuses_after_instruction_limit() -> Result<()> {
    const ENTRYPOINT: &str = "data.demo.result";
    let mut engine = Engine::new();
    engine.add_policy(
        "host-await.rego".to_string(),
        r#"
        package demo
        import rego.v1

        result := echo(input.value, {"nested": input.value})
        "#
        .to_string(),
    )?;
    let entrypoint: Rc<str> = ENTRYPOINT.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    let program =
        Compiler::compile_from_policy_with_host_await(&compiled, &[ENTRYPOINT], &[("echo", 2)])?;

    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_data(engine.get_data())?;
    vm.set_input(Value::from_json_str(r#"{"value":"request"}"#)?);
    vm.set_max_instructions(usize::MAX);

    vm.execute_entry_point_by_name(ENTRYPOINT)?;
    let expected_argument = Value::from_json_str(r#"["request", {"nested":"request"}]"#)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait {
                identifier,
                argument,
                ..
            },
            ..
        } if identifier == &Value::from("echo") && argument == &expected_argument
    ));

    vm.set_max_instructions(0);
    assert!(matches!(
        vm.resume(Some(Value::from("limited-response"))),
        Err(VmError::InstructionLimitExceeded { limit: 0, .. })
    ));
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Error {
            error: VmError::InstructionLimitExceeded { limit: 0, .. }
        }
    ));

    vm.set_max_instructions(usize::MAX);
    vm.execute_entry_point_by_name(ENTRYPOINT)?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { argument, .. },
            ..
        } if argument == &expected_argument
    ));
    vm.resume(Some(Value::from("host-response")))?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Completed { result } if result == &Value::from("host-response")
    ));

    Ok(())
}

#[cfg(any(feature = "test-utils", all(feature = "yaml", feature = "std")))]
#[test]
fn test_specific_case() {
    if std::env::var("TEST_CASE_FILTER").is_err() {
        println!("💡 Specific case test skipped - no TEST_CASE_FILTER set");
        println!("   Usage: TEST_CASE_FILTER=\"note substring\" cargo test test_specific_case -- --nocapture");
        return;
    }

    if let Ok(entries) = std::fs::read_dir("tests/rvm/rego/cases") {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.extension().and_then(|s| s.to_str()) == Some("yaml") {
                if let Err(e) = yaml_harness::yaml_test_impl(path.to_str().unwrap()) {
                    println!("❌ Error in file {}: {}", path.display(), e);
                }
            }
        }
    }
}
