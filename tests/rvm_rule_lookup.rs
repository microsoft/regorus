// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, RegoVM, VmError};
use regorus::{Engine, Rc, Value};

#[test]
fn virtual_reference_suffixes() -> anyhow::Result<()> {
    for module in [
        r#"package probe
        nested.p := {"a": {"b": 7}}
        result := data.probe.nested[input.key].a.b"#,
        r#"package probe
        nested.p.value := 7
        result := data.probe.nested[input.key].value"#,
    ] {
        let mut engine = Engine::new();
        engine.add_policy("probe.rego".into(), module.into())?;
        engine.set_input(Value::from_json_str(r#"{"key":"p"}"#)?);
        assert_eq!(
            engine.eval_rule("data.probe.result".into())?,
            Value::from(7)
        );

        let compiled = engine.compile_with_entrypoint(&Rc::from("data.probe.result"))?;
        let program = Compiler::compile_from_policy(&compiled, &["data.probe.result"])?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for (key, expected) in [("p", Value::from(7)), ("missing", Value::Undefined)] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_input(Value::from_json_str(&format!(r#"{{"key":"{key}"}}"#))?);
                vm.set_execution_mode(mode);
                assert_eq!(
                    vm.execute_entry_point_by_name("data.probe.result")?,
                    expected,
                    "{mode:?}, key={key}"
                );
            }
        }
    }
    Ok(())
}

#[test]
fn same_namespace_selection_and_reuse() -> anyhow::Result<()> {
    for default in ["", "default result := 99"] {
        let module = format!(
            r#"package probe
            p := {{"a": {{"b": 7}}}}
            recursive := data.probe.recursive
            {default}
            result := data.probe[input.key].a.b"#
        );
        let mut engine = Engine::new();
        engine.add_policy("probe.rego".into(), module)?;
        engine.set_input(Value::from_json_str(r#"{"key":"p"}"#)?);
        // Preserve the interpreter's existing same-namespace behavior.
        let missing = if default.is_empty() {
            Value::Undefined
        } else {
            Value::from(99)
        };
        assert_eq!(engine.eval_rule("data.probe.result".into())?, missing);

        let compiled = engine.compile_with_entrypoint(&Rc::from("data.probe.result"))?;
        let original = Compiler::compile_from_policy(&compiled, &["data.probe.result"])?;
        let bytes = original.serialize_binary().map_err(anyhow::Error::msg)?;
        let DeserializationResult::Complete(restored) =
            Program::deserialize_binary(&bytes).map_err(anyhow::Error::msg)?
        else {
            anyhow::bail!("expected a complete serialized lookup program");
        };

        for program in [original, Rc::new(restored)] {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                for key in ["p", "result", "missing", "recursive", "p"] {
                    vm.set_input(Value::from_json_str(&format!(r#"{{"key":"{key}"}}"#))?);
                    let result = vm.execute_entry_point_by_name("data.probe.result");
                    if matches!(key, "result" | "recursive") {
                        assert!(
                            matches!(result, Err(VmError::RecursiveRuleEvaluation { .. })),
                            "{mode:?}, key={key}: {result:?}"
                        );
                    } else {
                        assert_eq!(
                            result?,
                            if key == "p" {
                                Value::from(7)
                            } else {
                                missing.clone()
                            },
                            "{mode:?}, key={key}"
                        );
                    }
                }
            }
        }
    }
    Ok(())
}

#[test]
fn native_rule_depth_is_bounded() -> anyhow::Result<()> {
    let mut module = String::from("package probe\nr20 := 7\n");
    for index in 0..20 {
        module.push_str(&format!("r{index} := data.probe.r{}\n", index + 1));
    }
    let mut engine = Engine::new();
    engine.add_policy("probe.rego".into(), module)?;
    let compiled = engine.compile_with_entrypoint(&Rc::from("data.probe.r0"))?;
    let program = Compiler::compile_from_policy(&compiled, &["data.probe.r0"])?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        let result = vm.execute_entry_point_by_name("data.probe.r0");
        if mode == ExecutionMode::RunToCompletion {
            assert!(
                matches!(
                    result,
                    Err(VmError::RuleCallDepthExceeded { limit: 16, .. })
                ),
                "{result:?}"
            );
        } else {
            assert_eq!(result?, Value::from(7));
        }
    }
    Ok(())
}
