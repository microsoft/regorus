// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, RegoVM, VmError};
use regorus::{Engine, Rc, Value};
use std::sync::Arc;

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
        engine.set_strict_builtin_errors(false);
        engine.add_policy("probe.rego".into(), module)?;
        let missing = if default.is_empty() {
            Value::Undefined
        } else {
            Value::from(99)
        };
        let compiled = engine.compile_with_entrypoint(&Rc::from("data.probe.result"))?;
        let original = Compiler::compile_from_policy(&compiled, &["data.probe.result"])?;
        let bytes = original.serialize_binary().map_err(anyhow::Error::msg)?;
        let DeserializationResult::Complete(restored) =
            Program::deserialize_binary(&bytes).map_err(anyhow::Error::msg)?
        else {
            anyhow::bail!("expected a complete serialized lookup program");
        };

        for program in [original, Arc::new(restored)] {
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
