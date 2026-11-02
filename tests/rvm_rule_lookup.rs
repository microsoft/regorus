// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
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
        assert_eq!(engine.eval_rule("data.probe.result".into())?, Value::from(7));

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
