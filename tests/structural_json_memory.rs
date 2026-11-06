// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(all(
    feature = "allocator-memory-limits",
    any(feature = "jsonschema", feature = "rvm"),
    not(miri)
))]

use regorus::set_global_memory_limit;

struct ResetLimit;

impl Drop for ResetLimit {
    fn drop(&mut self) {
        set_global_memory_limit(None);
    }
}

fn tighten_limit() -> ResetLimit {
    let usage = mimalloc::global_allocation_stats_snapshot().allocated as u64;
    set_global_memory_limit(Some(usage.saturating_add(256 * 1024)));
    ResetLimit
}

#[cfg(feature = "jsonschema")]
fn object_schema_memory_errors_cannot_allow_negation() {
    use regorus::{Engine, LimitError, Value};

    let module = r#"
package schema
schema := {0: input, 1: true}
default allow_verify := false
allow_verify if { not json.verify_schema(schema)[0] }
default allow_match_schema := false
allow_match_schema if { not json.match_schema(1, schema)[0] }
default allow_match_document := false
allow_match_document if { not json.match_schema(schema, true)[0] }
"#;
    let large_input = Value::from("x".repeat(4 * 1024 * 1024));
    let small_input = Value::from("small");
    for strict in [false, true] {
        for rule in ["allow_verify", "allow_match_schema", "allow_match_document"] {
            let mut engine = Engine::new();
            engine.set_strict_builtin_errors(strict);
            engine
                .add_policy("schema.rego".into(), module.into())
                .unwrap();
            let entrypoint = regorus::Rc::<str>::from(format!("data.schema.{rule}"));
            #[cfg(feature = "rvm")]
            let data = engine.get_data();
            #[cfg(feature = "rvm")]
            let program = {
                let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
                regorus::languages::rego::compiler::Compiler::compile_from_policy(
                    &compiled,
                    &[entrypoint.as_ref()],
                )
                .unwrap()
            };

            engine.set_input(small_input.clone());
            assert_eq!(
                engine.eval_rule(entrypoint.to_string()).unwrap(),
                Value::Bool(false)
            );
            engine.set_input(large_input.clone());
            let guard = tighten_limit();
            let result = engine.eval_rule(entrypoint.to_string());
            drop(guard);
            let error = result.expect_err("memory exhaustion must not allow negation");
            assert!(
                matches!(
                    error.downcast_ref::<LimitError>(),
                    Some(LimitError::MemoryLimitExceeded { .. })
                ),
                "{rule}, strict={strict}: {error:#}"
            );
            engine.set_input(small_input.clone());
            assert_eq!(
                engine.eval_rule(entrypoint.to_string()).unwrap(),
                Value::Bool(false)
            );

            #[cfg(feature = "rvm")]
            for mode in [
                regorus::rvm::vm::ExecutionMode::RunToCompletion,
                regorus::rvm::vm::ExecutionMode::Suspendable,
            ] {
                use regorus::rvm::vm::{RegoVM, VmError};

                let mut vm = RegoVM::new();
                vm.set_execution_mode(mode);
                vm.set_strict_builtin_errors(strict);
                vm.load_program(program.clone());
                vm.set_data(data.clone()).unwrap();
                vm.set_input(small_input.clone());
                assert_eq!(vm.execute().unwrap(), Value::Bool(false));
                vm.set_input(large_input.clone());
                let guard = tighten_limit();
                let result = vm.execute();
                drop(guard);
                assert!(
                    matches!(result, Err(VmError::MemoryLimitExceeded { .. })),
                    "{rule}, strict={strict}, {mode:?}: {result:?}"
                );
                vm.set_input(small_input.clone());
                assert_eq!(vm.execute().unwrap(), Value::Bool(false));
            }
        }
    }
}

// Keep global-limit changes in a dedicated one-test process, so unrelated tests
// cannot race the limit. The wide nested extension exceeds the added budget
// during structural DOM accumulation, after initial parsing/evaluation checks.
#[test]
fn structural_json_memory_errors_survive_nested_visitors() {
    let extension = format!("[{}]", r#"["item"],"#.repeat(40_000));
    let extension = extension.replace(",]", "]");

    #[cfg(feature = "jsonschema")]
    for strict in [false, true] {
        use regorus::{Engine, LimitError, Value};
        let mut engine = Engine::new();
        engine.set_strict_builtin_errors(strict);
        engine
            .add_policy(
                "schema.rego".into(),
                "package schema\nvalid := json.verify_schema(input)[0]".into(),
            )
            .unwrap();
        engine.set_input(Value::from("{}"));
        assert_eq!(
            engine.eval_rule("data.schema.valid".into()).unwrap(),
            Value::Bool(true)
        );
        engine.set_input(Value::from(format!(r#"{{"extension":{extension}}}"#)));
        let guard = tighten_limit();
        let result = engine.eval_rule("data.schema.valid".into());
        drop(guard);
        let error = result.unwrap_err();
        assert!(
            matches!(
                error.downcast_ref::<LimitError>(),
                Some(LimitError::MemoryLimitExceeded { .. })
            ),
            "{error:#}"
        );
        engine.set_input(Value::from("{}"));
        assert_eq!(
            engine.eval_rule("data.schema.valid".into()).unwrap(),
            Value::Bool(true)
        );
    }

    #[cfg(feature = "rvm")]
    {
        use regorus::rvm::program::Program;
        let base = Program::new().serialize_json().unwrap();
        let text = format!(
            r#"{{"extension":{extension},{}"#,
            base.strip_prefix('{').unwrap()
        );
        let guard = tighten_limit();
        let result = Program::deserialize_json(&text);
        drop(guard);
        assert!(result.unwrap_err().contains("exceeded memory limit"));
        assert!(Program::deserialize_json(&base).is_ok());
    }

    #[cfg(feature = "jsonschema")]
    object_schema_memory_errors_cannot_allow_negation();
}
