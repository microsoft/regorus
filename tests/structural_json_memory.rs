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
}
