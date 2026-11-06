// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use regorus::{Engine, LimitError, Value};
use std::collections::{BTreeMap, BTreeSet};

const LIMIT: usize = 64;

fn nested(depth: usize, kind: usize) -> Value {
    nested_with_leaf(depth, kind, Value::Null)
}

fn nested_with_leaf(depth: usize, kind: usize, leaf: Value) -> Value {
    (0..depth).fold(leaf, |value, level| {
        match if kind == 3 { level % 3 } else { kind } {
            0 => Value::from(vec![value]),
            1 => Value::from(BTreeSet::from([value])),
            _ => Value::from(BTreeMap::from([(Value::from("k"), value)])),
        }
    })
}

fn marshal_expressions() -> Vec<&'static str> {
    #[allow(unused_mut)]
    let mut expressions = vec![
        "json.marshal(input)",
        "json.marshal_with_options(input, {})",
        r#"json.marshal_with_options(input, {"pretty": false})"#,
        r#"json.marshal_with_options(input, {"pretty": true, "indent": " ", "prefix": ">"})"#,
    ];
    #[cfg(feature = "yaml")]
    expressions.push("yaml.marshal(input)");
    expressions
}

fn engine(module: String, strict: bool, input: Value) -> Engine {
    let mut engine = Engine::new();
    engine.add_policy("test.rego".into(), module).unwrap();
    engine.set_strict_builtin_errors(strict);
    engine.set_input(input);
    engine
}

#[test]
fn generic_serde_preserves_container_budget_and_iterative_json() {
    for kind in 0..4 {
        let boundary = nested(LIMIT, kind);
        assert_eq!(
            serde_json::to_string(&boundary).unwrap(),
            format!("{boundary}")
        );
        assert!(serde_json::to_value(&boundary).is_ok());
        let beyond = nested(LIMIT + 1, kind);
        for error in [
            serde_json::to_string(&beyond).unwrap_err(),
            serde_json::to_string_pretty(&beyond).unwrap_err(),
            serde_json::to_value(&beyond).unwrap_err(),
        ] {
            assert!(error.to_string().contains("exceeds 64 nested containers"));
        }
        assert!(beyond.to_json_str().is_ok());
        assert!(!format!("{beyond}").contains("exceeds"));
    }

    // Non-string keys are encoded iteratively, not through container callbacks.
    let object = Value::from(BTreeMap::from([(nested(256, 0), nested(LIMIT - 1, 0))]));
    assert_eq!(serde_json::to_string(&object).unwrap(), format!("{object}"));
}

#[test]
fn interpreter_marshal_resource_errors_are_fatal_even_under_negation_and_defaults() {
    for strict in [false, true] {
        for expression in marshal_expressions() {
            for rule in [
                format!("p := {expression}"),
                format!("p := true if {{ not {expression} }}"),
                format!("default p := \"fallback\"\np := {expression}"),
                format!("p := value if {{ value := {expression} }} else := \"fallback\""),
                format!("serialized := {expression}\np := serialized"),
            ] {
                let mut engine = engine(
                    format!("package test\n{rule}"),
                    strict,
                    nested(LIMIT + 1, 3),
                );
                let error = engine.eval_rule("data.test.p".into()).unwrap_err();
                assert_eq!(
                    error.downcast_ref::<LimitError>(),
                    Some(&LimitError::SerializationDepthExceeded { limit: LIMIT }),
                    "{strict}: {rule}: {error:?}"
                );
                assert!(error.to_string().contains("exceeds 64 nested containers"));

                engine.set_input(Value::Null);
                assert!(engine.eval_rule("data.test.p".into()).is_ok());
            }
        }
    }
}

#[test]
fn interpreter_function_alternatives_preserve_resource_errors() {
    for strict in [false, true] {
        for expression in marshal_expressions() {
            let expression = expression.replace("input", "x");
            for definitions in [
                format!("f(x) := {expression}"),
                format!("f(x) := true if {{ {expression} }}\nf(x) := true"),
            ] {
                let mut engine = engine(
                    format!("package test\n{definitions}\np := f(input)"),
                    strict,
                    nested(LIMIT + 1, 0),
                );
                let error = engine.eval_rule("data.test.p".into()).unwrap_err();
                assert_eq!(
                    error.downcast_ref::<LimitError>(),
                    Some(&LimitError::SerializationDepthExceeded { limit: LIMIT }),
                    "{strict}: {definitions}: {error:?}"
                );
                engine.set_input(Value::Null);
                assert!(engine.eval_rule("data.test.p".into()).is_ok());
            }
        }
    }
}

#[test]
fn interpreter_function_type_errors_remain_ordinary() {
    for strict in [false, true] {
        let mut engine = engine(
            "package test\nf(x) := true if { upper(x) }\nf(x) := true\np := f(input)".into(),
            strict,
            Value::Null,
        );
        let result = engine.eval_rule("data.test.p".into());
        if strict {
            let error = result.unwrap_err();
            assert!(error.downcast_ref::<LimitError>().is_none());
            assert!(error.to_string().contains("expects string argument"));
        } else {
            assert_eq!(result.unwrap(), Value::Bool(true));
        }
        engine.set_input(Value::from("valid"));
        assert_eq!(
            engine.eval_rule("data.test.p".into()).unwrap(),
            Value::Bool(true)
        );
    }
}

#[test]
fn interpreter_options_type_errors_remain_ordinary_and_precede_serialization() {
    for options in [
        "null",
        "[]",
        r#"{"pretty": "true"}"#,
        r#"{"prefix": false}"#,
        r#"{"indent": 1}"#,
        r#"{"unknown": true}"#,
    ] {
        let expression = format!("json.marshal_with_options(input, {options})");
        for strict in [false, true] {
            let mut engine = engine(
                format!("package test\np := {expression}"),
                strict,
                nested(LIMIT + 1, 0),
            );
            let result = engine.eval_query(expression.clone(), false);
            if strict {
                let error = result.unwrap_err();
                assert!(error.downcast_ref::<LimitError>().is_none(), "{error:?}");
                assert!(!error.to_string().contains("exceeds 64 nested containers"));
            } else {
                assert!(result.unwrap().result.is_empty(), "{options}");
            }
        }
    }
}

#[test]
fn interpreter_marshal_success_is_unchanged_at_the_boundary() {
    let input = nested(LIMIT, 3);
    for strict in [false, true] {
        for (expression, expected) in [
            ("json.marshal(input)", format!("{input}")),
            ("json.marshal_with_options(input, {})", format!("{input}")),
            (
                r#"json.marshal_with_options(input, {"pretty": false})"#,
                format!("{input}"),
            ),
            (
                r#"json.marshal_with_options(input, {"pretty": true, "indent": "  "})"#,
                input.to_json_str().unwrap(),
            ),
        ] {
            let mut engine = engine(
                format!("package test\np := {expression}"),
                strict,
                input.clone(),
            );
            assert_eq!(
                engine.eval_rule("data.test.p".into()).unwrap(),
                Value::from(expected)
            );
        }
    }
}

#[cfg(feature = "rvm")]
mod rvm {
    use super::*;
    use regorus::languages::rego::compiler::Compiler;
    use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
    use regorus::Rc;

    fn vm(module: String, strict: bool, mode: ExecutionMode) -> RegoVM {
        let mut engine = engine(module, strict, Value::Null);
        let policy = engine
            .compile_with_entrypoint(&Rc::from("data.test.p"))
            .unwrap();
        let program = Compiler::compile_from_policy(&policy, &["data.test.p"]).unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_strict_builtin_errors(strict);
        vm.set_execution_mode(mode);
        vm
    }

    #[test]
    fn marshal_resource_errors_are_fatal_and_vm_recovers() {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for strict in [false, true] {
                for expression in marshal_expressions() {
                    for rule in [
                        format!("p := {expression}"),
                        format!("p := true if {{ not {expression} }}"),
                        format!("default p := \"fallback\"\np := {expression}"),
                        format!("p := value if {{ value := {expression} }} else := \"fallback\""),
                        format!("serialized := {expression}\np := serialized"),
                        format!(
                            "f(x) := {}\np := f(input)",
                            expression.replace("input", "x")
                        ),
                        format!(
                            "f(x) := true if {{ {} }}\nf(x) := true\np := f(input)",
                            expression.replace("input", "x")
                        ),
                    ] {
                        let mut vm = vm(format!("package test\n{rule}"), strict, mode);
                        let sentinel: Rc<str> = Rc::from("leaf");
                        vm.set_input(nested_with_leaf(
                            LIMIT + 1,
                            3,
                            Value::String(sentinel.clone()),
                        ));
                        let error = vm.execute_entry_point_by_name("data.test.p").unwrap_err();
                        assert!(
                            matches!(
                                error,
                                VmError::SerializationDepthExceeded { limit: LIMIT, .. }
                            ),
                            "{mode:?}, {strict}: {rule}: {error:?}"
                        );
                        assert!(
                            matches!(vm.execution_state(), ExecutionState::Error { error } if matches!(error, VmError::SerializationDepthExceeded { limit: LIMIT, .. })),
                            "{:?}",
                            vm.execution_state()
                        );

                        vm.set_input(Value::Null);
                        assert_eq!(Rc::strong_count(&sentinel), 1, "{mode:?}: {rule}");
                        assert!(vm.execute_entry_point_by_name("data.test.p").is_ok());
                    }
                }
            }
        }
    }

    #[test]
    fn malformed_options_remain_nonfatal_rule_failures() {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for strict in [false, true] {
                for options in [
                    "null",
                    "[]",
                    r#"{"pretty": "true"}"#,
                    r#"{"prefix": false}"#,
                    r#"{"indent": 1}"#,
                    r#"{"unknown": true}"#,
                ] {
                    let mut vm = vm(
                        format!(
                            "package test\ndefault p := \"fallback\"\np := json.marshal_with_options(input, {options})"
                        ),
                        strict,
                        mode,
                    );
                    vm.set_input(nested(LIMIT + 1, 0));
                    assert_eq!(
                        vm.execute_entry_point_by_name("data.test.p").unwrap(),
                        Value::from("fallback"),
                        "{mode:?}, {strict}: {options}"
                    );
                }
            }
        }
    }

    #[test]
    fn marshal_success_is_unchanged_at_the_boundary() {
        let input = nested(LIMIT, 3);
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for strict in [false, true] {
                for (expression, expected) in [
                    ("json.marshal(input)", format!("{input}")),
                    ("json.marshal_with_options(input, {})", format!("{input}")),
                    (
                        r#"json.marshal_with_options(input, {"pretty": false})"#,
                        format!("{input}"),
                    ),
                    (
                        r#"json.marshal_with_options(input, {"pretty": true, "indent": "  "})"#,
                        input.to_json_str().unwrap(),
                    ),
                ] {
                    let mut vm = vm(format!("package test\np := {expression}"), strict, mode);
                    vm.set_input(input.clone());
                    assert_eq!(
                        vm.execute_entry_point_by_name("data.test.p").unwrap(),
                        Value::from(expected)
                    );
                }
            }
        }
    }
}
