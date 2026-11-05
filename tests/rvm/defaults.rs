// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
use regorus::{Engine, Rc, Value};
use std::sync::Arc;

const ENTRY: &str = "data.defaults.result";

fn compile(module: &str, host_await: &[(&str, usize)]) -> Arc<Program> {
    let mut engine = Engine::new();
    engine
        .add_policy("defaults.rego".into(), module.into())
        .unwrap();
    let policy = engine.compile_with_entrypoint(&Rc::from(ENTRY)).unwrap();
    Compiler::compile_from_policy_with_host_await(&policy, &[ENTRY], host_await).unwrap()
}

fn round_trips(program: Arc<Program>) -> Vec<Arc<Program>> {
    let json = Arc::new(Program::deserialize_json(&program.serialize_json().unwrap()).unwrap());
    let binary = match Program::deserialize_binary(&program.serialize_binary().unwrap()).unwrap() {
        DeserializationResult::Complete(program) => Arc::new(program),
        DeserializationResult::Partial(_) => panic!("new default metadata must round-trip"),
    };
    vec![program, json, binary]
}

fn assert_reusable(module: &str, cases: &[(&str, &str, Value)]) {
    for program in round_trips(compile(module, &[])) {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(false);
            for (input, data, expected) in cases {
                vm.set_input(Value::from_json_str(input).unwrap());
                vm.set_data(Value::from_json_str(data).unwrap()).unwrap();
                assert_eq!(
                    vm.execute_entry_point_by_name(ENTRY).unwrap(),
                    *expected,
                    "{mode:?}, input={input}, data={data}"
                );
            }
        }
    }
}

#[test]
fn default_comprehensions_read_current_input_and_data() {
    let modules = [
        "package defaults\ndefault result := [x | x := input.x]",
        "package defaults\ndefault result := [x | x := data.x]",
        r#"package defaults
        default result := {"value": x | x := input.x}
        "#,
        "package defaults\ndefault result := {x | x := data.x}",
    ];
    for (index, module) in modules.iter().enumerate() {
        let expected = |number| match index {
            0 | 1 => Value::Array(Rc::new(vec![Value::from(number)].into())),
            2 => Value::from_json_str(&format!(r#"{{"value":{number}}}"#)).unwrap(),
            _ => Value::Set(Rc::new([Value::from(number)].into_iter().collect())),
        };
        assert_reusable(
            module,
            &[
                (r#"{"x":3}"#, r#"{"x":3}"#, expected(3)),
                (
                    "{}",
                    "{}",
                    match index {
                        0 | 1 => Value::new_array(),
                        2 => Value::new_object(),
                        _ => Value::new_set(),
                    },
                ),
                (r#"{"x":8}"#, r#"{"x":8}"#, expected(8)),
                (r#"{"x":3}"#, r#"{"x":3}"#, expected(3)),
            ],
        );
    }
}

#[test]
fn default_comprehensions_skip_missing_yields_without_losing_iterations() {
    for (expression, expected, empty) in [
        ("[x.k | some x in input.items]", "[false,null]", "[]"),
        (
            "{x.key:x.k | some x in input.items}",
            r#"{"ok":false,"null":null}"#,
            "{}",
        ),
        (
            "[[x.k | true] | some x in input.items]",
            "[[],[false],[],[null],[]]",
            "[]",
        ),
    ] {
        let module = format!("package defaults\ndefault result := {expression}");
        let input = r#"{"items":[{},{"key":"ok","k":false},{},{"key":"null","k":null},{}]}"#;
        assert_reusable(
            &module,
            &[
                (input, "{}", Value::from_json_str(expected).unwrap()),
                (
                    r#"{"items":[]}"#,
                    "{}",
                    Value::from_json_str(empty).unwrap(),
                ),
                (input, "{}", Value::from_json_str(expected).unwrap()),
            ],
        );
    }
}

#[test]
fn executable_defaults_respect_native_depth_and_allow_reuse() {
    let program = compile(
        "package defaults\ndefault value := [x | x := input.x]\nresult := value",
        &[],
    );
    for program in round_trips(program) {
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_input(Value::from_json_str(r#"{"x":3}"#).unwrap());
        vm.set_max_native_rule_call_depth(1);
        for _ in 0..2 {
            assert!(matches!(
                vm.execute_entry_point_by_name(ENTRY),
                Err(VmError::RuleCallDepthExceeded { limit: 1, .. })
            ));
            assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
            assert!(vm.get_call_stack().is_empty());
        }
        vm.set_max_native_rule_call_depth(2);
        assert_eq!(
            vm.execute_entry_point_by_name(ENTRY).unwrap(),
            Value::from_json_str("[3]").unwrap()
        );
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.set_max_native_rule_call_depth(0);
        assert_eq!(
            vm.execute_entry_point_by_name(ENTRY).unwrap(),
            Value::from_json_str("[3]").unwrap()
        );
        assert!(vm.get_call_stack().is_empty());
    }
}

#[test]
fn function_only_prefixes_remain_undefined_after_serialization() {
    for expression in ["nested", "data.defaults.nested", "data.defaults[input.key]"] {
        assert_reusable(
            &format!("package defaults\ndefault nested.f(x) := 7\nresult := {expression}"),
            &[(r#"{"key":"nested"}"#, "{}", Value::Undefined)],
        );
    }
    assert_reusable(
        "package defaults\ndefault nested.f(x) := 7\ndefault result := false\nresult if nested",
        &[("{}", "{}", Value::Bool(false))],
    );
}

#[test]
fn invalid_default_expressions_are_rejected_before_lowering() {
    for expression in [
        "input.admin",
        "[input.admin]",
        r#"{"admin": input.admin}"#,
        "count([])",
        "1 + 2",
    ] {
        let mut engine = Engine::new();
        let added = engine.add_policy(
            "invalid.rego".into(),
            format!("package defaults\ndefault result := {expression}"),
        );
        if expression == "1 + 2" {
            assert!(added.is_err());
            continue;
        }
        added.unwrap();
        let policy = engine.compile_with_entrypoint(&Rc::from(ENTRY)).unwrap();
        let error = Compiler::compile_from_policy(&policy, &[ENTRY]).unwrap_err();
        assert!(error.to_string().contains("in default value"), "{error}");
    }
}

#[test]
fn sibling_default_comprehensions_have_independent_input_and_data_loads() {
    for root in ["input", "data"] {
        for (expression, expected) in [
            (
                format!("[[{root}.x | false], [{root}.x | true]]"),
                "[[],[7]]",
            ),
            (
                format!("[[[{root}.x | false], {root}.x] | true]"),
                "[[[],7]]",
            ),
            (
                format!("[[[{root}.x | false] | true], [{root}.x | true]]"),
                "[[[]],[7]]",
            ),
        ] {
            assert_reusable(
                &format!("package defaults\ndefault result := {expression}"),
                &[(
                    r#"{"x":7}"#,
                    r#"{"x":7}"#,
                    Value::from_json_str(expected).unwrap(),
                )],
            );
        }
    }
}

#[test]
fn namespace_and_leaf_defaults_share_one_host_response() {
    for (expression, expected) in [
        ("[nested.value, nested]", r#"[[7],{"value":[7]}]"#),
        ("[nested, nested.value]", r#"[{"value":[7]},[7]]"#),
        (
            "[nested.value, data.defaults[input.key]]",
            r#"[[7],{"value":[7]}]"#,
        ),
        (
            "[data.defaults[input.key], nested.value]",
            r#"[{"value":[7]},[7]]"#,
        ),
    ] {
        let module = format!(
            "package defaults\ndefault nested.value := [lookup(\"x\") | true]\nresult := {expression}"
        );
        for program in round_trips(compile(&module, &[("lookup", 1)])) {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                vm.set_input(Value::from_json_str(r#"{"key":"nested"}"#).unwrap());
                for _ in 0..2 {
                    vm.set_host_await_responses([(
                        Value::from("lookup"),
                        [Value::from(7), Value::from(13)],
                    )]);
                    let mut result = vm.execute_entry_point_by_name(ENTRY).unwrap();
                    if mode == ExecutionMode::Suspendable {
                        assert!(matches!(
                            vm.execution_state(),
                            ExecutionState::Suspended {
                                reason: SuspendReason::HostAwait { argument, identifier, .. },
                                ..
                            } if argument == &Value::from_json_str(r#"["x"]"#).unwrap()
                                && identifier == &Value::from("lookup")
                        ));
                        result = vm.resume(Some(Value::from(7))).unwrap();
                        assert!(matches!(
                            vm.execution_state(),
                            ExecutionState::Completed { .. }
                        ));
                    }
                    assert_eq!(result, Value::from_json_str(expected).unwrap());
                }
            }
        }
    }
}

#[test]
fn declared_function_only_packages_remain_empty_documents() {
    for declaration in ["default f(x) := 7", "default nested.f(x) := 7"] {
        let mut engine = Engine::new();
        engine
            .add_policy("lib.rego".into(), format!("package lib\n{declaration}"))
            .unwrap();
        engine
            .add_policy(
                "consumer.rego".into(),
                "package defaults\ndefault result := [x | x := data.lib]".into(),
            )
            .unwrap();
        assert_eq!(
            engine.eval_rule(ENTRY.into()).unwrap(),
            Value::from_json_str("[{}]").unwrap()
        );
        let policy = engine.compile_with_entrypoint(&Rc::from(ENTRY)).unwrap();
        for program in round_trips(Compiler::compile_from_policy(&policy, &[ENTRY]).unwrap()) {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                vm.set_data(Value::new_object()).unwrap();
                assert_eq!(
                    vm.execute_entry_point_by_name(ENTRY).unwrap(),
                    Value::from_json_str("[{}]").unwrap()
                );
            }
        }
    }
}

#[test]
fn sibling_default_dependencies_preserve_leaf_identity() {
    for module in [
        r#"package defaults
        default p["a"] := [v | v := p["b"]]
        default p["b"] := 1
        result := p
        "#,
        r#"package defaults
        default p.a := [v | v := data.defaults.p[input.key]]
        default p.b := 1
        result := p
        "#,
        r#"package defaults
        default p.a := [v | v := p[input.key]]
        default p.b := 1
        result := p
        "#,
    ] {
        assert_reusable(
            module,
            &[(
                r#"{"key":"b"}"#,
                "{}",
                Value::from_json_str(r#"{"a":[1],"b":1}"#).unwrap(),
            )],
        );
    }
}

#[test]
fn large_constant_namespaces_keep_the_literal_fast_path() {
    let mut module = String::from("package defaults\n");
    let mut expected = Value::new_object();
    for index in 0..256 {
        module.push_str(&format!("default p[\"key{index}\"] := {index}\n"));
        expected
            .as_object_mut()
            .unwrap()
            .insert(Value::from(format!("key{index}")), Value::from(index));
    }
    module.push_str("result := p");
    let program = compile(&module, &[]);
    let namespace = program
        .rule_infos
        .iter()
        .find(|rule| rule.name == "data.defaults.p")
        .unwrap();
    assert!(namespace.default_literal_index.is_some());
    assert!(namespace.default_entry_point.is_none());
    for program in round_trips(program) {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(vm.execute_entry_point_by_name(ENTRY).unwrap(), expected);
        }
    }
}

#[test]
fn nested_default_dynamic_reentry_is_not_sibling_recursion() {
    let module = r#"package defaults
        default p.a := [v | v := p[input.key]]
        default p.b := 1
        result := p
    "#;
    for program in round_trips(compile(module, &[])) {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            for key in ["b", "a", "b"] {
                vm.set_input(Value::from_json_str(&format!(r#"{{"key":"{key}"}}"#)).unwrap());
                let result = vm.execute_entry_point_by_name(ENTRY);
                if key == "a" {
                    assert!(matches!(
                        result,
                        Err(VmError::RecursiveRuleEvaluation { .. })
                    ));
                    assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
                } else {
                    assert_eq!(
                        result.unwrap(),
                        Value::from_json_str(r#"{"a":[1],"b":1}"#).unwrap()
                    );
                }
                assert!(vm.get_call_stack().is_empty());
                assert_eq!(vm.get_execution_mode(), mode);
            }
        }
    }
}

#[test]
fn indexed_and_nested_defaults_preserve_their_object_shape() {
    for module in [
        r#"package defaults
        default result["first"] := [x | x := input.x]
        default result["second"] := [y | y := data.y]
        "#,
        r#"package defaults
        default nested.first := [x | x := input.x]
        default nested.second := [y | y := data.y]
        result := nested
        "#,
    ] {
        assert_reusable(
            module,
            &[
                (
                    r#"{"x":3}"#,
                    r#"{"y":4}"#,
                    Value::from_json_str(r#"{"first":[3],"second":[4]}"#).unwrap(),
                ),
                (
                    r#"{"x":8}"#,
                    r#"{"y":9}"#,
                    Value::from_json_str(r#"{"first":[8],"second":[9]}"#).unwrap(),
                ),
            ],
        );
    }
    assert_reusable(
        r#"package defaults
        default result["first"] := 3
        default result["second"] := 4
        "#,
        &[(
            "{}",
            "{}",
            Value::from_json_str(r#"{"first":3,"second":4}"#).unwrap(),
        )],
    );
}

#[test]
fn function_defaults_bind_parameters_and_do_not_cache_calls() {
    assert_reusable(
        r#"package defaults
        default f(parameter) := [y | y := parameter]
        f(x) := [x, x] if x > 10
        result := [f(input.x), f(30), f(4)]
        "#,
        &[
            (
                r#"{"x":3}"#,
                "{}",
                Value::from_json_str("[[3],[30,30],[4]]").unwrap(),
            ),
            (
                r#"{"x":8}"#,
                "{}",
                Value::from_json_str("[[8],[30,30],[4]]").unwrap(),
            ),
        ],
    );
}

#[test]
fn dynamic_defaults_only_run_after_undefined_not_false() {
    assert_reusable(
        r#"package defaults
        default result := [x | x := input.x]
        result := false if input.enabled
        "#,
        &[
            (
                r#"{"x":3,"enabled":false}"#,
                "{}",
                Value::from_json_str("[3]").unwrap(),
            ),
            (r#"{"x":8,"enabled":true}"#, "{}", Value::Bool(false)),
            (
                r#"{"x":8,"enabled":false}"#,
                "{}",
                Value::from_json_str("[8]").unwrap(),
            ),
            ("{}", "{}", Value::from_json_str("[]").unwrap()),
        ],
    );
}

#[test]
fn conflicts_never_select_literal_or_executable_defaults() {
    for default in ["7", "[x | x := input.x]"] {
        let module =
            format!("package defaults\ndefault result := {default}\nresult := 1\nresult := 2");
        for program in round_trips(compile(&module, &[])) {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                vm.set_input(Value::from_json_str(r#"{"x":3}"#).unwrap());
                match vm.execute_entry_point_by_name(ENTRY) {
                    Ok(Value::Undefined) | Err(_) => {}
                    Ok(value) => panic!("a conflict must not select a default: {value:?}"),
                }
            }
        }
    }
}

#[test]
fn object_and_set_function_defaults_bind_lexical_parameters() {
    assert_reusable(
        r#"package defaults
        default object(x) := {"value": y | y := x}
        default set(x) := {y | y := x}
        result := [object(3), object(8), set(3), set(8)]
        "#,
        &[(
            "{}",
            "{}",
            Value::Array(Rc::new(
                vec![
                    Value::from_json_str(r#"{"value":3}"#).unwrap(),
                    Value::from_json_str(r#"{"value":8}"#).unwrap(),
                    Value::Set(Rc::new([Value::from(3)].into_iter().collect())),
                    Value::Set(Rc::new([Value::from(8)].into_iter().collect())),
                ]
                .into(),
            )),
        )],
    );
}

#[test]
fn default_only_function_has_arity_and_lexical_parameters() {
    let module = r#"package defaults
        default f(x) := [y | y := x]
        result := [f(3), f(8)]
    "#;
    let program = compile(module, &[]);
    let function = program
        .rule_infos
        .iter()
        .find(|rule| rule.name == "data.defaults.f")
        .unwrap();
    assert_eq!(function.function_info.as_ref().unwrap().num_params, 1);
    assert!(function.default_entry_point.is_some());
    assert!(function.default_literal_index.is_none());
    assert_reusable(
        module,
        &[("{}", "{}", Value::from_json_str("[[3],[8]]").unwrap())],
    );
}

#[test]
fn default_only_function_output_arguments_are_scheduled() {
    assert_reusable(
        r#"package defaults
        default f(x) := [y | y := x]
        result := output if { f(3, output) }
        "#,
        &[("{}", "{}", Value::from_json_str("[3]").unwrap())],
    );
}

#[test]
fn imported_default_function_uses_its_own_module_scope() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "library.rego".into(),
            "package library\nbase := 5\ndefault f(x) := [y | y := x + base]".into(),
        )
        .unwrap();
    engine
        .add_policy(
            "defaults.rego".into(),
            "package defaults\nimport data.library.f\nresult := [f(3), data.library.f(8)]".into(),
        )
        .unwrap();
    let expected = Value::from_json_str("[[8],[13]]").unwrap();
    let policy = engine.compile_with_entrypoint(&Rc::from(ENTRY)).unwrap();
    let program = Compiler::compile_from_policy(&policy, &[ENTRY]).unwrap();
    for program in round_trips(program) {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(vm.execute_entry_point_by_name(ENTRY).unwrap(), expected);
        }
    }
}

#[test]
fn constant_defaults_keep_literal_fast_path_and_false_is_defined() {
    let module = r#"package defaults
        default f(x) := 7
        f(x) := x if x > 10
        default flag(x) := true
        flag(x) := false if x == 0
        result := [f(3), f(30), flag(0)]
    "#;
    let program = compile(module, &[]);
    let function = program
        .rule_infos
        .iter()
        .find(|rule| rule.name == "data.defaults.f")
        .unwrap();
    assert!(function.default_literal_index.is_some());
    assert!(function.default_entry_point.is_none());
    assert_reusable(
        module,
        &[("{}", "{}", Value::from_json_str("[7,30,false]").unwrap())],
    );
}

#[test]
fn undefined_function_arguments_do_not_select_defaults() {
    for default in ["7", "[y | y := x]"] {
        let module =
            format!("package defaults\ndefault f(x) := {default}\nresult := f(input.missing)");
        assert_reusable(&module, &[("{}", "{}", Value::Undefined)]);
    }
}

#[test]
fn default_functions_resume_in_their_parameter_window() {
    let module = r#"package defaults
        default f(x) := [y | y := lookup(x)]
        result := [f(3), f(8)]
    "#;
    for program in round_trips(compile(module, &[("lookup", 1)])) {
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.execute_entry_point_by_name(ENTRY).unwrap();
        for number in [3, 8] {
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { argument, .. },
                    ..
                } if argument == &Value::Array(Rc::new(vec![Value::from(number)].into()))
            ));
            vm.resume(Some(Value::from(number * 10))).unwrap();
        }
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Completed { result }
                if result == &Value::from_json_str("[[30],[80]]").unwrap()
        ));
    }
}

#[test]
fn dynamic_default_recursion_preserves_mode_and_allows_reuse() {
    let module = r#"package defaults
        default p := [y | y := data.defaults[input.name]]
        safe := 42
        result := p
    "#;
    for program in round_trips(compile(module, &[])) {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(false);
            for _ in 0..2 {
                vm.set_input(Value::from_json_str(r#"{"name":"p"}"#).unwrap());
                assert!(matches!(
                    vm.execute_entry_point_by_name(ENTRY),
                    Err(VmError::RecursiveRuleEvaluation { .. })
                ));
                assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
                assert_eq!(vm.get_execution_mode(), mode);
                vm.set_input(Value::from_json_str(r#"{"name":"safe"}"#).unwrap());
                assert_eq!(
                    vm.execute_entry_point_by_name(ENTRY).unwrap(),
                    Value::from_json_str("[42]").unwrap()
                );
                assert_eq!(vm.get_execution_mode(), mode);
            }
        }
    }
}

#[test]
fn dynamic_default_recursion_after_resume_allows_reuse() {
    let module = r#"package defaults
        default p := [y | name := lookup(input.name); y := data.defaults[name]]
        safe := 42
        result := p
    "#;
    for program in round_trips(compile(module, &[("lookup", 1)])) {
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.set_strict_builtin_errors(false);
        for (name, recursive) in [("p", true), ("safe", false)] {
            vm.set_input(Value::from_json_str(&format!(r#"{{"name":"{name}"}}"#)).unwrap());
            vm.execute_entry_point_by_name(ENTRY).unwrap();
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { argument, .. },
                    ..
                } if argument == &Value::from_json_str(&format!(r#"["{name}"]"#)).unwrap()
            ));
            let result = vm.resume(Some(Value::from(name)));
            if recursive {
                assert!(matches!(
                    result,
                    Err(VmError::RecursiveRuleEvaluation { .. })
                ));
                assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
            } else {
                assert_eq!(result.unwrap(), Value::from_json_str("[42]").unwrap());
                assert!(matches!(
                    vm.execution_state(),
                    ExecutionState::Completed { result }
                        if result == &Value::from_json_str("[42]").unwrap()
                ));
            }
            assert_eq!(vm.get_execution_mode(), ExecutionMode::Suspendable);
        }
    }
}

#[test]
fn namespace_selected_defaults_resume_after_loading_and_reuse() {
    let module = r#"package defaults
        x := "global"
        default leaf := [lookup("leaf") | true]
        default group.f(x) := 7
        default group.a := [lookup(x) | true]
        default group.b := [lookup("b") | true]
        result := data.defaults[input.name]
    "#;
    for program in round_trips(compile(module, &[("lookup", 1)])) {
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.set_strict_builtin_errors(false);
        for (name, calls, expected) in [
            ("leaf", vec![("leaf", 7)], "[7]"),
            (
                "group",
                vec![("global", 11), ("b", 13)],
                r#"{"a":[11],"b":[13]}"#,
            ),
            ("leaf", vec![("leaf", 17)], "[17]"),
        ] {
            vm.set_input(Value::from_json_str(&format!(r#"{{"name":"{name}"}}"#)).unwrap());
            vm.execute_entry_point_by_name(ENTRY).unwrap();
            for (argument, response) in calls {
                assert!(matches!(
                    vm.execution_state(),
                    ExecutionState::Suspended {
                        reason: SuspendReason::HostAwait { argument: actual, .. },
                        ..
                    } if actual == &Value::from_json_str(&format!(r#"["{argument}"]"#)).unwrap()
                ));
                vm.resume(Some(Value::from(response))).unwrap();
            }
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Completed { result }
                    if result == &Value::from_json_str(expected).unwrap()
            ));
            assert_eq!(vm.get_execution_mode(), ExecutionMode::Suspendable);
        }
    }
}

#[test]
fn replacing_program_invalidates_suspended_default_execution() {
    let program = compile(
        "package defaults\ndefault result := [lookup(\"value\") | true]",
        &[("lookup", 1)],
    );
    let mut bytes = compile("package defaults\nresult := 7", &[])
        .serialize_binary()
        .unwrap();
    bytes[4..8].copy_from_slice(&6u32.to_le_bytes());
    let legacy = match Program::deserialize_binary(&bytes).unwrap() {
        DeserializationResult::Partial(program) => Arc::new(program),
        DeserializationResult::Complete(_) => panic!("version 6 must be recompiled"),
    };
    for program in round_trips(program) {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.execute_entry_point_by_name(ENTRY).unwrap();
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Suspended { .. }
        ));

        vm.load_program(legacy.clone());
        assert!(matches!(vm.execution_state(), ExecutionState::Ready));
        assert!(matches!(
            vm.resume(Some(Value::Bool(true))),
            Err(VmError::InvalidResumeState { .. })
        ));
        assert!(matches!(
            vm.execute(),
            Err(VmError::Internal { ref message, .. })
                if message == "program requires recompilation"
        ));

        vm.load_program(program);
        vm.execute_entry_point_by_name(ENTRY).unwrap();
        assert_eq!(
            vm.resume(Some(Value::Bool(false))).unwrap(),
            Value::from_json_str("[false]").unwrap()
        );
        assert_eq!(vm.get_execution_mode(), ExecutionMode::Suspendable);
    }
}

#[test]
fn default_bytecode_metadata_is_validated() {
    let mut program = (*compile(
        "package defaults\ndefault result := [x | x := input.x]",
        &[],
    ))
    .clone();
    let rule = program.rule_infos.first_mut().unwrap();
    rule.default_entry_point = Some(u32::MAX);
    assert!(program.validate_limits().is_err());
    assert!(program.serialize_binary().is_err());
    assert!(program.serialize_json().is_err());
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for by_name in [true, false] {
            let mut vm = RegoVM::new();
            vm.load_program(Arc::new(program.clone()));
            vm.set_execution_mode(mode);
            let result = if by_name {
                vm.execute_entry_point_by_name(ENTRY)
            } else {
                vm.execute()
            };
            assert!(
                matches!(result, Err(VmError::Internal { ref message, .. })
                    if message == "Invalid default bytecode for rule 'data.defaults.result'"),
                "{mode:?}, by_name={by_name}: {result:?}"
            );
            assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
        }
    }
}

#[test]
fn malformed_serialized_default_metadata_is_rejected() {
    let program = compile(
        "package defaults\ndefault result := [x | x := input.x]",
        &[],
    );
    let mut json: serde_json::Value =
        serde_json::from_str(&program.serialize_json().unwrap()).unwrap();
    for invalid in [
        serde_json::json!(u32::MAX),
        serde_json::json!(0),
        serde_json::json!(-1),
        serde_json::json!("7"),
        serde_json::json!(4294967296u64),
    ] {
        json["rule_infos"][0]["default_entry_point"] = invalid;
        assert!(Program::deserialize_json(&json.to_string()).is_err());
    }
}

#[test]
fn legacy_json_defaults_require_recompilation_before_execution() {
    let program = compile("package defaults\ndefault result := 7", &[]);
    for current in round_trips(program.clone()) {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(current.clone());
            vm.set_execution_mode(mode);
            assert_eq!(vm.execute().unwrap(), Value::from(7));
        }
    }
    let mut json: serde_json::Value =
        serde_json::from_str(&program.serialize_json().unwrap()).unwrap();
    json["rule_infos"][0]
        .as_object_mut()
        .unwrap()
        .remove("default_entry_point");
    let legacy = Arc::new(Program::deserialize_json(&json.to_string()).unwrap());
    assert!(legacy.needs_recompilation);
    assert_eq!(legacy.sources.len(), program.sources.len());
    let repacked = match Program::deserialize_binary(&legacy.serialize_binary().unwrap()).unwrap() {
        DeserializationResult::Partial(program) => Arc::new(program),
        DeserializationResult::Complete(_) => {
            panic!("reserialization must not bypass recompilation")
        }
    };
    for legacy in [legacy, repacked] {
        assert!(legacy.needs_recompilation);
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            for by_name in [true, false] {
                let mut vm = RegoVM::new();
                vm.load_program(legacy.clone());
                vm.set_execution_mode(mode);
                let result = if by_name {
                    vm.execute_entry_point_by_name(ENTRY)
                } else {
                    vm.execute()
                };
                assert!(
                    matches!(result, Err(VmError::Internal { ref message, .. })
                        if message == "program requires recompilation"),
                    "{mode:?}, by_name={by_name}: {result:?}"
                );
                assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
            }
        }
    }
}

#[test]
fn legacy_json_omitted_function_defaults_require_recompilation() {
    let program = compile(
        "package defaults\ndefault f(x) := 7\nf(x) := x if x > 10\nresult := f(3)",
        &[],
    );
    let mut json: serde_json::Value =
        serde_json::from_str(&program.serialize_json().unwrap()).unwrap();
    for rule in json["rule_infos"].as_array_mut().unwrap() {
        rule.as_object_mut().unwrap().remove("default_entry_point");
        rule["default_literal_index"] = serde_json::Value::Null;
    }
    let legacy = Arc::new(Program::deserialize_json(&json.to_string()).unwrap());
    assert!(legacy.needs_recompilation);
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(legacy.clone());
        vm.set_execution_mode(mode);
        assert!(matches!(
            vm.execute_entry_point_by_name(ENTRY),
            Err(VmError::Internal { ref message, .. })
                if message == "program requires recompilation"
        ));
    }
}

#[test]
fn default_only_functions_enforce_call_arity() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "defaults.rego".into(),
            "package defaults\ndefault f(x) := 7\nresult := f(3, 4, 5)".into(),
        )
        .unwrap();
    let result = engine.compile_with_entrypoint(&Rc::from(ENTRY));
    if let Ok(policy) = result {
        assert!(Compiler::compile_from_policy(&policy, &[ENTRY]).is_err());
    }
}

#[test]
fn previous_binary_version_preserves_recompilation_artifacts() {
    for module in [
        "package defaults\ndefault result := true",
        "package defaults\nresult := 7",
    ] {
        let program = compile(module, &[]);
        let mut bytes = program.serialize_binary().unwrap();
        bytes[4..8].copy_from_slice(&6u32.to_le_bytes());
        match Program::deserialize_binary(&bytes).unwrap() {
            DeserializationResult::Partial(old) => {
                assert!(old.needs_recompilation);
                assert_eq!(old.sources.len(), program.sources.len());
                assert_eq!(old.entry_points, program.entry_points);
                for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                    for by_name in [true, false] {
                        let mut vm = RegoVM::new();
                        vm.load_program(Arc::new(old.clone()));
                        vm.set_execution_mode(mode);
                        let error = if by_name {
                            vm.execute_entry_point_by_name(ENTRY)
                        } else {
                            vm.execute_entry_point_by_index(0)
                        }
                        .unwrap_err();
                        assert!(matches!(
                            error,
                            VmError::Internal { ref message, .. }
                                if message == "program requires recompilation"
                        ));
                        assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
                    }
                }
            }
            DeserializationResult::Complete(_) => panic!("version 6 must be recompiled"),
        }
    }
}
