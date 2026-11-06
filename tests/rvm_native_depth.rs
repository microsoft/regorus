// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Rc, Value};
use serde::Deserialize;
use std::sync::Arc;

mod native_depth_support;

#[derive(Deserialize)]
struct Scenarios {
    cases: Vec<Scenario>,
}

#[derive(Clone, Deserialize)]
struct Scenario {
    note: String,
    modules: Vec<String>,
    query: String,
    input: Option<Value>,
    execution_mode: Option<String>,
    want_error: Option<String>,
    want_result: Option<Value>,
}

fn compile_case(case: &Scenario) -> Arc<Program> {
    let mut engine = Engine::new();
    for (index, module) in case.modules.iter().enumerate() {
        engine
            .add_policy(format!("native-depth-{index}.rego"), module.clone())
            .unwrap();
    }
    let policy = engine
        .compile_with_entrypoint(&Rc::from(case.query.as_str()))
        .unwrap();
    Compiler::compile_from_policy(&policy, &[&case.query, "data.probe.safe"]).unwrap()
}

fn check_lifecycle(case: &Scenario, step_mode: bool) {
    eprintln!("lifecycle: {}, step={step_mode}", case.note);
    let mut vm = RegoVM::new();
    vm.load_program(compile_case(case));
    vm.set_execution_mode(match case.execution_mode.as_deref() {
        None => ExecutionMode::RunToCompletion,
        Some("suspendable") => ExecutionMode::Suspendable,
        other => panic!("unsupported execution mode: {other:?}"),
    });
    vm.set_input(case.input.clone().unwrap_or(Value::Null));
    for _ in 0..if case.want_error.is_some() { 2 } else { 1 } {
        vm.set_step_mode(step_mode);
        let mut result = vm.execute_entry_point_by_name(&case.query);
        if step_mode {
            let mut resumed_active_rule = false;
            for _ in 0..10_000 {
                if !matches!(vm.execution_state(), ExecutionState::Suspended { .. }) {
                    break;
                }
                resumed_active_rule |= !vm.get_call_stack().is_empty();
                result = vm.resume(None);
            }
            assert!(resumed_active_rule, "must resume inside an active rule");
        }
        if case.want_error.is_some() {
            assert!(
                matches!(
                    result,
                    Err(VmError::RuleCallDepthExceeded { limit: 16, .. })
                ),
                "{result:?}"
            );
            assert!(matches!(vm.execution_state(), ExecutionState::Error { .. }));
        } else {
            assert_eq!(Some(result.unwrap()), case.want_result);
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Completed { .. }
            ));
        }
        assert!(vm.get_call_stack().is_empty());
        vm.set_step_mode(false);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
            Value::from(7)
        );
    }
}

fn check_configuration(scenarios: &Scenarios) {
    let case = scenarios
        .cases
        .iter()
        .find(|case| case.note == "native-depth/rules-17-error-not-default")
        .unwrap();
    let program = compile_case(case);
    let mut configured = RegoVM::new();
    let mut default = RegoVM::new();
    assert_eq!(configured.max_native_rule_call_depth(), 16);
    configured.set_max_native_rule_call_depth(17);
    for _ in 0..2 {
        configured.load_program(program.clone());
        assert_eq!(configured.max_native_rule_call_depth(), 17);
        assert_eq!(
            configured.execute_entry_point_by_name(&case.query).unwrap(),
            Value::from(42)
        );
        assert_eq!(configured.max_native_rule_call_depth(), 17);
        assert_eq!(
            configured
                .execute_entry_point_by_name("data.probe.safe")
                .unwrap(),
            Value::from(7)
        );
        assert_eq!(configured.max_native_rule_call_depth(), 17);
        default.load_program(program.clone());
        assert_eq!(default.max_native_rule_call_depth(), 16);
        assert!(matches!(
            default.execute_entry_point_by_name(&case.query),
            Err(VmError::RuleCallDepthExceeded { limit: 16, .. })
        ));
    }

    configured.set_max_native_rule_call_depth(1);
    assert!(matches!(
        configured.execute_entry_point_by_name(&case.query),
        Err(VmError::RuleCallDepthExceeded { limit: 1, .. })
    ));
    assert_eq!(
        configured
            .execute_entry_point_by_name("data.probe.safe")
            .unwrap(),
        Value::from(7)
    );
    configured.set_max_native_rule_call_depth(0);
    assert!(matches!(
        configured.execute_entry_point_by_name("data.probe.safe"),
        Err(VmError::RuleCallDepthExceeded { limit: 0, .. })
    ));
    configured.set_execution_mode(ExecutionMode::Suspendable);
    assert_eq!(
        configured.execute_entry_point_by_name(&case.query).unwrap(),
        Value::from(42)
    );

    let case = scenarios
        .cases
        .iter()
        .find(|case| case.note == "native-depth/virtual-leaf-suspendable-16-succeed")
        .unwrap();
    configured.load_program(compile_case(case));
    configured.set_input(case.input.clone().unwrap());
    configured.set_max_native_rule_call_depth(16);
    configured.set_step_mode(true);
    configured.execute_entry_point_by_name(&case.query).unwrap();
    configured.set_max_native_rule_call_depth(0);
    let mut result = Ok(Value::Undefined);
    for _ in 0..10_000 {
        if !matches!(
            configured.execution_state(),
            ExecutionState::Suspended { .. }
        ) {
            break;
        }
        result = configured.resume(None);
    }
    assert!(matches!(
        result,
        Err(VmError::RuleCallDepthExceeded { limit: 0, .. })
    ));
    assert!(matches!(
        configured.execution_state(),
        ExecutionState::Error { .. }
    ));
    assert!(configured.get_call_stack().is_empty());
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn native_depth_lifecycle() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess("native_depth_lifecycle");
        return;
    }

    let scenarios: Scenarios =
        yaml_serde::from_str(include_str!("rvm/rego/cases/native_depth.yaml")).unwrap();
    check_configuration(&scenarios);
    for case in &scenarios.cases {
        if case.want_error.is_some() {
            check_lifecycle(case, false);
        }
        if case.execution_mode.as_deref() == Some("suspendable")
            && (case.want_error.is_some() || case.note.contains("virtual-"))
        {
            check_lifecycle(case, true);
        }
    }
}

fn on_execution_stack(test_name: &str, check: fn()) {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess(test_name);
        return;
    }
    std::thread::Builder::new()
        .stack_size(1_500_000)
        .spawn(check)
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn expression_structure_limits() {
    on_execution_stack("expression_structure_limits", || {
        use regorus::unstable::{Lexer, Parser, Source, TokenKind};

        fn expression(text: &str) -> anyhow::Result<()> {
            let source = Source::from_contents("expression.rego".into(), text.into())?;
            let mut parser = Parser::new(&source)?;
            parser.enable_rego_v1()?;
            parser.parse_expr()?;
            Ok(())
        }

        for (open, close) in [
            ("(", ")"),
            ("[", "]"),
            ("{0:", "}"),
            ("count(", ")"),
            ("input[", "]"),
            ("- ", ""),
        ] {
            let accepted = format!("{}0{}", open.repeat(31), close.repeat(31));
            expression(&accepted).unwrap();
            let rejected = format!("{}0{}", open.repeat(32), close.repeat(32));
            let error = expression(&rejected).unwrap_err();
            assert!(error.to_string().contains("nesting too deep"), "{error}");
            let malformed = format!("{}@", open.repeat(32));
            assert!(expression(&malformed).is_err());
        }
        for operator in [
            " + ",
            " * ",
            " & ",
            " | ",
            " == ",
            " in ",
            #[cfg(feature = "rego-extensions")]
            " or ",
        ] {
            let accepted = vec!["0"; 32].join(operator);
            expression(&accepted).unwrap();
            let rejected = vec!["0"; 33].join(operator);
            let error = expression(&rejected).unwrap_err();
            assert!(error.to_string().contains("nesting too deep"), "{error}");
        }
        expression(&format!("input{}", ".field".repeat(31))).unwrap();
        assert!(expression(&format!("input{}", ".field".repeat(32))).is_err());
        expression(&format!("input{}", "[0]".repeat(31))).unwrap();
        assert!(expression(&format!("input{}", "[0]".repeat(32))).is_err());
        expression(&format!("({}) * 2", vec!["1"; 31].join(" + "))).unwrap();
        assert!(expression(&format!("({}) * 2", vec!["1"; 32].join(" + "))).is_err());

        for (open, close) in [("[", " | true]"), ("{", " | true}"), ("{0:", " | true}")] {
            expression(&format!("{}0{}", open.repeat(30), close.repeat(30))).unwrap();
            assert!(expression(&format!("{}0{}", open.repeat(31), close.repeat(31))).is_err());
        }
        for count in [31, 32] {
            let mut engine = Engine::new();
            let result = engine.add_policy(
                "references.rego".into(),
                format!("package probe\nr{} := 0", ".field".repeat(count)),
            );
            assert_eq!(result.is_ok(), count == 31);
        }

        for count in [30, 31] {
            let source = Source::from_contents(
                "query.rego".into(),
                format!(
                    "{}true{}",
                    "every x in [0] { ".repeat(count),
                    " }".repeat(count)
                ),
            )
            .unwrap();
            let mut parser = Parser::new(&source).unwrap();
            parser.enable_rego_v1().unwrap();
            let result = parser.parse_user_query();
            if count == 30 {
                result.unwrap();
            } else {
                assert!(result.unwrap_err().to_string().contains("nesting too deep"));
            }
        }

        // Lookahead must leave the token stream and source positions unchanged.
        let text = format!("{}0{}", "set(\n".repeat(256), ")".repeat(256));
        let source = Source::from_contents("tokens.rego".into(), text).unwrap();
        let mut lexer = Lexer::new(&source);
        let mut tokens = 0;
        while lexer.next_token().unwrap().0 != TokenKind::Eof {
            tokens += 1;
        }
        assert_eq!(tokens, 769);
        expression("[set() | true]").unwrap();
    });
}

fn dependency_module(count: usize, functions: bool) -> String {
    let mut module = String::from("package probe\nsafe := 7\n");
    for index in 0..count {
        let head = if functions {
            format!("f{index}(x)")
        } else {
            format!("r{index}")
        };
        let output = if index + 1 == count {
            if functions {
                "x".into()
            } else {
                "42".into()
            }
        } else if functions {
            format!("f{}(x)", index + 1)
        } else {
            format!("r{}", index + 1)
        };
        module.push_str(&format!("{head} := {output}\n"));
    }
    if functions {
        module.push_str("r0 := f0(42)\n");
    }
    module
}

fn virtual_dependency_modules(count: usize) -> Vec<String> {
    let mut modules = vec![String::from(
        "package probe\nsafe := 7\nr0 := count(data.probe.v0)\n",
    )];
    let suffix = vec!["field"; 28].join(".");
    for index in 0..count {
        let output = if index + 1 == count {
            "42".into()
        } else {
            format!("count(data.probe.v{})", index + 1)
        };
        modules.push(format!(
            "package probe.v{index}.{suffix}\nleaf := {output}\n"
        ));
    }
    modules
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn execution_structure_limits() {
    on_execution_stack("execution_structure_limits", || {
        for functions in [false, true] {
            let accepted = if functions { 20 } else { 21 };
            for count in [8, accepted, accepted + 1] {
                let mut engine = Engine::new();
                engine
                    .add_policy(
                        "dependencies.rego".into(),
                        dependency_module(count, functions),
                    )
                    .unwrap();
                engine.set_strict_builtin_errors(false);
                for _ in 0..2 {
                    let result = engine.eval_rule("data.probe.r0".into());
                    if count <= accepted {
                        assert_eq!(result.unwrap(), Value::from(42));
                    } else {
                        let error = result.unwrap_err();
                        assert!(
                            error.to_string().contains("native evaluation nesting"),
                            "{error}"
                        );
                    }
                    assert_eq!(
                        engine.eval_rule("data.probe.safe".into()).unwrap(),
                        Value::from(7)
                    );
                }
            }
        }

        for count in [8, 16] {
            let mut engine = Engine::new();
            for (index, module) in virtual_dependency_modules(count).into_iter().enumerate() {
                engine
                    .add_policy(format!("virtual-{index}.rego"), module)
                    .unwrap();
            }
            let result = engine.eval_rule("data.probe.r0".into());
            if count == 8 {
                assert_eq!(result.unwrap(), Value::from(1));
            } else {
                assert!(result
                    .unwrap_err()
                    .to_string()
                    .contains("native evaluation nesting"));
            }
            assert_eq!(
                engine.eval_rule("data.probe.safe".into()).unwrap(),
                Value::from(7)
            );
        }
        for count in [2, 3] {
            let mut module = String::from("package probe\nr0 := f0(input)\nsafe := 7\n");
            for index in 0..count {
                if index + 1 == count {
                    module.push_str(&format!("f{index}(x) := 42\n"));
                } else {
                    let pattern = format!("{}f{}(x){}", "[".repeat(24), index + 1, "]".repeat(24));
                    module.push_str(&format!("f{index}(x) := 42 if {{ [a, {pattern}] = x }}\n"));
                }
            }
            let mut nested = Value::from(42);
            for _ in 0..24 {
                nested = Value::from(vec![nested]);
            }
            let mut engine = Engine::new();
            engine.set_input(Value::from(vec![Value::from(0), nested]));
            engine.add_policy("bindings.rego".into(), module).unwrap();
            let result = engine.eval_rule("data.probe.r0".into());
            if count == 2 {
                assert_eq!(result.unwrap(), Value::from(42));
            } else {
                assert!(result
                    .unwrap_err()
                    .to_string()
                    .contains("native evaluation nesting"));
            }
            assert_eq!(
                engine.eval_rule("data.probe.safe".into()).unwrap(),
                Value::from(7)
            );
        }

        for count in [60, 61, 128] {
            let mut engine = Engine::new();
            let statements = (0..count)
                .map(|index| format!("some x{index} in [0]"))
                .collect::<Vec<_>>()
                .join(";\n");
            let policy = format!("package probe\nsafe := 7\nr0 := 42 if {{ {statements} }}");
            engine.add_policy("statements.rego".into(), policy).unwrap();
            assert_eq!(
                engine.eval_rule("data.probe.r0".into()).unwrap(),
                Value::from(42)
            );
            assert_eq!(
                engine.eval_rule("data.probe.safe".into()).unwrap(),
                Value::from(7)
            );
        }

        for count in [20, 21, 128] {
            let mut engine = Engine::new();
            engine.set_input_json(r#"{"items":[0]}"#).unwrap();
            let statements = vec!["input.items[_] == 0"; count].join(";\n");
            engine
                .add_policy(
                    "loops.rego".into(),
                    format!("package probe\nr0 := 42 if {{ {statements} }}"),
                )
                .unwrap();
            assert_eq!(
                engine.eval_rule("data.probe.r0".into()).unwrap(),
                Value::from(42)
            );
        }

        for statements in [
            (0..80)
                .map(|index| format!("some x{index} in [0]"))
                .collect::<Vec<_>>()
                .join(";\n"),
            vec!["input.items[_] == 0"; 80].join(";\n"),
        ] {
            let mut engine = Engine::new();
            engine
                .add_policy(
                    "registers.rego".into(),
                    format!("package probe\nr0 := 42 if {{ {statements} }}"),
                )
                .unwrap();
            let policy = engine
                .compile_with_entrypoint(&Rc::from("data.probe.r0"))
                .unwrap();
            assert!(Compiler::compile_from_policy(&policy, &["data.probe.r0"])
                .unwrap_err()
                .to_string()
                .contains("Register overflow"));
        }

        // Default comprehensions still propagate genuinely nested function
        // errors; wide sequential some-in bodies are no longer native nesting.
        let statements = "some x in f0(0)";
        let dependencies = dependency_module(24, true).replace("r0 := f0(42)\n", "");
        for function in [false, true] {
            let mut engine = Engine::new();
            let defaults = if function {
                format!("default f(x) := [42 | {statements}]\nr0 := f(0)")
            } else {
                format!("default r0 := [42 | {statements}]")
            };
            engine
                .add_policy(
                    "defaults.rego".into(),
                    format!("{dependencies}\n{defaults}"),
                )
                .unwrap();
            engine.set_strict_builtin_errors(false);
            assert!(engine
                .eval_rule("data.probe.r0".into())
                .unwrap_err()
                .to_string()
                .contains("native evaluation nesting"));
            assert_eq!(
                engine.eval_rule("data.probe.safe".into()).unwrap(),
                Value::from(7)
            );
            if !function {
                let policy = engine
                    .compile_with_entrypoint(&Rc::from("data.probe.r0"))
                    .unwrap();
                assert!(Compiler::compile_from_policy(&policy, &["data.probe.r0"])
                    .unwrap_err()
                    .to_string()
                    .contains("native evaluation nesting"));
            }
        }
        let mut engine = Engine::new();
        engine
            .add_policy(
                "partial.rego".into(),
                format!(
                    "{}\npartial[data.probe.r0] contains 1 if {{ false }}",
                    dependency_module(21, true)
                ),
            )
            .unwrap();
        engine.set_strict_builtin_errors(false);
        let error = engine.eval_rule("data.probe.partial".into()).unwrap_err();
        assert!(
            error.to_string().contains("native evaluation nesting"),
            "{error}"
        );

        let mut engine = Engine::new();
        #[cfg(feature = "coverage")]
        engine.set_enable_coverage(true);
        let sum = vec!["1"; 32].join(" + ");
        engine
            .add_policy(
                "expressions.rego".into(),
                format!("package probe\nsum := {sum}\nmissing := input.missing\nsafe := 7"),
            )
            .unwrap();
        assert_eq!(
            engine.eval_rule("data.probe.sum".into()).unwrap(),
            Value::from(32)
        );
        assert_eq!(
            engine.eval_rule("data.probe.missing".into()).unwrap(),
            Value::Undefined
        );
        #[cfg(feature = "coverage")]
        assert!(!engine.get_coverage_report().unwrap().files.is_empty());
        let policy = engine
            .compile_with_entrypoint(&Rc::from("data.probe.sum"))
            .unwrap();
        let program =
            Compiler::compile_from_policy(&policy, &["data.probe.sum", "data.probe.missing"])
                .unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.sum").unwrap(),
            Value::from(32)
        );
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.missing")
                .unwrap(),
            Value::Undefined
        );

        let pattern = format!("{}x{}", "[".repeat(29), "]".repeat(29));
        let nested = format!("{}42{}", "[".repeat(29), "]".repeat(29));
        let mut engine = Engine::new();
        engine
            .add_policy(
                "patterns.rego".into(),
                format!("package probe\nr0 := x if {{ {pattern} := {nested} }}"),
            )
            .unwrap();
        assert_eq!(
            engine.eval_rule("data.probe.r0".into()).unwrap(),
            Value::from(42)
        );
        let policy = engine
            .compile_with_entrypoint(&Rc::from("data.probe.r0"))
            .unwrap();
        assert!(format!("{policy:?}").contains("lhs_plan: Array"));
        let program = Compiler::compile_from_policy(&policy, &["data.probe.r0"]).unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.r0").unwrap(),
            Value::from(42)
        );

        let mut input = Value::from(0);
        for _ in 0..2048 {
            input = Value::from(vec![input]);
        }
        let mut engine = Engine::new();
        engine.set_gather_prints(true);
        engine.set_input(input.clone());
        engine
            .add_policy(
                "values.rego".into(),
                "package probe\nr0 := [input]\nprinted if { print(input) }".into(),
            )
            .unwrap();
        assert_eq!(
            engine.eval_rule("data.probe.printed".into()).unwrap(),
            Value::from(true)
        );
        let expected = format!("{}0{}", "[".repeat(2048), "]".repeat(2048));
        assert!(engine.take_prints().unwrap()[0].ends_with(&expected));
        let expected = Value::from(vec![input.clone()]);
        assert_eq!(engine.eval_rule("data.probe.r0".into()).unwrap(), expected);
        let policy = engine
            .compile_with_entrypoint(&Rc::from("data.probe.r0"))
            .unwrap();
        let program = Compiler::compile_from_policy(&policy, &["data.probe.r0"]).unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program);
        vm.set_input(input);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.r0").unwrap(),
            expected
        );
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn native_configuration_limits() {
    on_execution_stack("native_configuration_limits", || {
        let case = Scenario {
            note: "configuration".into(),
            modules: vec![dependency_module(17, false)],
            query: "data.probe.r0".into(),
            input: None,
            execution_mode: None,
            want_error: None,
            want_result: None,
        };
        let program = compile_case(&case);
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_max_native_rule_call_depth(17);
        assert_eq!(
            vm.execute_entry_point_by_name(&case.query).unwrap(),
            Value::from(42)
        );
        for (modules, expected) in [
            (vec![dependency_module(16, true)], Value::from(42)),
            (virtual_dependency_modules(16), Value::from(1)),
        ] {
            let case = Scenario {
                modules,
                ..case.clone()
            };
            let mut configured = RegoVM::new();
            let program = compile_case(&case);
            configured.load_program(program);
            configured.set_max_native_rule_call_depth(17);
            assert_eq!(
                configured.execute_entry_point_by_name(&case.query).unwrap(),
                expected
            );
        }
        let mut deeper = RegoVM::new();
        let case_deeper = Scenario {
            modules: virtual_dependency_modules(17),
            ..case.clone()
        };
        deeper.load_program(compile_case(&case_deeper));
        deeper.set_max_native_rule_call_depth(17);
        assert!(matches!(
            deeper.execute_entry_point_by_name(&case_deeper.query),
            Err(VmError::RuleCallDepthExceeded { limit: 17, .. })
        ));
        let package = vec!["part"; 32].join(".");
        for definition in ["r0 := 0", "default r0 := 0"] {
            let mut engine = Engine::new();
            engine
                .add_policy(
                    "paths.rego".into(),
                    format!("package {package}\n{definition}"),
                )
                .unwrap();
            let entrypoint = format!("data.{package}.r0");
            let policy = engine
                .compile_with_entrypoint(&Rc::from(entrypoint.as_str()))
                .unwrap();
            assert!(Compiler::compile_from_policy(&policy, &[&entrypoint])
                .unwrap_err()
                .to_string()
                .contains("Rule path depth exceeds maximum"));
        }
        for limit in [18, usize::MAX] {
            vm.load_program(program.clone());
            vm.set_max_native_rule_call_depth(limit);
            assert!(matches!(
                vm.execute_entry_point_by_name(&case.query),
                Err(VmError::RuleCallDepthExceeded { limit: 17, .. })
            ));
            assert_eq!(vm.max_native_rule_call_depth(), limit);
            assert!(vm.get_call_stack().is_empty());
            vm.set_max_native_rule_call_depth(16);
            assert_eq!(
                vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
                Value::from(7)
            );
        }
        vm.set_max_native_rule_call_depth(usize::MAX);
        vm.set_execution_mode(ExecutionMode::Suspendable);
        assert_eq!(
            vm.execute_entry_point_by_name(&case.query).unwrap(),
            Value::from(42)
        );

        let scenarios: Scenarios =
            yaml_serde::from_str(include_str!("rvm/rego/cases/native_depth.yaml")).unwrap();
        let case = scenarios
            .cases
            .iter()
            .find(|case| case.note == "native-depth/virtual-leaf-suspendable-16-succeed")
            .unwrap();
        vm.load_program(compile_case(case));
        vm.set_input(case.input.clone().unwrap());
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.set_max_native_rule_call_depth(16);
        vm.set_step_mode(true);
        vm.execute_entry_point_by_name(&case.query).unwrap();
        vm.set_max_native_rule_call_depth(18);
        let mut result = Ok(Value::Undefined);
        for _ in 0..10_000 {
            if !matches!(vm.execution_state(), ExecutionState::Suspended { .. }) {
                break;
            }
            result = vm.resume(None);
        }
        assert!(matches!(
            result,
            Err(VmError::RuleCallDepthExceeded { limit: 17, .. })
        ));
        assert!(vm.get_call_stack().is_empty());
        vm.set_max_native_rule_call_depth(17);
        vm.set_step_mode(false);
        assert_eq!(
            vm.execute_entry_point_by_name("data.probe.safe").unwrap(),
            Value::from(7)
        );
    });
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn authored_expression_lifecycle() {
    on_execution_stack("authored_expression_lifecycle", || {
        use regorus::unstable::{Expr, Literal, LiteralStmt, Query, Ref, Source, Span};
        let source = Source::from_contents("ast.rego".into(), "0".into()).unwrap();
        let span = Span {
            source,
            line: 1,
            col: 1,
            start: 0,
            end: 1,
        };
        let leaf = || {
            Ref::new(Expr::Null {
                span: span.clone(),
                value: Value::Null,
                eidx: 0,
            })
        };
        let mut accepted = leaf();
        for _ in 0..31 {
            accepted = Ref::new(Expr::Array {
                span: span.clone(),
                items: vec![accepted],
                eidx: 0,
            });
        }
        assert!(!format!("{accepted:?}").contains("cannot be formatted"));
        #[cfg(feature = "ast")]
        serde_json::to_string(&accepted).unwrap();

        for value_depth in [64, 65] {
            let mut value = Value::Null;
            for _ in 0..value_depth {
                value = Value::from(vec![value]);
            }
            let mut expr = Ref::new(Expr::Null {
                span: span.clone(),
                value,
                eidx: 0,
            });
            for _ in 0..31 {
                expr = Ref::new(Expr::Array {
                    span: span.clone(),
                    items: vec![expr],
                    eidx: 0,
                });
            }
            assert!(!format!("{expr:?}").contains("cannot be formatted"));
            #[cfg(feature = "ast")]
            assert_eq!(serde_json::to_string(&expr).is_ok(), value_depth == 64);
        }

        let mut query = Ref::new(Query {
            span: span.clone(),
            stmts: vec![],
            qidx: 0,
        });
        for depth in 0..2048 {
            query = Ref::new(Query {
                span: span.clone(),
                stmts: vec![LiteralStmt {
                    span: span.clone(),
                    literal: Literal::Every {
                        span: span.clone(),
                        key: None,
                        value: span.clone(),
                        domain: leaf(),
                        query,
                    },
                    with_mods: vec![],
                    sidx: 0,
                }],
                qidx: 0,
            });
            if depth == 30 {
                assert!(!format!("{query:?}").contains("cannot be formatted"));
                #[cfg(feature = "ast")]
                serde_json::to_string(&query).unwrap();
            }
        }
        assert!(format!("{query:?}").contains("cannot be formatted"));
        #[cfg(feature = "ast")]
        assert!(serde_json::to_string(&query)
            .unwrap_err()
            .to_string()
            .contains("nesting too deep"));
        drop(query);
        let mut expr = leaf();
        for _ in 0..2048 {
            expr = Ref::new(Expr::Array {
                span: span.clone(),
                items: vec![expr],
                eidx: 0,
            });
            let query = Ref::new(Query {
                span: span.clone(),
                stmts: vec![LiteralStmt {
                    span: span.clone(),
                    literal: Literal::Expr {
                        span: span.clone(),
                        expr,
                    },
                    with_mods: vec![],
                    sidx: 0,
                }],
                qidx: 0,
            });
            expr = Ref::new(Expr::ArrayCompr {
                span: span.clone(),
                term: leaf(),
                query,
                eidx: 0,
            });
        }
        assert!(format!("{expr:?}").contains("cannot be formatted"));
        #[cfg(feature = "ast")]
        assert!(serde_json::to_string(&expr)
            .unwrap_err()
            .to_string()
            .contains("nesting too deep"));
        let mut engine = Engine::new();
        engine
            .add_policy("policy.rego".into(), "package probe\nsafe := 7".into())
            .unwrap();
        let policy = engine
            .compile_with_entrypoint(&Rc::from("data.probe.safe"))
            .unwrap();
        let mut compiler = Compiler::with_policy(&policy);
        let error = compiler.compile_rego_expr(&expr).unwrap_err();
        assert!(error.to_string().contains("nesting too deep"));
        drop(compiler);
        drop(expr);
    });
}
