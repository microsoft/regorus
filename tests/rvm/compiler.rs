// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::instructions::GuardMode;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::rvm::Instruction;
use regorus::{Engine, Rc, Value};
use std::collections::BTreeSet;

/// Compile a single-rule Rego module and return the program.
fn compile_rule(module: &str) -> std::sync::Arc<regorus::rvm::program::Program> {
    let mut engine = Engine::new();
    engine
        .add_policy("test.rego".to_string(), module.to_string())
        .expect("failed to add policy");
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.test.p"))
        .expect("failed to compile policy");
    Compiler::compile_from_policy(&compiled, &["data.test.p"]).expect("failed to compile to RVM")
}

/// Assert that the program's instruction stream contains no collection-create
/// instructions (ArrayCreate, SetCreate, ObjectCreate), meaning the collections
/// were hoisted into the literal table.
fn assert_no_collection_create(program: &regorus::rvm::program::Program) {
    for (pc, instr) in program.instructions.iter().enumerate() {
        match instr {
            Instruction::ArrayCreate { .. } => {
                panic!("unexpected ArrayCreate at pc={pc}; expected hoisted constant")
            }
            Instruction::SetCreate { .. } => {
                panic!("unexpected SetCreate at pc={pc}; expected hoisted constant")
            }
            Instruction::ObjectCreate { .. } => {
                panic!("unexpected ObjectCreate at pc={pc}; expected hoisted constant")
            }
            _ => {}
        }
    }
}

/// Assert the literal table contains a value equal to `expected`.
fn assert_literal_exists(program: &regorus::rvm::program::Program, expected: &Value) {
    assert!(
        program.literals.iter().any(|v| v == expected),
        "expected literal {:?} not found in literal table: {:?}",
        expected,
        program.literals
    );
}

#[test]
fn rule_data_conflict_preserves_error_identity_and_pc() {
    let program = compile_rule(
        r#"
        package test
        p := 1
    "#,
    );
    let mut vm = RegoVM::new();
    vm.load_program(program);

    let error = vm
        .set_data(Value::from_json_str(r#"{"test":{"p":2}}"#).unwrap())
        .unwrap_err();
    assert!(matches!(
        error,
        VmError::RuleDataConflict { ref message, pc: 0 }
            if message.contains("rule defines path 'test.p'")
    ));
}

fn run_rvm_policy(module: &str, input: &str) -> anyhow::Result<Value> {
    let program = compile_rule(module);
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(Value::from_json_str(input)?);
    Ok(vm.execute_entry_point_by_name("data.test.p")?)
}

fn run_interpreter_policy(module: &str, input: &str) -> anyhow::Result<Value> {
    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), module.to_string())?;
    engine.set_input(Value::from_json_str(input)?);
    engine.eval_rule("data.test.p".to_string())
}

fn add_modules(engine: &mut Engine, modules: &[(&str, &str)]) -> anyhow::Result<()> {
    for (name, module) in modules {
        engine.add_policy((*name).to_string(), (*module).to_string())?;
    }
    Ok(())
}

fn compile_modules(
    modules: &[(&str, &str)],
    entry_point: &str,
) -> anyhow::Result<std::sync::Arc<regorus::rvm::program::Program>> {
    let mut engine = Engine::new();
    add_modules(&mut engine, modules)?;
    let entry_point_ref = Rc::from(entry_point);
    let compiled = engine.compile_with_entrypoint(&entry_point_ref)?;
    Ok(Compiler::compile_from_policy(&compiled, &[entry_point])?)
}

fn run_interpreter_modules(
    modules: &[(&str, &str)],
    entry_point: &str,
    input: Value,
) -> anyhow::Result<Value> {
    let mut engine = Engine::new();
    add_modules(&mut engine, modules)?;
    engine.set_input(input);
    engine.eval_rule(entry_point.to_string())
}

#[test]
fn complete_rule_conflict_is_undefined_in_rvm_and_interpreter() {
    let module = r#"
        package test
        p := input.left if input.enabled
        p := input.right if input.enabled
    "#;

    let conflict_input = r#"{"enabled":true,"left":1,"right":2}"#;
    assert_eq!(
        run_rvm_policy(module, conflict_input).unwrap(),
        Value::Undefined
    );
    let interpreter_error = run_interpreter_policy(module, conflict_input)
        .unwrap_err()
        .to_string();
    assert!(
        interpreter_error.contains("rule conflicts"),
        "unexpected interpreter error: {interpreter_error}"
    );

    let equal_input = r#"{"enabled":true,"left":1,"right":1}"#;
    assert_eq!(run_rvm_policy(module, equal_input).unwrap(), Value::from(1));
    assert_eq!(
        run_interpreter_policy(module, equal_input).unwrap(),
        Value::from(1)
    );
}

#[test]
fn function_rule_conflict_is_undefined_in_rvm_and_interpreter() {
    let module = r#"
        package test
        f(x) := input.left if input.enabled
        f(x) := input.right if input.enabled
        p := f(1)
    "#;

    let conflict_input = r#"{"enabled":true,"left":1,"right":2}"#;
    assert_eq!(
        run_rvm_policy(module, conflict_input).unwrap(),
        Value::Undefined
    );
    let interpreter_error = run_interpreter_policy(module, conflict_input)
        .unwrap_err()
        .to_string();
    assert!(
        interpreter_error.contains("functions must not produce multiple outputs"),
        "unexpected interpreter error: {interpreter_error}"
    );

    let equal_input = r#"{"enabled":true,"left":1,"right":1}"#;
    assert_eq!(run_rvm_policy(module, equal_input).unwrap(), Value::from(1));
    assert_eq!(
        run_interpreter_policy(module, equal_input).unwrap(),
        Value::from(1)
    );
}

#[test]
fn constant_array_is_hoisted() {
    let program = compile_rule(
        r#"
        package test
        p := x if { x := [1, 2, 3] }
    "#,
    );
    assert_no_collection_create(&program);
    assert_literal_exists(&program, &Value::from_json_str("[1, 2, 3]").unwrap());
}

#[test]
fn constant_set_is_hoisted() {
    let program = compile_rule(
        r#"
        package test
        p := x if { x := {1, 2, 3} }
    "#,
    );
    assert_no_collection_create(&program);
    let expected_set = Value::from(
        [1, 2, 3]
            .into_iter()
            .map(Value::from)
            .collect::<BTreeSet<_>>(),
    );
    assert_literal_exists(&program, &expected_set);
}

#[test]
fn constant_object_is_hoisted() {
    let program = compile_rule(
        r#"
        package test
        p := x if { x := {"a": 1, "b": 2} }
    "#,
    );
    assert_no_collection_create(&program);
    assert_literal_exists(
        &program,
        &Value::from_json_str(r#"{"a": 1, "b": 2}"#).unwrap(),
    );
}

#[test]
fn nested_constant_collection_is_hoisted() {
    let program = compile_rule(
        r#"
        package test
        p := x if { x := [1, [2, 3], {"k": "v"}] }
    "#,
    );
    assert_no_collection_create(&program);
    assert_literal_exists(
        &program,
        &Value::from_json_str(r#"[1, [2, 3], {"k": "v"}]"#).unwrap(),
    );
}

#[test]
fn non_constant_array_is_not_hoisted() {
    let program = compile_rule(
        r#"
        package test
        p := x if { y := 1; x := [y, 2, 3] }
    "#,
    );
    // This array contains a variable reference, so it must NOT be hoisted.
    let has_array_create = program
        .instructions
        .iter()
        .any(|i| matches!(i, Instruction::ArrayCreate { .. }));
    assert!(
        has_array_create,
        "non-constant array should use ArrayCreate"
    );
}

// --- Eq + Guard(Condition) tests ---
//
// The compiler emits `Eq { dest, left, right }` followed by
// `Guard { register: dest, mode: Condition }` for equality checks,
// rather than a fused `AssertEq`.

/// Count occurrences of a specific instruction pattern in the program.
fn count_instructions(
    program: &regorus::rvm::program::Program,
    pred: impl Fn(&Instruction) -> bool,
) -> usize {
    program.instructions.iter().filter(|i| pred(i)).count()
}

/// Helper: check that the program contains an Eq followed by Guard(Condition).
fn has_eq_guard_condition(program: &regorus::rvm::program::Program) -> bool {
    program.instructions.windows(2).any(|w| {
        matches!(w[0], Instruction::Eq { .. })
            && matches!(
                w[1],
                Instruction::Guard {
                    mode: GuardMode::Condition,
                    ..
                }
            )
    })
}

#[test]
fn equality_check_emits_eq_guard() {
    // Assignment `x = 1` followed by `x = 1` triggers Eq + Guard(Condition).
    let program = compile_rule(
        r#"
        package test
        p if { x = 1; x = 1 }
    "#,
    );
    assert!(
        has_eq_guard_condition(&program),
        "expected Eq + Guard(Condition) pair for equality check"
    );
}

#[test]
fn destructuring_equality_emits_eq_guard() {
    let program = compile_rule(
        r#"
        package test
        p if { [1, x] := [1, 2] }
    "#,
    );
    assert!(
        has_eq_guard_condition(&program),
        "expected Eq + Guard(Condition) for destructuring equality"
    );
}

#[test]
fn not_expr_emits_not_plus_guard_condition() {
    let program = compile_rule(
        r#"
        package test
        p if { not false }
    "#,
    );
    // The compiler emits Not { dest, operand } + Guard { register: dest, mode: Condition }.
    let not_count = count_instructions(&program, |i| matches!(i, Instruction::Not { .. }));
    assert!(
        not_count > 0,
        "expected Not instruction for `not` expression"
    );
    let guard_cond_count = count_instructions(&program, |i| {
        matches!(
            i,
            Instruction::Guard {
                mode: GuardMode::Condition,
                ..
            }
        )
    });
    assert!(
        guard_cond_count > 0,
        "expected Guard(Condition) after Not instruction"
    );
}

// --- B-11: early_exit_on_first_success flag tests ---

/// Find a RuleInfo by name suffix (e.g., "check" matches "data.test.check").
fn find_rule_info<'a>(
    program: &'a regorus::rvm::program::Program,
    name_suffix: &str,
) -> &'a regorus::rvm::program::RuleInfo {
    program
        .rule_infos
        .iter()
        .find(|ri| ri.name.ends_with(name_suffix))
        .unwrap_or_else(|| panic!("no RuleInfo ending with '{name_suffix}'"))
}

#[test]
fn early_exit_set_for_implicit_true_multi_def() {
    let program = compile_rule(
        r#"
        package test
        p if { 1 == 1 }
        p if { 2 == 2 }
    "#,
    );
    let ri = find_rule_info(&program, ".p");
    assert!(
        ri.early_exit_on_first_success,
        "two implicit-true defs should set early_exit_on_first_success"
    );
}

#[test]
fn early_exit_set_for_same_literal_string() {
    let program = compile_rule(
        r#"
        package test
        p := "ok" if { 1 == 1 }
        p := "ok" if { 2 == 2 }
    "#,
    );
    let ri = find_rule_info(&program, ".p");
    assert!(
        ri.early_exit_on_first_success,
        "two defs both returning \"ok\" should set early_exit_on_first_success"
    );
}

#[test]
fn early_exit_not_set_for_different_literals() {
    let program = compile_rule(
        r#"
        package test
        p := "a" if { 1 == 1 }
        p := "b" if { 2 == 2 }
    "#,
    );
    let ri = find_rule_info(&program, ".p");
    assert!(
        !ri.early_exit_on_first_success,
        "defs returning different literals must NOT set early_exit_on_first_success"
    );
}

#[test]
fn early_exit_not_set_for_computed_values() {
    let program = compile_rule(
        r#"
        package test
        p := x if { x := 1 + 1 }
        p := x if { x := 2 + 0 }
    "#,
    );
    let ri = find_rule_info(&program, ".p");
    assert!(
        !ri.early_exit_on_first_success,
        "computed expressions must NOT set early_exit_on_first_success"
    );
}

#[test]
fn early_exit_not_set_for_single_definition() {
    let program = compile_rule(
        r#"
        package test
        p if { 1 == 1 }
    "#,
    );
    let ri = find_rule_info(&program, ".p");
    assert!(
        !ri.early_exit_on_first_success,
        "single definition should not set early_exit (only ≥2 defs)"
    );
}

#[test]
fn early_exit_not_set_for_else_with_different_values() {
    let program = compile_rule(
        r#"
        package test
        p := "a" if { false } else := "b" if { true }
        p := "a" if { true }
    "#,
    );
    let ri = find_rule_info(&program, ".p");
    assert!(
        !ri.early_exit_on_first_success,
        "else branches with different values must NOT set early_exit_on_first_success"
    );
}

#[test]
fn early_exit_set_for_else_with_same_values() {
    let program = compile_rule(
        r#"
        package test
        p := "x" if { false } else := "x" if { true }
        p := "x" if { true }
    "#,
    );
    let ri = find_rule_info(&program, ".p");
    assert!(
        ri.early_exit_on_first_success,
        "else branches all returning same literal should set early_exit_on_first_success"
    );
}

#[test]
fn early_exit_set_for_implicit_true_function() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".to_string(),
            r#"
            package test
            check(x) if { x > 0 }
            check(x) if { x < -10 }
            p := check(5)
        "#
            .to_string(),
        )
        .expect("failed to add policy");
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.test.p"))
        .expect("failed to compile");
    let program = Compiler::compile_from_policy(&compiled, &["data.test.p"])
        .expect("failed to compile to RVM");
    let ri = find_rule_info(&program, ".check");
    assert!(
        ri.early_exit_on_first_success,
        "implicit-true function with 2 defs should set early_exit_on_first_success"
    );
}

#[test]
fn callable_default_runs_after_imported_function_definitions_miss() -> anyhow::Result<()> {
    let helper = r#"package helpers["1.0.0"]
import rego.v1
default f(_) := true
f(x) := false if x == 1
"#;
    let main = r#"package main["2.0.0"]
import rego.v1
import data.helpers["1.0.0"].f as f
p := f(input.x)
"#;
    let modules = [("helper.rego", helper), ("main.rego", main)];
    let entry_point = r#"data.main["2.0.0"].p"#;
    let inputs = [
        Value::from_json_str(r#"{"x":1}"#)?,
        Value::from_json_str(r#"{"x":2}"#)?,
        Value::new_object(),
    ];
    let expected: Vec<std::result::Result<Value, String>> = vec![
        Ok(Value::Bool(false)),
        Ok(Value::Bool(true)),
        Ok(Value::Undefined),
    ];

    let interpreter_results = inputs
        .iter()
        .cloned()
        .map(|input| {
            run_interpreter_modules(&modules, entry_point, input).map_err(|error| error.to_string())
        })
        .collect::<Vec<_>>();
    assert_eq!(interpreter_results, expected, "interpreter results");

    let program = compile_modules(&modules, entry_point)?;
    let mut vm_results_by_mode = Vec::new();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        let vm_results = inputs
            .iter()
            .cloned()
            .map(|input| {
                vm.set_input(input);
                vm.execute_entry_point_by_name(entry_point)
                    .map_err(|error| error.to_string())
            })
            .collect::<Vec<_>>();
        vm_results_by_mode.push(vm_results);
    }
    assert_eq!(
        vm_results_by_mode,
        vec![expected.clone(), expected],
        "RunToCompletion and Suspendable VM results"
    );

    Ok(())
}

#[test]
fn callable_default_does_not_hide_wrong_function_arity() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := true
f(x) := false if x == 1
p := f(0, 1, 2)
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";

    assert!(
        run_interpreter_modules(&modules, entry_point, Value::new_object()).is_err(),
        "the interpreter must reject a wrong-arity ordinary call"
    );

    let program = compile_modules(&modules, entry_point)?;
    let mut vm_results = Vec::new();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm_results.push(vm.execute_entry_point_by_name(entry_point));
    }
    let rejected_wrong_arity = vm_results
        .iter()
        .map(|result| matches!(result, Err(VmError::FunctionArgumentMismatch { .. })))
        .collect::<Vec<_>>();
    assert_eq!(
        rejected_wrong_arity,
        vec![true, true],
        "both VM modes must reject wrong arity rather than select the default: {vm_results:?}"
    );

    Ok(())
}

#[test]
fn default_only_callable_binds_its_output_argument() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := true
p := result if { f(0, result) }
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";
    let input = Value::new_object();
    assert_eq!(
        run_interpreter_modules(&modules, entry_point, input.clone())?,
        Value::Bool(true),
        "the interpreter must bind the output argument from a default-only function"
    );

    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::Bool(true),
            "{mode:?} must bind the output argument from a default-only function"
        );
    }
    Ok(())
}

#[test]
fn aliased_default_only_callable_binds_its_output_argument() -> anyhow::Result<()> {
    let helper = r#"package helpers
import rego.v1
default f(_) := true
"#;
    let main = r#"package main
import rego.v1
import data.helpers as helper
p := result if { helper.f(0, result) }
"#;
    let modules = [("helper.rego", helper), ("main.rego", main)];
    let entry_point = "data.main.p";
    let input = Value::new_object();
    assert_eq!(
        run_interpreter_modules(&modules, entry_point, input.clone())?,
        Value::Bool(true),
        "the interpreter must bind the output argument through an import alias"
    );

    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::Bool(true),
            "{mode:?} must bind the output argument through an import alias"
        );
    }
    Ok(())
}

#[test]
fn absolute_data_call_does_not_resolve_package_prefixed_shadow() -> anyhow::Result<()> {
    let shadow = r#"package main.data.helpers
import rego.v1
default f(_) := true
"#;
    let main = r#"package main
import rego.v1
p := data.helpers.f(0)
"#;
    let entry_point = "data.main.p";
    for modules in [
        [("shadow.rego", shadow), ("main.rego", main)],
        [("main.rego", main), ("shadow.rego", shadow)],
    ] {
        let interpreter_result =
            run_interpreter_modules(&modules, entry_point, Value::new_object());
        assert!(
            interpreter_result.as_ref().err().is_some_and(|error| {
                error
                    .to_string()
                    .contains("could not find function data.helpers.f")
            }),
            "expected a missing absolute function error, got {interpreter_result:?}"
        );

        let mut engine = Engine::new();
        add_modules(&mut engine, &modules)?;
        let compiled = engine.compile_with_entrypoint(&Rc::from(entry_point))?;
        let compiler_result = Compiler::compile_from_policy(&compiled, &[entry_point]);
        assert!(
            compiler_result
                .as_ref()
                .err()
                .is_some_and(|error| {
                    error
                        .to_string()
                        .contains("Unknown function: 'data.helpers.f'")
                }),
            "expected the RVM compiler to reject the missing absolute target, got {compiler_result:?}"
        );
    }
    Ok(())
}

#[test]
fn absolute_data_call_and_bracketed_path_resolve_the_root_function() -> anyhow::Result<()> {
    let helper = r#"package helpers
import rego.v1
default f(_) := true
"#;
    let main = r#"package main
import rego.v1
dotted := data.helpers.f(0)
bracketed := data["helpers"].f(0)
"#;
    let modules = [("helper.rego", helper), ("main.rego", main)];
    for entry_point in ["data.main.dotted", "data.main.bracketed"] {
        assert_eq!(
            run_interpreter_modules(&modules, entry_point, Value::new_object())?,
            Value::Bool(true),
            "the interpreter must resolve {entry_point} from the absolute data root"
        );

        let program = compile_modules(&modules, entry_point)?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name(entry_point)?,
                Value::Bool(true),
                "{mode:?} must resolve {entry_point} from the absolute data root"
            );
        }
    }
    Ok(())
}

#[test]
fn callable_default_ignores_partial_child_rule_type() -> anyhow::Result<()> {
    let source = r#"package main
import rego.v1
default f(_) := "fallback"
f.child contains 1
p := f(0)
"#;
    let modules = [("main.rego", source)];
    let entry_point = "data.main.p";
    assert_eq!(
        run_interpreter_modules(&modules, entry_point, Value::new_object())?,
        Value::from("fallback"),
        "the interpreter must use the callable default"
    );

    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::from("fallback"),
            "{mode:?} must not classify the callable parent as its partial child"
        );
    }
    Ok(())
}

#[test]
fn callable_default_ignores_partial_object_child_rule_type() -> anyhow::Result<()> {
    let source = r#"package main
import rego.v1
default f(_) := "fallback"
f.child[input.key] := true
p := f(0)
"#;
    let modules = [("main.rego", source)];
    let entry_point = "data.main.p";
    let input = Value::from_json_str(r#"{"key":"x"}"#)?;
    assert_eq!(
        run_interpreter_modules(&modules, entry_point, input.clone())?,
        Value::from("fallback"),
        "the interpreter must use the callable default"
    );

    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::from("fallback"),
            "{mode:?} must not classify the callable parent as its partial object child"
        );
    }
    Ok(())
}

#[test]
fn strict_builtin_failure_does_not_fall_through_to_callable_default() -> anyhow::Result<()> {
    let source = r#"package main
import rego.v1
default f(_) := [1 | true]
f(_) := to_number("bad")
allow := f(0) == [1]
"#;
    let modules = [("main.rego", source)];
    let entry_point = "data.main.allow";
    let mut engine = Engine::new();
    add_modules(&mut engine, &modules)?;
    engine.set_strict_builtin_errors(true);
    let interpreter_result = engine.eval_rule(entry_point.to_string());
    assert!(
        interpreter_result.is_err(),
        "strict interpreter builtin failures must remain errors"
    );
    engine.set_strict_builtin_errors(false);
    assert_eq!(
        engine.eval_rule(entry_point.to_string())?,
        Value::Bool(true),
        "non-strict interpreter builtin failures may use the default"
    );

    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_strict_builtin_errors(true);
        let strict_result = vm.execute_entry_point_by_name(entry_point);
        assert!(
            matches!(
                strict_result,
                Err(ref error) if error.to_string().contains("could not parse string as number")
            ),
            "{mode:?} strict builtin failure must remain an error, got {strict_result:?}"
        );

        vm.set_strict_builtin_errors(false);
        vm.set_input(Value::new_object());
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::Bool(true),
            "{mode:?} VM must be reusable with non-strict fallback after an error"
        );
    }
    Ok(())
}

#[test]
fn resumed_strict_builtin_error_sets_terminal_state_and_vm_is_reusable() -> anyhow::Result<()> {
    let source = r#"package main
import rego.v1
p := to_number(__builtin_host_await(input.value, "remote"))
"#;
    let modules = [("main.rego", source)];
    let entry_point = "data.main.p";
    let program = compile_modules(&modules, entry_point)?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_strict_builtin_errors(true);

    vm.execute_entry_point_by_name(entry_point)?;
    assert!(
        matches!(vm.execution_state(), ExecutionState::Suspended { .. }),
        "HostAwait must suspend before evaluating to_number"
    );
    assert!(matches!(
        vm.resume(None),
        Err(VmError::MissingResumeValue { .. })
    ));
    assert!(
        matches!(vm.execution_state(), ExecutionState::Suspended { .. }),
        "invalid resume-value validation must leave the suspension retryable"
    );
    let error = vm.resume(Some(Value::from("bad"))).unwrap_err();
    assert!(matches!(error, VmError::StrictBuiltinError { .. }));
    assert!(
        matches!(
            vm.execution_state(),
            ExecutionState::Error {
                error: VmError::StrictBuiltinError { .. }
            }
        ),
        "a resumed runtime error must be published as terminal Error state"
    );

    vm.set_strict_builtin_errors(false);
    vm.execute_entry_point_by_name(entry_point)?;
    assert_eq!(vm.resume(Some(Value::from("bad")))?, Value::Undefined);
    Ok(())
}

#[test]
fn strict_comparison_arithmetic_error_remains_fallback_eligible() -> anyhow::Result<()> {
    let source = r#"package main
import rego.v1
default f(_) := [1]
f(_) := 1 < "1"
allow := f(0) == [1]
"#;
    let modules = [("main.rego", source)];
    let entry_point = "data.main.allow";
    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_strict_builtin_errors(true);
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::Bool(true),
            "{mode:?} must not promote a non-builtin ArithmeticError to fatal"
        );
    }
    Ok(())
}

#[test]
fn callable_default_executes_dynamic_array_comprehension() -> anyhow::Result<()> {
    let source = r#"package main
import rego.v1
default f(_) := [1 | true]
f(_) := to_number("bad")
p := f(0)
"#;
    let modules = [("main.rego", source)];
    let entry_point = "data.main.p";
    let mut engine = Engine::new();
    add_modules(&mut engine, &modules)?;
    engine.set_strict_builtin_errors(false);
    assert_eq!(
        engine.eval_rule(entry_point.to_string())?,
        Value::from_json_str("[1]")?,
        "the interpreter must evaluate a dynamic callable default"
    );

    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(Value::new_object());
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::from_json_str("[1]")?,
            "{mode:?} must evaluate a dynamic callable default"
        );
    }
    Ok(())
}

#[test]
fn dynamic_callable_default_preserves_false_null_and_empty_array_results() -> anyhow::Result<()> {
    let source = r#"package main
import rego.v1
default f(_) := [1 | true]
f(_) := input.value
p := f(0)
"#;
    let modules = [("main.rego", source)];
    let entry_point = "data.main.p";
    let cases = [
        (r#"{"value":false}"#, Value::Bool(false)),
        (r#"{"value":null}"#, Value::Null),
        (r#"{"value":[]}"#, Value::new_array()),
        (r#"{}"#, Value::from_json_str("[1]")?),
    ];

    for (input_json, expected) in cases {
        let input = Value::from_json_str(input_json)?;
        assert_eq!(
            run_interpreter_modules(&modules, entry_point, input.clone())?,
            expected,
            "the interpreter must preserve ordinary results for input {input_json}"
        );

        let program = compile_modules(&modules, entry_point)?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name(entry_point)?,
                expected,
                "{mode:?} must preserve ordinary results for input {input_json}"
            );
        }
    }
    Ok(())
}

#[test]
fn dynamic_default_comprehensions_skip_undefined_keys_and_values_after_v6_round_trip(
) -> anyhow::Result<()> {
    use regorus::rvm::program::{DeserializationResult, Program};

    let helper = r#"package helpers
import rego.v1
import data.owner as source
default f(_) := {
    "set_count": count({item.value | some item in source.items}),
    "set_drop_key": "drop-key" in {item.value | some item in source.items},
    "set_false": false in {item.value | some item in source.items},
    "set_null": null in {item.value | some item in source.items},
    "set_kept": "kept" in {item.value | some item in source.items},
    "array": [item.value | some item in source.items],
    "object": {item.key: item.value | some item in source.items}
}
f(x) := "ordinary" if x == 1
"#;
    let main = r#"package main
import rego.v1
import data.caller as source
import data.helpers.f as f
p := f(input.argument)
"#;
    let module_orders = [
        [("helper.rego", helper), ("main.rego", main)],
        [("main.rego", main), ("helper.rego", helper)],
    ];
    let data = Value::from_json_str(
        r#"{"owner":{"items":[{"key":"drop-value"},{"value":"drop-key"},{"key":"false","value":false},{"key":"null","value":null},{"key":"valid","value":"kept"}]},"caller":{"items":[{"key":"caller","value":"wrong"}]}}"#,
    )?;
    let inputs = [
        Value::from_json_str(r#"{"argument":1}"#)?,
        Value::from_json_str(r#"{"argument":0}"#)?,
    ];
    let expected = [
        Value::from("ordinary"),
        Value::from_json_str(
            r#"{"set_count":4,"set_drop_key":true,"set_false":true,"set_null":true,"set_kept":true,"array":["drop-key",false,null,"kept"],"object":{"false":false,"null":null,"valid":"kept"}}"#,
        )?,
    ];

    for modules in module_orders {
        let entry_point = "data.main.p";
        let mut engine = Engine::new();
        for (module_path, module) in &modules {
            engine.add_policy((*module_path).to_string(), (*module).to_string())?;
        }
        engine.add_data(data.clone())?;

        for (input, expected) in inputs.iter().zip(expected.iter()) {
            engine.set_input(input.clone());
            assert_eq!(
                engine.eval_rule(entry_point.to_string())?,
                *expected,
                "interpreter result for input {input:?}"
            );
        }

        let compiled = engine.compile_with_entrypoint(&Rc::from(entry_point))?;
        let program = Compiler::compile_from_policy(&compiled, &[entry_point])?;
        let json = program.serialize_json().map_err(anyhow::Error::msg)?;
        let json_program =
            std::sync::Arc::new(Program::deserialize_json(&json).map_err(anyhow::Error::msg)?);
        let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
        assert_eq!(
            u16::from_le_bytes([binary[4], binary[5]]),
            6,
            "helper-bearing dynamic defaults must remain in Program v6"
        );
        let binary_program =
            match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
                DeserializationResult::Complete(program) => std::sync::Arc::new(program),
                DeserializationResult::Partial(_) => {
                    anyhow::bail!("helper-bearing dynamic-default v6 program needs recompilation")
                }
            };

        for (program, graph) in [
            (program, "compiled"),
            (json_program, "JSON round trip"),
            (binary_program, "binary round trip"),
        ] {
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                vm.set_data(data.clone())?;

                for (input, expected) in inputs.iter().zip(expected.iter()) {
                    vm.set_input(input.clone());
                    assert_eq!(
                        vm.execute_entry_point_by_name(entry_point)?,
                        *expected,
                        "{graph} {mode:?} result for input {input:?}"
                    );
                }
            }
        }
    }

    Ok(())
}

#[test]
fn local_namespace_documents_merge_values_but_not_callable_descendants() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default config.timeout := 30
default config.retries := 5
config.timeout := 42
config.mode := "strict"
default config.render(_) := input.render
p := config
callable := config.render(0)
"#;
    let modules = [("test.rego", source)];
    let data = Value::from_json_str(r#"{"test":{"config":{"base":"data"}}}"#)?;
    let input = Value::from_json_str(r#"{"render":"called"}"#)?;
    let entry_points = [
        (
            "data.test.p",
            Value::from_json_str(r#"{"base":"data","retries":5,"timeout":42,"mode":"strict"}"#)?,
        ),
        ("data.test.callable", Value::from("called")),
    ];

    let mut engine = Engine::new();
    add_modules(&mut engine, &modules)?;
    engine.add_data(data.clone())?;
    engine.set_input(input.clone());
    for (entry_point, expected) in &entry_points {
        assert_eq!(
            engine.eval_rule((*entry_point).to_string())?,
            *expected,
            "interpreter result for {entry_point}"
        );
    }

    for (entry_point, expected) in &entry_points {
        let compiled = engine.compile_with_entrypoint(&Rc::from(*entry_point))?;
        let program = Compiler::compile_from_policy(&compiled, &[*entry_point])?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_data(data.clone())?;
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name(entry_point)?,
                *expected,
                "{mode:?} result for {entry_point}"
            );
        }
    }

    Ok(())
}

#[test]
fn dynamic_callable_default_reads_current_input_and_data_on_reused_vm() -> anyhow::Result<()> {
    let helper = r#"package helpers
import rego.v1
import data.owner as source
default f(_) := {"input": input.x, "owner": source.value}
f(x) := "ordinary" if x == 1
"#;
    let main = r#"package main
import rego.v1
import data.helpers.f as f
p := f(input.argument)
"#;
    let module_orders = [
        [("helper.rego", helper), ("main.rego", main)],
        [("main.rego", main), ("helper.rego", helper)],
    ];
    let cases = [
        (
            Value::from_json_str(r#"{"argument":0,"x":7}"#)?,
            Value::from_json_str(r#"{"owner":{"value":"first"}}"#)?,
            Value::from_json_str(r#"{"input":7,"owner":"first"}"#)?,
        ),
        (
            Value::from_json_str(r#"{"argument":0,"x":9}"#)?,
            Value::from_json_str(r#"{"owner":{"value":"second"}}"#)?,
            Value::from_json_str(r#"{"input":9,"owner":"second"}"#)?,
        ),
        (
            Value::from_json_str(r#"{"argument":1,"x":11}"#)?,
            Value::from_json_str(r#"{"owner":{"value":"third"}}"#)?,
            Value::from("ordinary"),
        ),
    ];

    for modules in module_orders {
        let program = compile_modules(&modules, "data.main.p")?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            for (input, data, expected) in &cases {
                vm.set_input(input.clone());
                vm.set_data(data.clone())?;
                assert_eq!(
                    vm.execute_entry_point_by_name("data.main.p")?,
                    *expected,
                    "{mode:?} result for input {input:?} and data {data:?}"
                );
            }
        }

        for (input, data, expected) in &cases {
            let mut engine = Engine::new();
            add_modules(&mut engine, &modules)?;
            engine.add_data(data.clone())?;
            engine.set_input(input.clone());
            assert_eq!(
                engine.eval_rule("data.main.p".to_string())?,
                *expected,
                "interpreter result for input {input:?} and data {data:?}"
            );
        }
    }

    Ok(())
}

#[test]
fn default_only_parent_and_child_functions_keep_exact_arities_in_module_orders(
) -> anyhow::Result<()> {
    let parent = r#"package test
import rego.v1
default f(_) := true
"#;
    let child = r#"package test
import rego.v1
default f.child(_, _) := true
"#;
    let main = r#"package main
import rego.v1
p := {
    "parent": data.test.f(0),
    "child": data.test.f.child(0, 0)
}
"#;
    let expected = Value::from_json_str(r#"{"parent":true,"child":true}"#)?;

    for modules in [
        [
            ("parent.rego", parent),
            ("child.rego", child),
            ("main.rego", main),
        ],
        [
            ("child.rego", child),
            ("parent.rego", parent),
            ("main.rego", main),
        ],
    ] {
        assert_eq!(
            run_interpreter_modules(&modules, "data.main.p", Value::new_object())?,
            expected,
            "interpreter result for module order {modules:?}"
        );

        let program = compile_modules(&modules, "data.main.p")?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name("data.main.p")?,
                expected,
                "{mode:?} result for module order {modules:?}"
            );
        }
    }

    Ok(())
}

#[test]
fn default_only_output_literals_resolve_absolute_and_aliased_calls() -> anyhow::Result<()> {
    let helper = r#"package helpers
import rego.v1
default f(_) := true
"#;
    let main = r#"package main
import rego.v1
import data.helpers as helper
qualified_match if { data.helpers.f(0, true) }
qualified_mismatch if { data.helpers.f(0, false) }
aliased_match if { helper.f(0, true) }
aliased_mismatch if { helper.f(0, false) }
bound := result if { helper.f(0, result) }
"#;
    let module_orders = [
        [("helper.rego", helper), ("main.rego", main)],
        [("main.rego", main), ("helper.rego", helper)],
    ];
    let entry_points = [
        ("data.main.qualified_match", Value::Bool(true)),
        ("data.main.qualified_mismatch", Value::Undefined),
        ("data.main.aliased_match", Value::Bool(true)),
        ("data.main.aliased_mismatch", Value::Undefined),
        ("data.main.bound", Value::Bool(true)),
    ];

    for modules in module_orders {
        for (entry_point, expected) in &entry_points {
            assert_eq!(
                run_interpreter_modules(&modules, entry_point, Value::new_object())?,
                *expected,
                "interpreter result for {entry_point}"
            );

            let program = compile_modules(&modules, entry_point)?;
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                assert_eq!(
                    vm.execute_entry_point_by_name(entry_point)?,
                    *expected,
                    "{mode:?} result for {entry_point}"
                );
            }
        }
    }

    Ok(())
}

#[test]
fn absolute_default_call_uses_root_target_arity_for_input_and_output_arguments(
) -> anyhow::Result<()> {
    let root_two_arguments = r#"package helpers
import rego.v1
default f(_, _) := true
"#;
    let shadow_one_argument = r#"package main.data.helpers
import rego.v1
default f(_) := false
"#;
    let direct_call = r#"package main
import rego.v1
p if { data.helpers.f(0, 0) }
"#;
    for modules in [
        [
            ("helper.rego", root_two_arguments),
            ("shadow.rego", shadow_one_argument),
            ("main.rego", direct_call),
        ],
        [
            ("shadow.rego", shadow_one_argument),
            ("helper.rego", root_two_arguments),
            ("main.rego", direct_call),
        ],
    ] {
        let expected = Value::Bool(true);
        assert_eq!(
            run_interpreter_modules(&modules, "data.main.p", Value::new_object())?,
            expected,
            "interpreter direct-input result for module order {modules:?}"
        );
        let program = compile_modules(&modules, "data.main.p")?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name("data.main.p")?,
                expected,
                "{mode:?} direct-input result for module order {modules:?}"
            );
        }
    }

    let root_one_argument = r#"package helpers
import rego.v1
default f(_) := true
"#;
    let shadow_two_arguments = r#"package main.data.helpers
import rego.v1
default f(_, _) := false
"#;
    let output_calls = r#"package main
import rego.v1
matched if { data.helpers.f(0, true) }
mismatched if { data.helpers.f(0, false) }
bound := result if { data.helpers.f(0, result) }
"#;
    let expected_by_entry_point = [
        ("data.main.matched", Value::Bool(true)),
        ("data.main.mismatched", Value::Undefined),
        ("data.main.bound", Value::Bool(true)),
    ];
    for modules in [
        [
            ("helper.rego", root_one_argument),
            ("shadow.rego", shadow_two_arguments),
            ("main.rego", output_calls),
        ],
        [
            ("shadow.rego", shadow_two_arguments),
            ("helper.rego", root_one_argument),
            ("main.rego", output_calls),
        ],
    ] {
        for (entry_point, expected) in &expected_by_entry_point {
            assert_eq!(
                run_interpreter_modules(&modules, entry_point, Value::new_object())?,
                *expected,
                "interpreter output-argument result for {entry_point}"
            );
            let program = compile_modules(&modules, entry_point)?;
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(mode);
                assert_eq!(
                    vm.execute_entry_point_by_name(entry_point)?,
                    *expected,
                    "{mode:?} output-argument result for {entry_point}"
                );
            }
        }
    }

    Ok(())
}

#[test]
fn interpreter_preserves_function_arity_at_u8_boundaries() -> anyhow::Result<()> {
    let zero_arity = r#"package test
import rego.v1
zero() := "ordinary"
p := zero()
"#;
    let zero_modules = [("test.rego", zero_arity)];
    let zero_expected = Value::from("ordinary");
    assert_eq!(
        run_interpreter_modules(&zero_modules, "data.test.p", Value::new_object())?,
        zero_expected,
        "the interpreter must preserve zero-argument function arity"
    );
    let zero_program = compile_modules(&zero_modules, "data.test.p")?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(zero_program.clone());
        vm.set_execution_mode(mode);
        assert_eq!(
            vm.execute_entry_point_by_name("data.test.p")?,
            zero_expected,
            "{mode:?} must preserve zero-argument function arity"
        );
    }

    let arguments = |values: &[String]| {
        values
            .chunks(16)
            .map(|chunk| format!("    {}", chunk.join(", ")))
            .collect::<Vec<_>>()
            .join(",\n")
    };

    for arity in [255, 256, 257] {
        let parameters = (1..=arity)
            .map(|index| format!("a{index}"))
            .collect::<Vec<_>>();
        let values = (1..=arity)
            .map(|value| value.to_string())
            .collect::<Vec<_>>();
        let source = format!(
            "package test\n\
             import rego.v1\n\
             ordinary(\n{parameters}\n) := true\n\
             default default_only(\n{parameters}\n) := true\n\
             p := ordinary(\n{values}\n)\n\
             q := default_only(\n{values}\n)\n",
            parameters = arguments(&parameters),
            values = arguments(&values),
        );
        let mut engine = Engine::new();
        engine.add_policy("test.rego".to_string(), source)?;
        assert_eq!(
            engine.eval_rule("data.test.p".to_string())?,
            Value::Bool(true),
            "ordinary function with {arity} arguments"
        );
        assert_eq!(
            engine.eval_rule("data.test.q".to_string())?,
            Value::Bool(true),
            "default-only function with {arity} arguments"
        );
    }
    Ok(())
}

#[test]
fn rvm_rejects_callable_default_calls_above_its_argument_limit() -> anyhow::Result<()> {
    let too_many_arguments = r#"package test
import rego.v1
default f(_, _, _, _, _, _, _, _) := true
p := f(0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
"#;
    let invalid_modules = [("test.rego", too_many_arguments)];
    let entry_point = "data.test.p";
    let interpreter_error =
        run_interpreter_modules(&invalid_modules, entry_point, Value::new_object())
            .expect_err("the interpreter must reject ten arguments for an eight-argument default")
            .to_string();
    assert!(
        interpreter_error.contains("supplied 10, expected 8"),
        "expected an arity error, got {interpreter_error}"
    );

    let compiler_error = match compile_modules(&invalid_modules, entry_point) {
        Err(error) => error.to_string(),
        Ok(_) => panic!("RVM compilation must reject ten inputs before encoding only eight"),
    };
    assert!(
        compiler_error.contains("supports at most 8 arguments, got 10"),
        "expected an unrepresentable-arity error, got {compiler_error}"
    );

    let valid_calls = r#"package test
import rego.v1
default f(_, _, _, _, _, _, _, _) := true
eight_inputs := f(0, 0, 0, 0, 0, 0, 0, 0)
output_argument := result if { f(0, 0, 0, 0, 0, 0, 0, 0, result) }
p := {"eight_inputs": eight_inputs, "output_argument": output_argument}
"#;
    let valid_modules = [("test.rego", valid_calls)];
    let expected = Value::from_json_str(r#"{"eight_inputs":true,"output_argument":true}"#)?;
    assert_eq!(
        run_interpreter_modules(&valid_modules, entry_point, Value::new_object())?,
        expected,
        "the interpreter must preserve eight inputs and the ninth output argument"
    );

    let program = compile_modules(&valid_modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            expected,
            "{mode:?} must preserve eight inputs and the ninth output argument"
        );
    }
    Ok(())
}

#[test]
fn value_default_does_not_hide_native_builtin_count() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default count := 123
p := count([])
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";
    let interpreter_result = run_interpreter_modules(&modules, entry_point, Value::new_object());
    assert!(
        matches!(&interpreter_result, Ok(value) if value == &Value::from(0)),
        "the interpreter must dispatch count([]) to the builtin, got {interpreter_result:?}"
    );

    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::from(0),
            "{mode:?} must dispatch count([]) to the builtin"
        );
    }
    Ok(())
}

#[test]
fn value_default_remains_fallback_for_same_name_ordinary_function() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default pick := 123
pick(x) := "ordinary" if x == "hit"
p := {"ordinary": pick("hit"), "fallback": pick("miss")}
"#;
    let modules = [("test.rego", source)];
    let expected = Value::from_json_str(r#"{"ordinary":"ordinary","fallback":123}"#)?;
    assert_eq!(
        run_interpreter_modules(&modules, "data.test.p", Value::new_object())?,
        expected,
        "the value default must remain available after the same-name ordinary function misses"
    );
    Ok(())
}

#[test]
fn host_await_runs_only_for_default_fallback_and_resumes_once() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [count(input.value) | true]
f(x) := "ordinary" if x == 1
p := f(input.value)
"#;
    let entry_point = "data.test.p";
    let modules = [("test.rego", source)];
    let mut engine = Engine::new();
    add_modules(&mut engine, &modules)?;
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry_point))?;
    let program =
        Compiler::compile_from_policy_with_host_await(&compiled, &[entry_point], &[("count", 1)])?;

    let mut run_to_completion = RegoVM::new();
    run_to_completion.load_program(program.clone());
    run_to_completion
        .set_host_await_responses([(Value::from("count"), [Value::from("host-result")])]);
    run_to_completion.set_input(Value::from_json_str(r#"{"value":1}"#)?);
    assert_eq!(
        run_to_completion.execute_entry_point_by_name(entry_point)?,
        Value::from("ordinary"),
        "an ordinary success must not execute the default host call"
    );
    run_to_completion.set_input(Value::from_json_str(r#"{"value":2}"#)?);
    assert_eq!(
        run_to_completion.execute_entry_point_by_name(entry_point)?,
        Value::from_json_str(r#"["host-result"]"#)?,
        "the fallback host call must consume exactly one response"
    );
    run_to_completion.set_input(Value::from_json_str(r#"{"value":3}"#)?);
    assert_eq!(
        run_to_completion.execute_entry_point_by_name(entry_point)?,
        Value::Undefined,
        "a missing default host response remains a failed rule result"
    );

    let mut suspendable = RegoVM::new();
    suspendable.load_program(program);
    suspendable.set_execution_mode(ExecutionMode::Suspendable);
    suspendable.set_input(Value::from_json_str(r#"{"value":1}"#)?);
    assert_eq!(
        suspendable.execute_entry_point_by_name(entry_point)?,
        Value::from("ordinary")
    );
    suspendable.set_input(Value::from_json_str(r#"{"value":2}"#)?);
    suspendable.execute_entry_point_by_name(entry_point)?;
    assert!(
        matches!(
            suspendable.execution_state(),
            ExecutionState::Suspended { .. }
        ),
        "the default host call must suspend"
    );
    assert_eq!(
        suspendable.resume(Some(Value::from("resumed")))?,
        Value::from_json_str(r#"["resumed"]"#)?
    );
    suspendable.set_input(Value::from_json_str(r#"{"value":1}"#)?);
    assert_eq!(
        suspendable.execute_entry_point_by_name(entry_point)?,
        Value::from("ordinary"),
        "the VM must remain reusable after resume"
    );
    Ok(())
}

#[test]
fn callable_default_does_not_absorb_instruction_limit_errors() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [value | some value in input.values]
p := f(input.x)
"#;
    let modules = [("test.rego", source)];
    let program = compile_modules(&modules, "data.test.p")?;

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(r#"{"x":0,"values":[1]}"#)?);
        vm.set_max_instructions(0);
        assert!(
            matches!(
                vm.execute_entry_point_by_name("data.test.p"),
                Err(VmError::InstructionLimitExceeded { .. })
            ),
            "{mode:?} must preserve the instruction-limit error instead of using the default"
        );
    }

    Ok(())
}

#[test]
fn callable_defaults_preserve_ordinary_values_else_and_conflicts() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default choose(_) := [value | some value in input.fallback]
choose(x) := false if x == "false"
choose(x) := null if x == "null"
choose(x) := [] if x == "empty"
choose(x) := "same" if x == "same"
choose(x) := "same" if x == "same"
default branch(_) := [value | some value in input.fallback]
branch(x) := "one" if x == 1
else := "two" if x == 2
p := {
    "false": choose("false"),
    "null": choose("null"),
    "empty": choose("empty"),
    "equal": choose("same"),
    "one": branch(1),
    "two": branch(2),
    "fallback": branch(3)
}
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";
    let input = Value::from_json_str(r#"{"fallback":["fallback"]}"#)?;
    let expected = Value::from_json_str(
        r#"{"false":false,"null":null,"empty":[],"equal":"same","one":"one","two":"two","fallback":["fallback"]}"#,
    )?;
    assert_eq!(
        run_interpreter_modules(&modules, entry_point, input.clone())?,
        expected,
        "interpreter must keep every successful ordinary result"
    );
    let program = compile_modules(&modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            expected,
            "{mode:?} must keep every successful ordinary result"
        );
    }

    let conflict = r#"package test
import rego.v1
default f(_) := input.fallback
f(x) := "first" if x == 1
f(x) := "second" if x == 1
p := f(1)
"#;
    let conflict_modules = [("test.rego", conflict)];
    let conflict_input = Value::from_json_str(r#"{"fallback":"default"}"#)?;
    assert!(
        run_interpreter_modules(&conflict_modules, entry_point, conflict_input.clone()).is_err(),
        "the interpreter must preserve its ordinary function conflict error"
    );
    let conflict_program = compile_modules(&conflict_modules, entry_point)?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(conflict_program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(conflict_input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)?,
            Value::Undefined,
            "{mode:?} must not select a default after conflicting ordinary results"
        );
    }

    Ok(())
}

#[test]
fn value_parent_rules_and_defaults_remain_distinct_from_child_callable_defaults(
) -> anyhow::Result<()> {
    let parent_value_first = r#"package test
import rego.v1
a := true
default a.child(_) := [input.items | true]
p := a
"#;
    let child_default_first = r#"package test
import rego.v1
default a.child(_) := [input.items | true]
a := true
p := a
"#;
    let parent_default_first = r#"package test
import rego.v1
default f := true
default f.child(_) := input.child
p := data.test.f
"#;
    let child_default_first_value = r#"package test
import rego.v1
default f.child(_) := input.child
default f := true
p := data.test.f
"#;

    for (source, entry_point) in [
        (parent_value_first, "data.test.p"),
        (child_default_first, "data.test.p"),
        (parent_default_first, "data.test.p"),
        (child_default_first_value, "data.test.p"),
    ] {
        let modules = [("test.rego", source)];
        let expected = Value::Bool(true);
        let input = Value::from_json_str(r#"{"items":["child"],"child":"child-default"}"#)?;
        assert_eq!(
            run_interpreter_modules(&modules, entry_point, input.clone())?,
            expected,
            "interpreter result for parent/child source"
        );
        let program = compile_modules(&modules, entry_point)?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name(entry_point)?,
                expected,
                "{mode:?} parent/child result"
            );
        }
    }
    Ok(())
}

#[test]
fn dynamic_default_wrapper_excludes_descendant_function_definitions() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [input.x | true]
f(x) := "parent" if x == 1
f.child(x) := "child" if x == 1
p := {
    "parent_hit": f(1),
    "parent_miss": f(2),
    "child_hit": f.child(1)
}
child_miss if { f.child(2) }
"#;
    let modules = [("test.rego", source)];
    let input = Value::from_json_str(r#"{"x":7}"#)?;
    for (entry_point, expected) in [
        (
            "data.test.p",
            Value::from_json_str(
                r#"{"parent_hit":"parent","parent_miss":[7],"child_hit":"child"}"#,
            )?,
        ),
        ("data.test.child_miss", Value::Undefined),
    ] {
        assert_eq!(
            run_interpreter_modules(&modules, entry_point, input.clone())?,
            expected,
            "interpreter result for {entry_point}"
        );
        let program = compile_modules(&modules, entry_point)?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name(entry_point)?,
                expected,
                "{mode:?} result for {entry_point}"
            );
        }
    }
    Ok(())
}

#[test]
fn dynamic_parent_default_ignores_ordinary_child_on_reused_vm() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [input.x | true]
f.child(_) := true
p := f(0)
"#;
    let modules = [("test.rego", source)];
    let cases = [
        (
            Value::from_json_str(r#"{"x":7}"#)?,
            Value::from_json_str("[7]")?,
        ),
        (
            Value::from_json_str(r#"{"x":9}"#)?,
            Value::from_json_str("[9]")?,
        ),
    ];
    let program = compile_modules(&modules, "data.test.p")?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        for (input, expected) in &cases {
            vm.set_input(input.clone());
            assert_eq!(
                vm.execute_entry_point_by_name("data.test.p")?,
                *expected,
                "{mode:?} dynamic parent default for input {input:?}"
            );
        }
    }
    for (input, expected) in &cases {
        assert_eq!(
            run_interpreter_modules(&modules, "data.test.p", input.clone())?,
            *expected,
            "interpreter dynamic parent default for input {input:?}"
        );
    }
    Ok(())
}

#[test]
fn parameterized_function_paths_remain_document_reads_and_callable_targets() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default defaulted(_) := input.fallback
ordinary(value) := value
zero() := "zero"
p := {
    "defaulted_data": data.test.defaulted,
    "ordinary_data": data.test.ordinary,
    "defaulted_call": defaulted(0),
    "ordinary_call": ordinary("ordinary"),
    "zero_arity_call": zero()
}
"#;
    let modules = [("main.rego", source)];
    let data = Value::from_json_str(
        r#"{"test":{"defaulted":"base-default","ordinary":"base-ordinary"}}"#,
    )?;
    let input = Value::from_json_str(r#"{"fallback":"default-call"}"#)?;
    let expected = Value::from_json_str(
        r#"{"defaulted_data":"base-default","ordinary_data":"base-ordinary","defaulted_call":"default-call","ordinary_call":"ordinary","zero_arity_call":"zero"}"#,
    )?;

    let mut engine = Engine::new();
    add_modules(&mut engine, &modules)?;
    engine.add_data(data.clone())?;
    engine.set_input(input.clone());
    assert_eq!(
        engine.eval_rule("data.test.p".to_string())?,
        expected,
        "interpreter must preserve data reads and callable results at the same paths"
    );

    let program = compile_modules(&modules, "data.test.p")?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_data(data.clone())?;
        vm.set_input(input.clone());
        assert_eq!(
            vm.execute_entry_point_by_name("data.test.p")?,
            expected,
            "{mode:?} must preserve data reads and callable results at the same paths"
        );
    }
    Ok(())
}

#[test]
fn default_metadata_keeps_ordinary_function_module_in_either_order() -> anyhow::Result<()> {
    let defaults = r#"package helpers
import rego.v1
default f(_) := "fallback"
"#;
    let ordinary = r#"package helpers
import rego.v1
f({"kind": "ordinary"}) := "ordinary"
"#;
    let main = r#"package main
import rego.v1
import data.helpers as helper
p := {
    "hit": helper.f({"kind": "ordinary"}),
    "miss": helper.f({"kind": "miss"})
}
"#;
    let expected = Value::from_json_str(r#"{"hit":"ordinary","miss":"fallback"}"#)?;
    for modules in [
        [
            ("defaults.rego", defaults),
            ("ordinary.rego", ordinary),
            ("main.rego", main),
        ],
        [
            ("ordinary.rego", ordinary),
            ("defaults.rego", defaults),
            ("main.rego", main),
        ],
    ] {
        assert_eq!(
            run_interpreter_modules(&modules, "data.main.p", Value::new_object())?,
            expected,
            "interpreter result for module order {modules:?}"
        );
        let program = compile_modules(&modules, "data.main.p")?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            assert_eq!(
                vm.execute_entry_point_by_name("data.main.p")?,
                expected,
                "{mode:?} result for module order {modules:?}"
            );
        }
    }
    Ok(())
}
