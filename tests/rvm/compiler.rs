// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::instructions::GuardMode;
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
    let expected_set = Value::Set(Rc::new(
        [1, 2, 3]
            .into_iter()
            .map(Value::from)
            .collect::<BTreeSet<_>>(),
    ));
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
