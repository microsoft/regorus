// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
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

// --- AssertEq fusion tests ---

/// Count occurrences of a specific instruction pattern in the program.
fn count_instructions(
    program: &regorus::rvm::program::Program,
    pred: impl Fn(&Instruction) -> bool,
) -> usize {
    program.instructions.iter().filter(|i| pred(i)).count()
}

#[test]
fn equality_check_emits_assert_eq() {
    // Assignment `x = 1` followed by `x = 1` triggers EqualityCheck in destructuring.
    let program = compile_rule(
        r#"
        package test
        p if { x = 1; x = 1 }
    "#,
    );
    let assert_eq_count =
        count_instructions(&program, |i| matches!(i, Instruction::AssertEq { .. }));
    assert!(
        assert_eq_count > 0,
        "expected AssertEq instruction for equality check"
    );
}

#[test]
fn destructuring_equality_emits_assert_eq() {
    let program = compile_rule(
        r#"
        package test
        p if { [1, x] := [1, 2] }
    "#,
    );
    let assert_eq_count =
        count_instructions(&program, |i| matches!(i, Instruction::AssertEq { .. }));
    assert!(
        assert_eq_count > 0,
        "expected AssertEq for destructuring equality"
    );
}
