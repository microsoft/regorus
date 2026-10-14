// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::{
    Compiler, CompilerError, CompilerOptions, SpannedCompilerError,
};
use regorus::rvm::instructions::GuardMode;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::rvm::BuiltinPolicy;
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

fn compile_rule_with_options(
    module: &str,
    options: &CompilerOptions,
) -> std::sync::Arc<regorus::rvm::program::Program> {
    let mut engine = Engine::new();
    engine
        .add_policy("test.rego".to_string(), module.to_string())
        .expect("failed to add policy");
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.test.p"))
        .expect("failed to compile policy");
    Compiler::compile_from_policy_with_options(&compiled, &["data.test.p"], options)
        .expect("failed to compile to RVM")
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
fn builtin_policy_normalizes_duplicates_and_rejects_invalid_names() {
    let policy = BuiltinPolicy::from_disabled_names(&["count", "count"])
        .expect("count is a registered builtin");
    let disabled_names = policy
        .disabled_names()
        .iter()
        .map(String::as_str)
        .collect::<Vec<_>>();
    assert_eq!(disabled_names, ["count"]);
    assert!(BuiltinPolicy::default().disabled_names().is_empty());

    for invalid_name in [
        "",
        " count",
        "count ",
        "count..value",
        "unknown_builtin_xyz",
    ] {
        assert!(
            BuiltinPolicy::from_disabled_names(&[invalid_name]).is_err(),
            "expected {invalid_name:?} to be rejected"
        );
    }
}

#[test]
fn disabled_native_builtin_is_rejected_with_a_source_span() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".to_string(),
            "package test\np := count([])".to_string(),
        )
        .expect("failed to add policy");
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.test.p"))
        .expect("failed to compile policy");
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["count"])
            .expect("count is a registered builtin"),
    };

    let error = Compiler::compile_from_policy_with_options(&compiled, &["data.test.p"], &options)
        .expect_err("disabled native call must fail compilation");
    assert!(matches!(
        error.error,
        CompilerError::BuiltinDisabled { ref name } if name == "count"
    ));
    assert!(
        error.span.is_some(),
        "disabled calls must retain source spans"
    );
}

fn compile_modules_with_options(
    modules: &[(&str, &str)],
    entry_point: &str,
    options: &CompilerOptions,
) -> anyhow::Result<std::sync::Arc<regorus::rvm::program::Program>> {
    let mut engine = Engine::new();
    for (id, content) in modules {
        engine.add_policy((*id).to_string(), (*content).to_string())?;
    }
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry_point))?;
    Ok(Compiler::compile_from_policy_with_options(
        &compiled,
        &[entry_point],
        options,
    )?)
}

fn disabled_count_options() -> CompilerOptions {
    CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["count"])
            .expect("count is a registered builtin"),
    }
}

fn assert_count_is_disabled(
    result: anyhow::Result<std::sync::Arc<regorus::rvm::program::Program>>,
) {
    let error = result.expect_err("disabled count call must fail compilation");
    assert!(
        error.to_string().contains("Builtin 'count' is disabled"),
        "unexpected compilation error: {error}"
    );
}

fn assert_builtin_disabled_with_span(
    result: anyhow::Result<std::sync::Arc<regorus::rvm::program::Program>>,
    name: &str,
    source_path: &str,
    source: &str,
    call: &str,
    line: u32,
) {
    let error = result.expect_err("disabled native call must fail compilation");
    let error = error
        .downcast_ref::<SpannedCompilerError>()
        .expect("compilation must preserve the typed spanned error");
    assert!(matches!(
        &error.error,
        CompilerError::BuiltinDisabled { name: disabled } if disabled == name
    ));

    let span = error
        .span
        .as_ref()
        .expect("disabled call must retain its span");
    assert_eq!(span.source.get_path(), source_path);
    assert_eq!(span.line, line);
    assert_eq!(
        span.start,
        u32::try_from(source.find(call).expect("call must exist in fixture"))
            .expect("fixture offset fits in u32")
    );
    assert_eq!(span.text(), call);
}

#[test]
fn disabled_builtin_call_is_not_hidden_by_same_name_value_rule() {
    let source = "package test\ncount := true\np := true\nunused := count([])";
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("main.rego", source)],
            "data.test.p",
            &disabled_count_options(),
        ),
        "count",
        "main.rego",
        source,
        "count([])",
        4,
    );
}

#[test]
fn disabled_builtin_call_is_not_hidden_by_rule_prefix_in_unused_module() {
    let main = "package main\np := true";
    let unused = "package unused\ncount.child := true\nq := count([])";
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("main.rego", main), ("unused.rego", unused)],
            "data.main.p",
            &disabled_count_options(),
        ),
        "count",
        "unused.rego",
        unused,
        "count([])",
        3,
    );
}

#[cfg(feature = "http")]
#[test]
fn disabled_http_send_calls_are_not_hidden_by_value_or_prefix_rules() {
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };

    let value_rule = "package test\nhttp.send := true\np := true\nunused := http.send({})";
    assert_builtin_disabled_with_span(
        compile_modules_with_options(&[("value.rego", value_rule)], "data.test.p", &options),
        "http.send",
        "value.rego",
        value_rule,
        "http.send({})",
        4,
    );

    let main = "package main\np := true";
    let unused = "package unused\nhttp.send.child := true\nq := http.send({})";
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("main.rego", main), ("unused.rego", unused)],
            "data.main.p",
            &options,
        ),
        "http.send",
        "unused.rego",
        unused,
        "http.send({})",
        3,
    );
}

#[test]
fn empty_builtin_policy_preserves_value_and_prefix_rule_collisions() {
    let empty_options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&[])
            .expect("an empty builtin policy is valid"),
    };

    for options in [CompilerOptions::default(), empty_options] {
        let value_rule_program = compile_modules_with_options(
            &[(
                "main.rego",
                "package main\ncount := true\np := true\nunused := count([])",
            )],
            "data.main.p",
            &options,
        )
        .expect("default and explicit-empty policies preserve value-rule compilation");
        let mut vm = RegoVM::new();
        vm.load_program(value_rule_program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.main.p")
                .expect("evaluate entry point"),
            Value::from(true)
        );

        let prefix_rule_program = compile_modules_with_options(
            &[
                ("main.rego", "package main\np := true"),
                (
                    "unused.rego",
                    "package unused\ncount.child := true\nq := count([])",
                ),
            ],
            "data.main.p",
            &options,
        )
        .expect("default and explicit-empty policies preserve prefix-rule compilation");
        let mut vm = RegoVM::new();
        vm.load_program(prefix_rule_program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.main.p")
                .expect("evaluate entry point"),
            Value::from(true)
        );
    }
}

#[test]
fn disabled_builtin_name_preserves_local_default_function() {
    let main = r#"package main
import rego.v1

default count(_) := "fallback"
count(value) := "local" if value == "local"

p := count("local")
"#;
    let program = compile_modules_with_options(
        &[("main.rego", main)],
        "data.main.p",
        &disabled_count_options(),
    )
    .expect("a local default function takes precedence over a disabled builtin name");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.main.p")
            .expect("evaluate local function"),
        Value::from("local")
    );
}

#[test]
fn disabled_builtin_name_preserves_unused_local_default_function() {
    let main = r#"package main
import rego.v1

default count(_) := "fallback"
p := true
unused := count([])
"#;
    let program = compile_modules_with_options(
        &[("main.rego", main)],
        "data.main.p",
        &disabled_count_options(),
    )
    .expect("an unused local default function must not be mistaken for the disabled builtin");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.main.p")
            .expect("evaluate entry point"),
        Value::from(true)
    );
}

#[test]
fn disabled_builtin_name_preserves_unused_imported_default_functions() {
    let helper = r#"package helpers
import rego.v1
default count(_) := "fallback"
"#;
    let main = "package main\np := true";
    let qualified = r#"package qualified
import rego.v1
unused := data.helpers.count([])
"#;
    let imported = r#"package imported
import rego.v1
import data.helpers
unused := helpers.count([])
"#;
    let aliased = r#"package aliased
import rego.v1
import data.helpers as h
unused := h.count([])
"#;
    let program = compile_modules_with_options(
        &[
            ("helpers.rego", helper),
            ("main.rego", main),
            ("qualified.rego", qualified),
            ("imported.rego", imported),
            ("aliased.rego", aliased),
        ],
        "data.main.p",
        &disabled_count_options(),
    )
    .expect(
        "unused calls through package paths and import aliases must resolve to default functions",
    );
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.main.p")
            .expect("evaluate entry point"),
        Value::from(true)
    );
}

#[test]
fn disabled_builtin_name_preserves_unused_directly_imported_default_function() {
    let helper = r#"package helpers
import rego.v1
default count(_) := "fallback"
"#;
    let main = "package main\np := true";
    let imported = r#"package direct_import
import rego.v1
import data.helpers.count as count
unused := count([])
"#;
    let program = compile_modules_with_options(
        &[
            ("helpers.rego", helper),
            ("main.rego", main),
            ("direct_import.rego", imported),
        ],
        "data.main.p",
        &disabled_count_options(),
    )
    .expect("a direct import alias to a default function is not the disabled builtin");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.main.p")
            .expect("evaluate entry point"),
        Value::from(true)
    );
}

#[cfg(feature = "http")]
#[test]
fn disabled_http_send_preserves_unused_import_alias_to_default_function() {
    let helper = r#"package helpers
import rego.v1
default send(_) := "fallback"
"#;
    let main = r#"package main
import rego.v1
import data.helpers as http
p := true
unused := http.send({})
"#;
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };
    let program = compile_modules_with_options(
        &[("helper.rego", helper), ("main.rego", main)],
        "data.main.p",
        &options,
    )
    .expect("an alias targeting a default user function is not the disabled native builtin");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.main.p")
            .expect("evaluate entry point"),
        Value::from(true)
    );
}

#[cfg(feature = "http")]
#[test]
fn disabled_http_send_is_not_hidden_by_imported_default_value_or_function_prefix() {
    let main = r#"package main
import rego.v1
import data.helpers as http
p := true
unused := http.send({})
"#;
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };

    let default_value = r#"package helpers
import rego.v1
default send := true
"#;
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("value.rego", default_value), ("main.rego", main)],
            "data.main.p",
            &options,
        ),
        "http.send",
        "main.rego",
        main,
        "http.send({})",
        5,
    );

    let default_function = r#"package helpers
import rego.v1
default send.child(_) := "fallback"
"#;
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("function.rego", default_function), ("main.rego", main)],
            "data.main.p",
            &options,
        ),
        "http.send",
        "main.rego",
        main,
        "http.send({})",
        5,
    );
}

#[cfg(feature = "http")]
#[test]
fn r3_local_http_send_value_and_default_child_do_not_hide_disabled_builtin() {
    let source = r#"package main
import rego.v1
http.send := true
default http.send.child(_) := "fallback"
p := true
unused := http.send({})
"#;
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };
    assert_builtin_disabled_with_span(
        compile_modules_with_options(&[("main.rego", source)], "data.main.p", &options),
        "http.send",
        "main.rego",
        source,
        "http.send({})",
        6,
    );
}

#[cfg(feature = "http")]
#[test]
fn r3_local_default_value_and_default_child_do_not_hide_disabled_builtin() {
    let source = r#"package main
import rego.v1
default http.send := true
default http.send.child(_) := "fallback"
p := true
unused := http.send({})
"#;
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };
    assert_builtin_disabled_with_span(
        compile_modules_with_options(&[("main.rego", source)], "data.main.p", &options),
        "http.send",
        "main.rego",
        source,
        "http.send({})",
        6,
    );
}

#[test]
fn r3_local_count_value_and_default_child_do_not_hide_disabled_builtin() {
    let source = r#"package main
import rego.v1
count := true
default count.child(_) := "fallback"
p := true
unused := count([])
"#;
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("main.rego", source)],
            "data.main.p",
            &disabled_count_options(),
        ),
        "count",
        "main.rego",
        source,
        "count([])",
        6,
    );
}

#[test]
fn r3_local_default_count_value_and_default_child_do_not_hide_disabled_builtin() {
    let source = r#"package main
import rego.v1
default count := true
default count.child(_) := "fallback"
p := true
unused := count([])
"#;
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("main.rego", source)],
            "data.main.p",
            &disabled_count_options(),
        ),
        "count",
        "main.rego",
        source,
        "count([])",
        6,
    );
}

#[cfg(feature = "http")]
#[test]
fn r3_imported_http_send_value_and_default_child_do_not_hide_disabled_builtin() {
    let helper = r#"package helpers
import rego.v1
send := true
default send.child(_) := "fallback"
"#;
    let main = r#"package main
import rego.v1
import data.helpers as http
p := true
unused := http.send({})
"#;
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("helper.rego", helper), ("main.rego", main)],
            "data.main.p",
            &options,
        ),
        "http.send",
        "main.rego",
        main,
        "http.send({})",
        5,
    );
}

#[cfg(feature = "http")]
#[test]
fn r3_imported_default_http_send_value_and_default_child_do_not_hide_disabled_builtin() {
    let helper = r#"package helpers
import rego.v1
default send := true
default send.child(_) := "fallback"
"#;
    let main = r#"package main
import rego.v1
import data.helpers as http
p := true
unused := http.send({})
"#;
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("helper.rego", helper), ("main.rego", main)],
            "data.main.p",
            &options,
        ),
        "http.send",
        "main.rego",
        main,
        "http.send({})",
        5,
    );
}

#[test]
fn r3_directly_imported_count_value_and_default_child_do_not_hide_disabled_builtin() {
    let helper = r#"package helpers
import rego.v1
count := true
default count.child(_) := "fallback"
"#;
    let main = r#"package main
import rego.v1
import data.helpers.count as count
p := true
unused := count([])
"#;
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("helper.rego", helper), ("main.rego", main)],
            "data.main.p",
            &disabled_count_options(),
        ),
        "count",
        "main.rego",
        main,
        "count([])",
        5,
    );
}

#[test]
fn r3_directly_imported_default_count_value_and_default_child_do_not_hide_disabled_builtin() {
    let helper = r#"package helpers
import rego.v1
default count := true
default count.child(_) := "fallback"
"#;
    let main = r#"package main
import rego.v1
import data.helpers.count as count
p := true
unused := count([])
"#;
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("helper.rego", helper), ("main.rego", main)],
            "data.main.p",
            &disabled_count_options(),
        ),
        "count",
        "main.rego",
        main,
        "count([])",
        5,
    );
}

#[test]
fn r3_default_function_path_is_owned_by_its_package_in_either_module_order() {
    let helper = r#"package helpers
import rego.v1
default count(_) := "helper"
"#;
    let main = r#"package main
import rego.v1
count := true
default count.child(_) := "fallback"
p := true
unused := count([])
"#;
    let options = disabled_count_options();

    for modules in [
        [("helper.rego", helper), ("main.rego", main)],
        [("main.rego", main), ("helper.rego", helper)],
    ] {
        assert_builtin_disabled_with_span(
            compile_modules_with_options(&modules, "data.main.p", &options),
            "count",
            "main.rego",
            main,
            "count([])",
            6,
        );
    }
}

#[test]
fn r3_unused_module_value_and_default_child_do_not_hide_disabled_builtin() {
    let main = "package main\np := true";
    let unused = r#"package unused
import rego.v1
count := true
default count.child(_) := "fallback"
q := count([])
"#;
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("main.rego", main), ("unused.rego", unused)],
            "data.main.p",
            &disabled_count_options(),
        ),
        "count",
        "unused.rego",
        unused,
        "count([])",
        5,
    );
}

#[test]
fn empty_builtin_policy_preserves_unused_default_function_call() {
    let main = r#"package main
import rego.v1
default count(_) := "fallback"
p := true
unused := count([])
"#;
    let empty_options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&[])
            .expect("an empty builtin policy is valid"),
    };

    for options in [CompilerOptions::default(), empty_options] {
        let program = compile_modules_with_options(&[("main.rego", main)], "data.main.p", &options)
            .expect("default and explicit-empty policies preserve default-function compilation");
        let mut vm = RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.main.p")
                .expect("evaluate entry point"),
            Value::from(true)
        );
    }
}

#[test]
fn disabled_builtin_call_is_not_hidden_by_default_value_rule() {
    let source =
        "package main\nimport rego.v1\ndefault count := true\np := true\nunused := count([])";
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("main.rego", source)],
            "data.main.p",
            &disabled_count_options(),
        ),
        "count",
        "main.rego",
        source,
        "count([])",
        5,
    );
}

#[test]
fn disabled_builtin_call_is_not_hidden_by_default_function_under_rule_prefix() {
    let source =
        "package unused\nimport rego.v1\ndefault count.child(_) := \"fallback\"\nq := count([])";
    assert_builtin_disabled_with_span(
        compile_modules_with_options(
            &[("unused.rego", source)],
            "data.unused.q",
            &disabled_count_options(),
        ),
        "count",
        "unused.rego",
        source,
        "count([])",
        4,
    );
}

#[test]
fn r3_namespace_import_resolves_callable_default_with_disabled_native_builtin() {
    let helper = r#"package helpers["1.0.0"]
import rego.v1
default count(_) := "fallback"
"#;
    let main = r#"package main["2.0.0"]
import rego.v1
import data.helpers["1.0.0"].count as count
p := count([])
"#;
    let entry_point = r#"data.main["2.0.0"].p"#;
    let module_orders = [
        [("helper.rego", helper), ("main.rego", main)],
        [("main.rego", main), ("helper.rego", helper)],
    ];

    for modules in module_orders {
        let program =
            compile_modules_with_options(&modules, entry_point, &disabled_count_options())
                .expect("an imported callable default must take precedence over disabled count");
        let mut vm = RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name(entry_point)
                .expect("evaluate versioned namespace entry point"),
            Value::from("fallback")
        );
    }
}

#[test]
fn r3_namespace_import_rejects_value_and_prefix_alias_as_disabled_builtin() {
    let helper = r#"package helpers["1.0.0"]
import rego.v1
count := true
default count.child(_) := "fallback"
"#;
    let main = r#"package main["2.0.0"]
import rego.v1
import data.helpers["1.0.0"].count as count
p := true
unused := count([])
"#;
    let module_orders = [
        [("helper.rego", helper), ("main.rego", main)],
        [("main.rego", main), ("helper.rego", helper)],
    ];

    for modules in module_orders {
        assert_builtin_disabled_with_span(
            compile_modules_with_options(
                &modules,
                r#"data.main["2.0.0"].p"#,
                &disabled_count_options(),
            ),
            "count",
            "main.rego",
            main,
            "count([])",
            5,
        );
    }
}

#[test]
fn disabled_registered_host_keeps_precedence_over_same_name_default_function() {
    let source = "package main\nimport rego.v1\ndefault count(_) := \"fallback\"\np := true\nunused := count([])";
    let mut options = disabled_count_options();
    options.host_await_builtins = vec![("count".to_string(), 1)];
    assert_builtin_disabled_with_span(
        compile_modules_with_options(&[("main.rego", source)], "data.main.p", &options),
        "count",
        "main.rego",
        source,
        "count([])",
        5,
    );
}

#[test]
fn disabled_builtin_name_preserves_qualified_and_imported_user_functions() {
    let helper = r#"package helpers
count(_) := "helper"
"#;
    let main = r#"package main
import rego.v1
import data.helpers

p := {
    "qualified": data.helpers.count("argument"),
    "imported": helpers.count("argument"),
}
"#;
    let program = compile_modules_with_options(
        &[("helper.rego", helper), ("main.rego", main)],
        "data.main.p",
        &disabled_count_options(),
    )
    .expect("genuine functions must take precedence over disabled builtin names");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.main.p")
            .expect("evaluate qualified and imported functions"),
        Value::from_json_str(r#"{"qualified":"helper","imported":"helper"}"#)
            .expect("valid expected object")
    );
}

#[cfg(feature = "http")]
#[test]
fn disabled_http_send_allows_import_alias_to_genuine_user_send() {
    let helper = r#"package helpers
send(_) := "user send"
"#;
    let main = r#"package main
import data.helpers as http
p := http.send({})
"#;
    let options = CompilerOptions {
        host_await_builtins: Vec::new(),
        builtin_policy: BuiltinPolicy::from_disabled_names(&["http.send"])
            .expect("http.send is registered with the http feature"),
    };
    let program = compile_modules_with_options(
        &[("helper.rego", helper), ("main.rego", main)],
        "data.main.p",
        &options,
    )
    .expect("an import alias targeting a genuine function is not a builtin call");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.main.p")
            .expect("evaluate aliased user function"),
        Value::from("user send")
    );
}

#[test]
fn disabled_native_calls_are_rejected_in_all_loaded_modules_and_rules() {
    let options = disabled_count_options();

    assert_count_is_disabled(compile_modules_with_options(
        &[("main.rego", "package main\np := true\nunused := count([])")],
        "data.main.p",
        &options,
    ));

    assert_count_is_disabled(compile_modules_with_options(
        &[
            ("main.rego", "package main\np := true"),
            ("unused.rego", "package unused\nq := count([])"),
        ],
        "data.main.p",
        &options,
    ));

    assert_count_is_disabled(compile_modules_with_options(
        &[
            ("helpers.rego", "package helpers\nsize(xs) := count(xs)"),
            (
                "main.rego",
                "package main\nimport data.helpers as h\np := h.size([])",
            ),
        ],
        "data.main.p",
        &options,
    ));
}

#[test]
fn disabled_native_calls_are_found_in_nested_ast_paths() {
    let options = disabled_count_options();
    let modules = [
        (
            "comprehension.rego",
            "package test\np := true\nq := [count([]) | some x in [1]]",
        ),
        (
            "default.rego",
            "package test\np := true\ndefault q := count([])",
        ),
        (
            "else.rego",
            "package test\np := true\nq := true if { false } else := count([]) if { true }",
        ),
        (
            "every.rego",
            "package test\nimport rego.v1\np := true\nq if { every x in [1] { count([]) == 0 } }",
        ),
        (
            "with.rego",
            "package test\np := true\nq if { data.test.p with input as count([]) }",
        ),
    ];

    for (id, module) in modules {
        assert_count_is_disabled(compile_modules_with_options(
            &[(id, module)],
            "data.test.p",
            &options,
        ));
    }
}

#[test]
fn disabled_builtin_policy_preserves_user_functions_and_ignores_text() {
    let options = disabled_count_options();
    let program = compile_modules_with_options(
        &[(
            "test.rego",
            r#"package test
count(xs) := "user"
p := count([])
q := "count([])" # count([])
unused := unknown_function([])
"#,
        )],
        "data.test.p",
        &options,
    )
    .expect("user functions, strings, comments, and unused unknown calls are not builtins");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.test.p").unwrap(),
        Value::from("user")
    );
}

#[test]
fn disabled_registered_and_static_host_calls_are_rejected() {
    let registered = CompilerOptions {
        host_await_builtins: vec![("count".to_string(), 1)],
        builtin_policy: BuiltinPolicy::from_disabled_names(&["count"])
            .expect("count is a registered builtin"),
    };
    assert_count_is_disabled(compile_modules_with_options(
        &[("test.rego", "package test\np := count([])")],
        "data.test.p",
        &registered,
    ));

    let options = disabled_count_options();
    assert_count_is_disabled(compile_modules_with_options(
        &[(
            "test.rego",
            r#"package test
p := __builtin_host_await([], "count")
"#,
        )],
        "data.test.p",
        &options,
    ));
}

#[test]
fn runtime_disabled_builtin_is_hard_before_undefined_arguments() {
    let program = compile_rule(
        r#"
        package test
        p := count(input.missing)
    "#,
    );
    let policy =
        BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin");

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            for entry_point in 0..3 {
                let mut vm = RegoVM::new();
                vm.set_execution_mode(mode);
                vm.set_strict_builtin_errors(strict);
                vm.load_program(program.clone());
                vm.set_input(Value::new_object());
                vm.set_builtin_policy(policy.clone())
                    .expect("policy can be set before execution");

                let result = match entry_point {
                    0 => vm.execute(),
                    1 => vm.execute_entry_point_by_name("data.test.p"),
                    _ => vm.execute_entry_point_by_index(0),
                };
                let error = result.expect_err("disabled calls must fail in every execution mode");
                assert!(
                    matches!(
                        &error,
                        VmError::BuiltinDisabled { name, .. } if name == "count"
                    ),
                    "unexpected runtime error: {error}"
                );
                assert!(matches!(
                    vm.execution_state(),
                    ExecutionState::Error {
                        error: VmError::BuiltinDisabled { name, .. }
                    } if name == "count"
                ));
            }
        }
    }
}

#[test]
fn runtime_dynamic_host_identifier_is_checked_before_response_or_suspension() {
    let program = compile_rule(
        r#"
        package test
        p := __builtin_host_await(input.argument, input.identifier)
    "#,
    );
    let policy =
        BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin");

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(mode);
        vm.load_program(program.clone());
        vm.set_input(Value::from_json_str(r#"{"identifier":"count"}"#).expect("valid JSON input"));
        vm.set_host_await_responses([(Value::from("count"), [Value::from(42)])]);
        vm.set_builtin_policy(policy.clone())
            .expect("policy can be set before execution");

        let error = vm
            .execute()
            .expect_err("a disabled dynamic host identifier must fail before host handling");
        assert!(
            matches!(
                &error,
                VmError::BuiltinDisabled { name, .. } if name == "count"
            ),
            "unexpected runtime error: {error}"
        );
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Error {
                error: VmError::BuiltinDisabled { name, .. }
            } if name == "count"
        ));
    }
}

#[test]
fn runtime_registered_host_builtin_is_guarded_on_precompiled_programs() {
    let options = CompilerOptions {
        host_await_builtins: vec![("count".to_string(), 1)],
        builtin_policy: BuiltinPolicy::default(),
    };
    let program = compile_rule_with_options("package test\np := count(input.argument)", &options);
    let policy =
        BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin");

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(mode);
        vm.load_program(program.clone());
        vm.set_input(Value::from_json_str(r#"{"argument":1}"#).unwrap());
        vm.set_host_await_responses([(Value::from("count"), [Value::from(42)])]);
        vm.set_builtin_policy(policy.clone())
            .expect("policy can be set before execution");

        let error = vm
            .execute()
            .expect_err("disabled registered host calls must not yield or use responses");
        assert!(matches!(
            &error,
            VmError::BuiltinDisabled { name, .. } if name == "count"
        ));
    }
}

#[test]
fn builtin_policy_is_per_vm_survives_load_and_can_be_replaced_after_error() {
    let program = compile_rule(
        r#"
        package test
        p := count(input.missing)
    "#,
    );
    let policy =
        BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin");

    let mut denied_vm = RegoVM::new();
    denied_vm.set_builtin_policy(policy.clone()).unwrap();
    denied_vm.load_program(program.clone());
    denied_vm.set_input(Value::new_object());
    let error = denied_vm
        .execute_entry_point_by_name("data.test.p")
        .unwrap_err();
    assert!(matches!(
        &error,
        VmError::BuiltinDisabled { name, .. } if name == "count"
    ));

    let mut allowed_vm = RegoVM::new();
    allowed_vm.load_program(program);
    allowed_vm.set_input(Value::new_object());
    assert_eq!(
        allowed_vm
            .execute_entry_point_by_name("data.test.p")
            .unwrap(),
        Value::Undefined
    );

    denied_vm
        .set_builtin_policy(BuiltinPolicy::default())
        .expect("terminal VM can change policy");
    assert!(matches!(denied_vm.execution_state(), ExecutionState::Ready));
    assert_eq!(
        denied_vm
            .execute_entry_point_by_name("data.test.p")
            .unwrap(),
        Value::Undefined
    );
}

#[test]
fn serialized_program_enforces_policy_independently_per_vm() {
    let program = compile_rule("package test\np := count([])");
    let serialized = program
        .serialize_binary()
        .expect("serialize compiled program");
    let deserialized = match regorus::rvm::program::Program::deserialize_binary(&serialized)
        .expect("deserialize compiled program")
    {
        regorus::rvm::program::DeserializationResult::Complete(program) => {
            std::sync::Arc::new(program)
        }
        regorus::rvm::program::DeserializationResult::Partial(_) => {
            panic!("compiled program should deserialize completely")
        }
    };

    let policy =
        BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin");
    let mut denied_vm = RegoVM::new();
    denied_vm.load_program(deserialized.clone());
    denied_vm
        .set_builtin_policy(policy)
        .expect("policy can be set for deserialized program");
    assert!(matches!(
        denied_vm.execute_entry_point_by_name("data.test.p"),
        Err(VmError::BuiltinDisabled { name, .. }) if name == "count"
    ));

    let mut allowed_vm = RegoVM::new();
    allowed_vm.load_program(deserialized);
    assert_eq!(
        allowed_vm
            .execute_entry_point_by_name("data.test.p")
            .expect("the same deserialized program remains allowed in another VM"),
        Value::from(0)
    );
}

#[test]
fn builtin_policy_change_is_rejected_atomically_while_suspended() {
    let program = compile_rule(
        r#"
        package test
        p := __builtin_host_await(input.argument, "other")
    "#,
    );
    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_input(Value::from_json_str(r#"{"argument":1}"#).unwrap());
    assert_eq!(vm.execute().unwrap(), Value::Undefined);
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended { .. }
    ));

    let error = vm
        .set_builtin_policy(
            BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin"),
        )
        .expect_err("policy changes must be rejected while suspended");
    assert!(matches!(
        error,
        VmError::BuiltinPolicyChangeWhileExecuting { .. }
    ));
    assert!(vm.get_builtin_policy().disabled_names().is_empty());
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended { .. }
    ));
    assert_eq!(vm.resume(Some(Value::from(7))).unwrap(), Value::from(7));
}

#[cfg(feature = "http")]
#[test]
fn default_http_send_remains_undefined_in_interpreter_and_rvm() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".to_string(),
            "package test\np := http.send({})".to_string(),
        )
        .expect("add policy");

    assert_eq!(
        engine
            .eval_rule("data.test.p".to_string())
            .expect("evaluate in interpreter"),
        Value::Undefined
    );

    let entry_point = "data.test.p";
    let compiled = engine
        .compile_with_entrypoint(&Rc::from(entry_point))
        .expect("compile policy");
    let program = Compiler::compile_from_policy(&compiled, &[entry_point]).expect("compile to RVM");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name(entry_point)
            .expect("evaluate in RVM"),
        Value::Undefined
    );
}

#[test]
fn disabled_native_error_during_resume_leaves_vm_in_error_state() {
    let program = compile_rule(
        r#"
        package test
        p := __builtin_host_await(input.argument, "other") + count(input.missing)
    "#,
    );
    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_input(Value::new_object());
    vm.set_builtin_policy(
        BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin"),
    )
    .unwrap();

    vm.execute().expect("first host await is permitted");
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: regorus::rvm::vm::SuspendReason::HostAwait { .. },
            ..
        }
    ));

    let error = vm
        .resume(Some(Value::from(1)))
        .expect_err("disabled native call must fail during resume");
    assert!(matches!(
        &error,
        VmError::BuiltinDisabled { name, .. } if name == "count"
    ));
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Error {
            error: VmError::BuiltinDisabled { name, .. }
        } if name == "count"
    ));
}
