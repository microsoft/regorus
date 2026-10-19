// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::{Compiler, CompilerOptions};
use regorus::rvm::instructions::GuardMode;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
use regorus::rvm::Instruction;
use regorus::rvm::{BuiltinPolicy, Program};
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

fn compile_modules_with_options(
    modules: &[(&str, &str)],
    entry_point: &str,
    options: &CompilerOptions,
) -> anyhow::Result<std::sync::Arc<Program>> {
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

fn compile_rule_with_options(
    module: &str,
    options: &CompilerOptions,
) -> anyhow::Result<std::sync::Arc<Program>> {
    compile_modules_with_options(&[("test.rego", module)], "data.test.p", options)
}

fn assert_disabled_builtin_fails_compilation(builtin: &str, expression: &str) {
    let options = CompilerOptions {
        builtin_policy: builtin_policy(&[builtin]),
        ..CompilerOptions::default()
    };
    let module = format!("package test\np := {expression}");
    let error = compile_rule_with_options(&module, &options)
        .expect_err("a disabled emitted native builtin must fail compilation");
    assert!(
        error.to_string().contains(builtin),
        "expected {builtin} in the error, got: {error}"
    );
}

fn builtin_policy(names: &[&str]) -> BuiltinPolicy {
    BuiltinPolicy::from_disabled_names(names).expect("builtin names are registered")
}

#[test]
fn builtin_policy_validates_exact_registered_names_and_normalizes_duplicates() {
    let policy = builtin_policy(&["count", "count"]);
    assert_eq!(policy.disabled_names(), ["count"]);
    assert!(BuiltinPolicy::default().disabled_names().is_empty());
    assert!(BuiltinPolicy::from_disabled_names(&["not_a_registered_builtin"]).is_err());
    assert!(BuiltinPolicy::from_disabled_names(&["count..nested"]).is_err());
    assert!(BuiltinPolicy::from_disabled_names(&[" count"]).is_err());
}

#[test]
fn compiler_policy_rejects_emitted_native_builtin_calls() {
    assert_disabled_builtin_fails_compilation("count", "count([])");
}

#[cfg(feature = "http")]
#[test]
fn compiler_policy_rejects_emitted_http_send() {
    assert_disabled_builtin_fails_compilation("http.send", "http.send({})");
}

#[cfg(feature = "uuid")]
#[test]
fn compiler_policy_rejects_emitted_uuid_rfc4122() {
    assert_disabled_builtin_fails_compilation("uuid.rfc4122", "uuid.rfc4122(\"v4\")");
}

#[cfg(feature = "rand")]
#[test]
fn compiler_policy_rejects_emitted_rand_intn() {
    assert_disabled_builtin_fails_compilation("rand.intn", "rand.intn(1, 2)");
}

#[cfg(feature = "time")]
#[test]
fn compiler_policy_rejects_emitted_time_now_ns() {
    assert_disabled_builtin_fails_compilation("time.now_ns", "time.now_ns()");
}

#[test]
fn compiler_policy_rejects_emitted_set_operators_in_rules_and_comprehensions() {
    let cases = [
        ("package test\np := {1} | {2}", "__builtin_sets.union"),
        (
            "package test\np := {1} & {2}",
            "__builtin_sets.intersection",
        ),
        (
            "package test\np := [result | result := ({1} | {2})]",
            "__builtin_sets.union",
        ),
        (
            "package test\np := [result | result := ({1} & {2})]",
            "__builtin_sets.intersection",
        ),
    ];

    for (module, builtin) in cases {
        let options = CompilerOptions {
            builtin_policy: builtin_policy(&[builtin]),
            ..CompilerOptions::default()
        };
        let error = compile_rule_with_options(module, &options)
            .expect_err("a disabled emitted set operator must fail compilation");
        assert!(
            error.to_string().contains(builtin),
            "expected {builtin} in the error, got: {error}"
        );
    }
}

#[test]
fn compiler_policy_allows_unemitted_uses_in_unused_rules_and_defaults() {
    let options = CompilerOptions {
        builtin_policy: builtin_policy(&["count"]),
        ..CompilerOptions::default()
    };
    let program = compile_rule_with_options(
        r#"
package test
default p := count([])
p := true
unused := count([])
"#,
        &options,
    )
    .expect("unemitted default and unused-rule builtins are outside the emitted table");

    assert!(
        program.builtin_info_table.is_empty(),
        "unemitted source calls must not appear in Program builtin metadata"
    );
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.test.p")
            .expect("the selected rule has no disabled builtin"),
        Value::Bool(true)
    );
}

#[test]
fn compiler_policy_default_allows_emitted_set_operators() {
    let program = compile_rule(
        r#"
package test
p := ({1} | {2}) == (({2, 3} & {4, 2}) | {1, 2})
"#,
    );
    let names = program
        .builtin_info_table
        .iter()
        .map(|info| info.name.as_str())
        .collect::<BTreeSet<_>>();
    assert!(names.contains("__builtin_sets.union"));
    assert!(names.contains("__builtin_sets.intersection"));

    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.test.p")
            .expect("default policy allows set operators"),
        Value::Bool(true)
    );
}

#[test]
fn compiler_policy_does_not_mistake_user_defined_or_imported_names_for_builtins() {
    let options = CompilerOptions {
        builtin_policy: builtin_policy(&["count"]),
        ..CompilerOptions::default()
    };
    let program = compile_modules_with_options(
        &[
            ("helpers.rego", "package helpers\ncount(_) := \"helper\""),
            (
                "test.rego",
                "package test\nimport data.helpers as h\ncount(_) := \"local\"\np := count([]) == h.count([])",
            ),
        ],
        "data.test.p",
        &options,
    )
    .expect("user-defined functions are not native builtin calls");
    assert!(
        program.builtin_info_table.is_empty(),
        "user-defined functions must not create native builtin metadata"
    );
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert_eq!(
        vm.execute_entry_point_by_name("data.test.p")
            .expect("local user function remains allowed"),
        Value::Bool(false)
    );
}

#[test]
fn compiler_policy_rejects_same_native_name_host_await_but_allows_host_only_names() {
    let native_name_options = CompilerOptions {
        host_await_builtins: vec![("count".to_string(), 1)],
        builtin_policy: builtin_policy(&["count"]),
    };
    let error = compile_rule_with_options("package test\np := count([])", &native_name_options)
        .expect_err("a registered native-name HostAwait cannot bypass the compiler policy");
    assert!(error.to_string().contains("count"));

    let host_only_options = CompilerOptions {
        host_await_builtins: vec![("lookup".to_string(), 1)],
        builtin_policy: builtin_policy(&["count"]),
    };
    compile_rule_with_options("package test\np := lookup(input.value)", &host_only_options)
        .expect("a host-only identifier is not a native builtin");
}

#[test]
fn runtime_disabled_builtin_is_fatal_before_undefined_arguments() {
    let program = compile_rule("package test\np := count(input.missing)");
    let policy = builtin_policy(&["count"]);

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            let mut vm = RegoVM::new();
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(strict);
            vm.load_program(program.clone());
            vm.set_input(Value::new_object());
            vm.set_builtin_policy(policy.clone())
                .expect("policy can be applied before execution");

            let error = vm
                .execute_entry_point_by_name("data.test.p")
                .expect_err("disabled builtin calls must fail even with undefined arguments");
            assert!(
                matches!(
                    error,
                    VmError::BuiltinDisabled { ref name, .. } if name == "count"
                ),
                "disabled builtin must remain a fatal policy error, got: {error}"
            );
        }
    }
}

#[test]
fn runtime_dynamic_host_identifier_is_checked_before_response_or_suspension() {
    let program =
        compile_rule("package test\np := __builtin_host_await(input.argument, input.identifier)");
    let policy = builtin_policy(&["count"]);

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(mode);
        vm.load_program(program.clone());
        vm.set_input(Value::from_json_str(r#"{"identifier":"count"}"#).unwrap());
        vm.set_host_await_responses([(Value::from("count"), [Value::from(42)])]);
        vm.set_builtin_policy(policy.clone())
            .expect("policy can be applied before execution");

        let error = vm
            .execute_entry_point_by_name("data.test.p")
            .expect_err("disabled identifiers must fail before host handling");
        assert!(matches!(
            error,
            VmError::BuiltinDisabled { ref name, .. } if name == "count"
        ));
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Error {
                error: VmError::BuiltinDisabled { name, .. }
            } if name == "count"
        ));
    }
}

#[test]
fn runtime_disabled_native_builtin_after_resume_is_terminal_and_reusable() {
    let program = compile_rule(
        r#"package test
p := count(__builtin_host_await([], "lookup"))"#,
    );
    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_builtin_policy(builtin_policy(&["count"]))
        .expect("policy can be applied before execution");

    vm.execute_entry_point_by_name("data.test.p")
        .expect("the initial host await should suspend");
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("lookup")
    ));

    let error = vm.resume(Some(Value::new_array()));
    assert!(matches!(
        error,
        Err(VmError::BuiltinDisabled { ref name, .. }) if name == "count"
    ));
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Error {
            error: VmError::BuiltinDisabled { name, .. }
        } if name == "count"
    ));
    assert!(vm.suspend_reason().is_none());
    assert!(matches!(
        vm.resume(Some(Value::new_array())),
        Err(VmError::InvalidResumeState { .. })
    ));

    vm.set_builtin_policy(BuiltinPolicy::default())
        .expect("an empty policy should reset a terminal VM");
    assert!(matches!(vm.execution_state(), ExecutionState::Ready));

    vm.execute_entry_point_by_name("data.test.p")
        .expect("the reused VM should suspend on the host await");
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("lookup")
    ));
    assert_eq!(
        vm.resume(Some(Value::new_array()))
            .expect("the unrestricted builtin should run after reset"),
        Value::from(0)
    );
}

#[test]
fn runtime_disabled_dynamic_host_identifier_after_resume_is_terminal_and_reusable() {
    let program = compile_rule(
        r#"package test
p := __builtin_host_await([], __builtin_host_await([], "lookup"))"#,
    );
    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_host_await_responses([(Value::from("count"), [Value::from(42)])]);
    vm.set_builtin_policy(builtin_policy(&["count"]))
        .expect("policy can be applied before execution");

    vm.execute_entry_point_by_name("data.test.p")
        .expect("the inner host await should suspend");
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("lookup")
    ));

    let error = vm.resume(Some(Value::from("count")));
    assert!(matches!(
        error,
        Err(VmError::BuiltinDisabled { ref name, .. }) if name == "count"
    ));
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Error {
            error: VmError::BuiltinDisabled { name, .. }
        } if name == "count"
    ));
    assert!(vm.suspend_reason().is_none());
    assert!(matches!(
        vm.resume(Some(Value::from(42))),
        Err(VmError::InvalidResumeState { .. })
    ));

    vm.set_builtin_policy(BuiltinPolicy::default())
        .expect("an empty policy should reset a terminal VM");
    assert!(matches!(vm.execution_state(), ExecutionState::Ready));

    vm.execute_entry_point_by_name("data.test.p")
        .expect("the reused VM should suspend on the inner host await");
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("lookup")
    ));
    vm.resume(Some(Value::from("count")))
        .expect("the unrestricted outer host await should suspend");
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("count")
    ));
    assert_eq!(
        vm.resume(Some(Value::from(42)))
            .expect("the reused VM should complete after the second host await"),
        Value::from(42)
    );
}

#[test]
fn missing_host_await_resume_value_preserves_suspension() {
    let program = compile_rule("package test\np := __builtin_host_await([], \"lookup\")");
    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);

    vm.execute_entry_point_by_name("data.test.p")
        .expect("the host await should suspend");
    let error = vm
        .resume(None)
        .expect_err("a host await requires a resume value");
    assert!(matches!(error, VmError::MissingResumeValue { .. }));
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { identifier, .. },
            ..
        } if identifier == &Value::from("lookup")
    ));
    assert_eq!(
        vm.resume(Some(Value::from(7)))
            .expect("the suspended VM should remain retryable"),
        Value::from(7)
    );
}

#[test]
fn runtime_host_only_identifier_is_not_restricted_as_a_native_builtin() {
    let options = CompilerOptions {
        host_await_builtins: vec![("lookup".to_string(), 1)],
        builtin_policy: builtin_policy(&["count"]),
    };
    let program = compile_rule_with_options("package test\np := lookup(input.value)", &options)
        .expect("host-only identifiers are not native builtins");

    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_input(Value::from_json_str(r#"{"value":1}"#).unwrap());
    vm.set_builtin_policy(builtin_policy(&["count"]))
        .expect("policy can be applied before execution");
    vm.execute_entry_point_by_name("data.test.p")
        .expect("host-only HostAwait is not blocked");
    assert!(matches!(
        vm.suspend_reason(),
        Some(SuspendReason::HostAwait {
            identifier: Value::String(name),
            ..
        }) if name.as_ref() == "lookup"
    ));
}

#[test]
fn serialized_program_uses_independent_vm_builtin_policies() {
    let program = compile_rule("package test\np := count([])");
    let serialized = program
        .serialize_binary()
        .expect("serialize compiled program");
    let deserialized =
        match Program::deserialize_binary(&serialized).expect("deserialize compiled program") {
            regorus::rvm::program::DeserializationResult::Complete(program) => {
                std::sync::Arc::new(program)
            }
            regorus::rvm::program::DeserializationResult::Partial(_) => {
                panic!("compiled program should deserialize completely")
            }
        };

    let mut restricted = RegoVM::new();
    restricted.load_program(deserialized.clone());
    restricted
        .set_builtin_policy(builtin_policy(&["count"]))
        .expect("policy applies to one VM");
    assert!(matches!(
        restricted.execute_entry_point_by_name("data.test.p"),
        Err(VmError::BuiltinDisabled { name, .. }) if name == "count"
    ));

    let mut unrestricted = RegoVM::new();
    unrestricted.load_program(deserialized);
    assert_eq!(
        unrestricted
            .execute_entry_point_by_name("data.test.p")
            .expect("the shared serialized program is unrestricted in another VM"),
        Value::from(0)
    );
}

#[test]
fn builtin_policy_replacement_is_atomic_while_suspended_and_resets_after_error() {
    let host_program =
        compile_rule("package test\np := __builtin_host_await(input.argument, \"host\")");
    let mut suspended = RegoVM::new();
    suspended.set_execution_mode(ExecutionMode::Suspendable);
    suspended.load_program(host_program);
    suspended.set_input(Value::from_json_str(r#"{"argument":1}"#).unwrap());
    suspended
        .execute_entry_point_by_name("data.test.p")
        .expect("host call suspends");
    let error = suspended
        .set_builtin_policy(builtin_policy(&["count"]))
        .expect_err("policy changes are rejected while suspended");
    assert!(matches!(
        error,
        VmError::BuiltinPolicyChangeWhileExecuting { .. }
    ));
    assert!(suspended.get_builtin_policy().disabled_names().is_empty());
    assert!(matches!(
        suspended.execution_state(),
        ExecutionState::Suspended { .. }
    ));
    assert_eq!(
        suspended.resume(Some(Value::from(7))).unwrap(),
        Value::from(7)
    );

    let program = compile_rule("package test\np := count([])");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_builtin_policy(builtin_policy(&["count"]))
        .expect("policy applies before execution");
    assert!(matches!(
        vm.execute_entry_point_by_name("data.test.p"),
        Err(VmError::BuiltinDisabled { name, .. }) if name == "count"
    ));
    vm.set_builtin_policy(BuiltinPolicy::default())
        .expect("terminal error state allows policy replacement");
    assert!(matches!(vm.execution_state(), ExecutionState::Ready));
    assert_eq!(
        vm.execute_entry_point_by_name("data.test.p").unwrap(),
        Value::from(0)
    );
}
