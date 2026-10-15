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

#[derive(Clone, Copy, Debug)]
enum R3DefaultDiagStyle {
    Plain,
    Literal,
}

#[derive(Clone, Copy, Debug)]
enum R3DefaultDiagModuleOrder {
    HelperFirst,
    MainFirst,
}

#[derive(Clone, Copy, Debug)]
enum R3DefaultDiagBuiltinPolicy {
    Default,
    Disabled,
}

#[derive(Clone, Copy, Debug)]
enum R3DefaultDiagBehavior {
    Value,
    Undefined,
    Output,
    Arity,
}

#[derive(Debug)]
struct R3DefaultDiagObservations {
    compilation: Result<(), String>,
    interpreter: Result<Value, String>,
    run_to_completion: Option<Result<Value, VmError>>,
    suspendable: Option<Result<Value, VmError>>,
}

fn run_r3_default_diag_vm(
    program: std::sync::Arc<regorus::rvm::program::Program>,
    entry_point: &str,
    execution_mode: ExecutionMode,
    builtin_policy: R3DefaultDiagBuiltinPolicy,
) -> Result<Value, VmError> {
    let mut vm = RegoVM::new();
    vm.set_execution_mode(execution_mode);
    vm.load_program(program);
    vm.set_input(Value::new_object());
    if matches!(builtin_policy, R3DefaultDiagBuiltinPolicy::Disabled) {
        vm.set_builtin_policy(
            BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin"),
        )?;
    }
    vm.execute_entry_point_by_name(entry_point)
}

fn observe_r3_default_diag(
    style: R3DefaultDiagStyle,
    module_order: R3DefaultDiagModuleOrder,
    builtin_policy: R3DefaultDiagBuiltinPolicy,
    behavior: R3DefaultDiagBehavior,
) -> R3DefaultDiagObservations {
    let (helper_package, main_package, helper_import, entry_point) = match style {
        R3DefaultDiagStyle::Plain => (
            "helpers",
            "main",
            "import data.helpers.count as count",
            "data.main.p",
        ),
        R3DefaultDiagStyle::Literal => (
            "helpers[\"1.0.0\"]",
            "main[\"2.0.0\"]",
            "import data.helpers[\"1.0.0\"].count as count",
            "data.main[\"2.0.0\"].p",
        ),
    };
    let helper =
        format!("package {helper_package}\nimport rego.v1\ndefault count(_) := \"fallback\"\n");
    let expression = match behavior {
        R3DefaultDiagBehavior::Value => "p := count([])",
        R3DefaultDiagBehavior::Undefined => "p := count(input.missing)",
        R3DefaultDiagBehavior::Output => "p := result if { count([], result) }",
        R3DefaultDiagBehavior::Arity => "p := count([], [], [])",
    };
    let main = format!("package {main_package}\nimport rego.v1\n{helper_import}\n{expression}\n");
    let modules = match module_order {
        R3DefaultDiagModuleOrder::HelperFirst => vec![
            ("helper.rego", helper.as_str()),
            ("main.rego", main.as_str()),
        ],
        R3DefaultDiagModuleOrder::MainFirst => vec![
            ("main.rego", main.as_str()),
            ("helper.rego", helper.as_str()),
        ],
    };

    let mut engine = Engine::new();
    let mut interpreter_setup = Ok(());
    for (module_path, module) in &modules {
        if let Err(error) = engine.add_policy((*module_path).to_string(), (*module).to_string()) {
            interpreter_setup = Err(error.to_string());
            break;
        }
    }
    engine.set_input(Value::new_object());
    let interpreter = interpreter_setup.and_then(|()| {
        engine
            .eval_rule(entry_point.to_string())
            .map_err(|error| error.to_string())
    });

    let options = match builtin_policy {
        R3DefaultDiagBuiltinPolicy::Default => CompilerOptions::default(),
        R3DefaultDiagBuiltinPolicy::Disabled => disabled_count_options(),
    };
    let compiled_program = compile_modules_with_options(&modules, entry_point, &options);
    match compiled_program {
        Ok(program) => R3DefaultDiagObservations {
            compilation: Ok(()),
            interpreter,
            run_to_completion: Some(run_r3_default_diag_vm(
                program.clone(),
                entry_point,
                ExecutionMode::RunToCompletion,
                builtin_policy,
            )),
            suspendable: Some(run_r3_default_diag_vm(
                program,
                entry_point,
                ExecutionMode::Suspendable,
                builtin_policy,
            )),
        },
        Err(error) => {
            let error = format!("RVM compilation failed: {error}");
            R3DefaultDiagObservations {
                compilation: Err(error.clone()),
                interpreter,
                run_to_completion: None,
                suspendable: None,
            }
        }
    }
}

fn assert_r3_default_diag(
    test_name: &str,
    behavior: R3DefaultDiagBehavior,
    observations: &R3DefaultDiagObservations,
) {
    assert!(
        observations.compilation.is_ok(),
        "{test_name}: RVM compilation must succeed before each execution; observations: {observations:?}"
    );

    let run_to_completion = observations
        .run_to_completion
        .as_ref()
        .expect("RunToCompletion VM must execute after successful compilation");
    let suspendable = observations
        .suspendable
        .as_ref()
        .expect("Suspendable VM must execute after successful compilation");

    match behavior {
        R3DefaultDiagBehavior::Value | R3DefaultDiagBehavior::Output => {
            let expected = Value::from("fallback");
            assert_eq!(
                observations.interpreter.as_ref().ok(),
                Some(&expected),
                "{test_name} (interpreter): observations: {observations:?}"
            );
            assert_eq!(
                run_to_completion.as_ref().ok(),
                Some(&expected),
                "{test_name} (RunToCompletion): observations: {observations:?}"
            );
            assert_eq!(
                suspendable.as_ref().ok(),
                Some(&expected),
                "{test_name} (Suspendable): observations: {observations:?}"
            );
        }
        R3DefaultDiagBehavior::Undefined => {
            let expected = Value::Undefined;
            assert_eq!(
                observations.interpreter.as_ref().ok(),
                Some(&expected),
                "{test_name} (interpreter): observations: {observations:?}"
            );
            assert_eq!(
                run_to_completion.as_ref().ok(),
                Some(&expected),
                "{test_name} (RunToCompletion): observations: {observations:?}"
            );
            assert_eq!(
                suspendable.as_ref().ok(),
                Some(&expected),
                "{test_name} (Suspendable): observations: {observations:?}"
            );
        }
        R3DefaultDiagBehavior::Arity => {
            assert!(
                observations.interpreter.is_err(),
                "{test_name} (interpreter): wrong arity must be rejected; observations: {observations:?}"
            );
            assert!(
                matches!(
                    run_to_completion,
                    Err(VmError::FunctionArgumentMismatch {
                        expected: 1,
                        actual: 3,
                        ..
                    })
                ),
                "{test_name} (RunToCompletion): wrong arity must produce a function-argument error; observations: {observations:?}"
            );
            assert!(
                matches!(
                    suspendable,
                    Err(VmError::FunctionArgumentMismatch {
                        expected: 1,
                        actual: 3,
                        ..
                    })
                ),
                "{test_name} (Suspendable): wrong arity must produce a function-argument error; observations: {observations:?}"
            );
        }
    }
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

macro_rules! r3_default_diag_test {
    ($name:ident, $style:ident, $order:ident, $policy:ident, $behavior:ident) => {
        #[test]
        fn $name() {
            let observations = observe_r3_default_diag(
                R3DefaultDiagStyle::$style,
                R3DefaultDiagModuleOrder::$order,
                R3DefaultDiagBuiltinPolicy::$policy,
                R3DefaultDiagBehavior::$behavior,
            );
            assert_r3_default_diag(
                stringify!($name),
                R3DefaultDiagBehavior::$behavior,
                &observations,
            );
        }
    };
}

r3_default_diag_test!(
    r3_default_diag_plain_helper_first_default_value,
    Plain,
    HelperFirst,
    Default,
    Value
);
r3_default_diag_test!(
    r3_default_diag_plain_helper_first_default_undefined,
    Plain,
    HelperFirst,
    Default,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_plain_helper_first_default_output,
    Plain,
    HelperFirst,
    Default,
    Output
);
r3_default_diag_test!(
    r3_default_diag_plain_helper_first_default_arity,
    Plain,
    HelperFirst,
    Default,
    Arity
);
r3_default_diag_test!(
    r3_default_diag_plain_helper_first_disabled_value,
    Plain,
    HelperFirst,
    Disabled,
    Value
);
r3_default_diag_test!(
    r3_default_diag_plain_helper_first_disabled_undefined,
    Plain,
    HelperFirst,
    Disabled,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_plain_helper_first_disabled_output,
    Plain,
    HelperFirst,
    Disabled,
    Output
);
r3_default_diag_test!(
    r3_default_diag_plain_helper_first_disabled_arity,
    Plain,
    HelperFirst,
    Disabled,
    Arity
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_default_value,
    Plain,
    MainFirst,
    Default,
    Value
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_default_undefined,
    Plain,
    MainFirst,
    Default,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_default_output,
    Plain,
    MainFirst,
    Default,
    Output
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_default_arity,
    Plain,
    MainFirst,
    Default,
    Arity
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_disabled_value,
    Plain,
    MainFirst,
    Disabled,
    Value
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_disabled_undefined,
    Plain,
    MainFirst,
    Disabled,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_disabled_output,
    Plain,
    MainFirst,
    Disabled,
    Output
);
r3_default_diag_test!(
    r3_default_diag_plain_main_first_disabled_arity,
    Plain,
    MainFirst,
    Disabled,
    Arity
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_default_value,
    Literal,
    HelperFirst,
    Default,
    Value
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_default_undefined,
    Literal,
    HelperFirst,
    Default,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_default_output,
    Literal,
    HelperFirst,
    Default,
    Output
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_default_arity,
    Literal,
    HelperFirst,
    Default,
    Arity
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_disabled_value,
    Literal,
    HelperFirst,
    Disabled,
    Value
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_disabled_undefined,
    Literal,
    HelperFirst,
    Disabled,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_disabled_output,
    Literal,
    HelperFirst,
    Disabled,
    Output
);
r3_default_diag_test!(
    r3_default_diag_literal_helper_first_disabled_arity,
    Literal,
    HelperFirst,
    Disabled,
    Arity
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_default_value,
    Literal,
    MainFirst,
    Default,
    Value
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_default_undefined,
    Literal,
    MainFirst,
    Default,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_default_output,
    Literal,
    MainFirst,
    Default,
    Output
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_default_arity,
    Literal,
    MainFirst,
    Default,
    Arity
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_disabled_value,
    Literal,
    MainFirst,
    Disabled,
    Value
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_disabled_undefined,
    Literal,
    MainFirst,
    Disabled,
    Undefined
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_disabled_output,
    Literal,
    MainFirst,
    Disabled,
    Output
);
r3_default_diag_test!(
    r3_default_diag_literal_main_first_disabled_arity,
    Literal,
    MainFirst,
    Disabled,
    Arity
);

#[derive(Debug)]
struct RgpInputObservations {
    interpreter: Vec<Result<Value, String>>,
    run_to_completion: Vec<Result<Value, String>>,
    suspendable: Vec<Result<Value, String>>,
}

fn observe_rgp_input_cases(
    modules: &[(&str, &str)],
    entry_point: &str,
    inputs: &[Value],
) -> anyhow::Result<RgpInputObservations> {
    let mut engine = Engine::new();
    for (module_id, content) in modules {
        engine.add_policy((*module_id).to_string(), (*content).to_string())?;
    }

    let mut interpreter = Vec::new();
    for input in inputs {
        engine.set_input(input.clone());
        interpreter.push(
            engine
                .eval_rule(entry_point.to_string())
                .map_err(|error| error.to_string()),
        );
    }

    let program = compile_modules_with_options(modules, entry_point, &CompilerOptions::default())?;
    let mut vm_observations = Vec::new();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_data(Value::new_object())?;

        let mut results = Vec::new();
        for input in inputs {
            vm.set_input(input.clone());
            results.push(
                vm.execute_entry_point_by_name(entry_point)
                    .map_err(|error| error.to_string()),
            );
        }
        vm_observations.push(results);
    }

    let mut vm_observations = vm_observations.into_iter();
    Ok(RgpInputObservations {
        interpreter,
        run_to_completion: vm_observations
            .next()
            .expect("RunToCompletion observations were collected"),
        suspendable: vm_observations
            .next()
            .expect("Suspendable observations were collected"),
    })
}

#[test]
fn rgp_01_callable_default_falls_back_after_ordinary_definition_misses_for_literal_import(
) -> anyhow::Result<()> {
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
    let expected: Vec<Result<Value, String>> = vec![
        Ok(Value::Bool(false)),
        Ok(Value::Bool(true)),
        Ok(Value::Undefined),
    ];

    let observations = observe_rgp_input_cases(&modules, entry_point, &inputs)?;
    assert_eq!(
        observations.interpreter, expected,
        "literal-package interpreter results"
    );
    assert_eq!(
        (observations.run_to_completion, observations.suspendable),
        (expected.clone(), expected),
        "literal-package VM results for both execution modes"
    );
    Ok(())
}

#[test]
fn rgp_01_callable_default_output_does_not_bind_undefined_argument() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := true
f(x) := false if x == 1
p := result if { f(input.x, result) }
"#;
    let modules = [("test.rego", source)];
    let inputs = [Value::new_object()];
    let expected = vec![Ok(Value::Undefined)];

    let observations = observe_rgp_input_cases(&modules, "data.test.p", &inputs)?;
    assert_eq!(
        observations.interpreter, expected,
        "interpreter output binding with a missing argument"
    );
    assert_eq!(
        (observations.run_to_completion, observations.suspendable),
        (expected.clone(), expected),
        "VM output binding with a missing argument in both execution modes"
    );
    Ok(())
}

#[test]
fn rgp_01_callable_default_rejects_wrong_arity_after_ordinary_definition() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := true
f(x) := false if x == 1
p := f(0, 1, 2)
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";
    let program = compile_modules_with_options(&modules, entry_point, &CompilerOptions::default())?;

    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), source.to_string())?;
    engine.set_input(Value::new_object());
    let interpreter = engine
        .eval_rule(entry_point.to_string())
        .map_err(|error| error.to_string());
    assert!(
        interpreter.is_err(),
        "interpreter must report wrong arity instead of using the default: {interpreter:?}"
    );

    let mut vm_results = Vec::new();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_data(Value::new_object())?;
        vm_results.push((mode, vm.execute_entry_point_by_name(entry_point)));
    }

    assert!(
        vm_results.iter().all(|(_, result)| matches!(
            result,
            Err(VmError::FunctionArgumentMismatch {
                expected: 1,
                actual: 3,
                ..
            })
        )),
        "both VM modes must report wrong arity instead of using the default: {vm_results:?}"
    );
    Ok(())
}

#[test]
fn rgp_04_ordinary_wrong_arity_precedes_undefined_argument() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := true
f(x) := false if x == 1
p := f(input.missing, 0, 0)
"#;
    let entry_point = "data.test.p";

    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), source.to_string())?;
    engine.set_input(Value::new_object());
    let interpreter = engine
        .eval_rule(entry_point.to_string())
        .map_err(|error| error.to_string());
    assert!(
        interpreter.is_err(),
        "ordinary function arity must be checked before Undefined propagation; got {interpreter:?}"
    );
    assert!(
        interpreter
            .as_ref()
            .expect_err("wrong arity must be an interpreter error")
            .contains("mismatch in number of arguments"),
        "unexpected interpreter error: {interpreter:?}"
    );

    let modules = [("test.rego", source)];
    let program = compile_modules_with_options(&modules, entry_point, &CompilerOptions::default())?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(mode);
        vm.load_program(program.clone());
        vm.set_input(Value::new_object());
        assert!(
            matches!(
                vm.execute_entry_point_by_name(entry_point),
                Err(VmError::FunctionArgumentMismatch {
                    expected: 1,
                    actual: 3,
                    ..
                })
            ),
            "{mode:?} must reject wrong arity before Undefined propagation"
        );
    }

    Ok(())
}

#[test]
fn rgp_04_ordinary_function_without_default_checks_arity_before_undefined() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
f(x) := false if x == 1
p := f(input.missing, 0, 0)
"#;
    let entry_point = "data.test.p";

    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), source.to_string())?;
    engine.set_input(Value::new_object());
    let interpreter = engine
        .eval_rule(entry_point.to_string())
        .map_err(|error| error.to_string());
    assert!(
        interpreter.is_err(),
        "ordinary function arity must be checked before Undefined propagation; got {interpreter:?}"
    );

    let modules = [("test.rego", source)];
    let program = compile_modules_with_options(&modules, entry_point, &CompilerOptions::default())?;
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(mode);
        vm.load_program(program.clone());
        vm.set_input(Value::new_object());
        assert!(
            matches!(
                vm.execute_entry_point_by_name(entry_point),
                Err(VmError::FunctionArgumentMismatch {
                    expected: 1,
                    actual: 3,
                    ..
                })
            ),
            "{mode:?} must reject wrong arity before Undefined propagation"
        );
    }

    Ok(())
}

#[test]
fn rgp_02_default_only_comprehension_reads_runtime_input_on_reused_vm() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [input.x | true]
p := f(0)
"#;
    let modules = [("test.rego", source)];
    let inputs = [
        Value::from_json_str(r#"{"x":7}"#)?,
        Value::from_json_str(r#"{"x":9}"#)?,
    ];
    let expected: Vec<Result<Value, String>> = vec![
        Ok(Value::from_json_str("[7]")?),
        Ok(Value::from_json_str("[9]")?),
    ];

    let observations = observe_rgp_input_cases(&modules, "data.test.p", &inputs)?;
    assert_eq!(
        observations.interpreter, expected,
        "interpreter input values"
    );
    assert_eq!(
        (observations.run_to_completion, observations.suspendable),
        (expected.clone(), expected),
        "results in both VM modes while reusing the program and VM"
    );
    Ok(())
}

#[test]
fn rgp_02_default_comprehension_after_ordinary_miss_reads_runtime_input() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [input.x | true]
f(x) := ["ordinary"] if x == 1
p := f(0)
"#;
    let modules = [("test.rego", source)];
    let inputs = [
        Value::from_json_str(r#"{"x":7}"#)?,
        Value::from_json_str(r#"{"x":9}"#)?,
    ];
    let expected: Vec<Result<Value, String>> = vec![
        Ok(Value::from_json_str("[7]")?),
        Ok(Value::from_json_str("[9]")?),
    ];

    let observations = observe_rgp_input_cases(&modules, "data.test.p", &inputs)?;
    assert_eq!(
        observations.interpreter, expected,
        "interpreter input values"
    );
    assert_eq!(
        (observations.run_to_completion, observations.suspendable),
        (expected.clone(), expected),
        "results in both VM modes after an ordinary definition misses"
    );
    Ok(())
}

#[test]
fn rgp_02_default_comprehension_reads_runtime_data_on_reused_vm() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [value | some value in data.values]
p := f(0)
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";
    let data_cases = [
        (
            Value::from_json_str(r#"{"values":[7]}"#)?,
            Value::from_json_str("[7]")?,
        ),
        (
            Value::from_json_str(r#"{"values":[9]}"#)?,
            Value::from_json_str("[9]")?,
        ),
    ];
    let expected: Vec<Result<Value, String>> = data_cases
        .iter()
        .map(|(_, value)| Ok(value.clone()))
        .collect();
    let program = compile_modules_with_options(&modules, entry_point, &CompilerOptions::default())?;

    let mut interpreter_observations = Vec::new();
    for (data, _) in &data_cases {
        let mut engine = Engine::new();
        engine.add_policy("test.rego".to_string(), source.to_string())?;
        engine.add_data(data.clone())?;
        engine.set_input(Value::new_object());
        interpreter_observations.push(
            engine
                .eval_rule(entry_point.to_string())
                .map_err(|error| error.to_string()),
        );
    }
    assert_eq!(
        interpreter_observations, expected,
        "interpreter results for runtime data"
    );

    let mut vm_observations = Vec::new();
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(Value::new_object());

        let mut results = Vec::new();
        for (data, _) in &data_cases {
            vm.set_data(data.clone())?;
            results.push(
                vm.execute_entry_point_by_name(entry_point)
                    .map_err(|error| error.to_string()),
            );
        }
        vm_observations.push((mode, results));
    }

    assert!(
        vm_observations
            .iter()
            .all(|(_, results)| results == &expected),
        "both VM modes must read current data while reusing the program and VM: {vm_observations:?}"
    );
    Ok(())
}

#[test]
fn rgp_02_nested_input_and_data_defaults_survive_v6_round_trips() -> anyhow::Result<()> {
    use regorus::rvm::program::{DeserializationResult, Program};

    let source = r#"package test
import rego.v1
default nested(_) := [[input.x | true] | true]
default values(_) := [value | some value in data.values]
p := {"nested": nested(0), "values": values(0)}
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";
    let program = compile_modules_with_options(&modules, entry_point, &CompilerOptions::default())?;
    let json = program.serialize_json().map_err(anyhow::Error::msg)?;
    let json_program =
        std::sync::Arc::new(Program::deserialize_json(&json).map_err(anyhow::Error::msg)?);
    let binary = program.serialize_binary().map_err(anyhow::Error::msg)?;
    assert_eq!(
        u16::from_le_bytes([binary[4], binary[5]]),
        6,
        "dynamic defaults must remain in the existing Program v6 format"
    );
    let binary_program = match Program::deserialize_binary(&binary).map_err(anyhow::Error::msg)? {
        DeserializationResult::Complete(program) => std::sync::Arc::new(program),
        DeserializationResult::Partial(_) => {
            anyhow::bail!("dynamic-default v6 program unexpectedly needs recompilation")
        }
    };

    let inputs = [
        Value::from_json_str(r#"{"x":7}"#)?,
        Value::from_json_str(r#"{"x":9}"#)?,
        Value::new_object(),
    ];
    let expected_results = [
        Value::from_json_str(r#"{"nested":[[7]],"values":[3]}"#)?,
        Value::from_json_str(r#"{"nested":[[9]],"values":[5]}"#)?,
        Value::from_json_str(r#"{"nested":[[]],"values":[]}"#)?,
    ];
    let data_cases = [
        Value::from_json_str(r#"{"values":[3]}"#)?,
        Value::from_json_str(r#"{"values":[5]}"#)?,
        Value::new_object(),
    ];

    for ((input, data), expected) in inputs
        .iter()
        .zip(data_cases.iter())
        .zip(expected_results.iter())
    {
        let mut engine = Engine::new();
        engine.add_policy("test.rego".to_string(), source.to_string())?;
        engine.add_data(data.clone())?;
        engine.set_input(input.clone());
        assert_eq!(
            engine.eval_rule(entry_point.to_string())?,
            *expected,
            "interpreter result for input {input:?} and data {data:?}"
        );
    }

    for round_tripped_program in [json_program, binary_program] {
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(round_tripped_program.clone());
            vm.set_execution_mode(mode);

            for ((input, data), expected) in inputs
                .iter()
                .zip(data_cases.iter())
                .zip(expected_results.iter())
            {
                vm.set_input(input.clone());
                vm.set_data(data.clone())?;
                let result = vm.execute_entry_point_by_name(entry_point)?;
                assert_eq!(result, *expected, "{mode:?} result after v6 round trip");
            }
        }
    }
    Ok(())
}

#[test]
fn rgp_02_dynamic_default_preserves_multiple_definition_results_and_else() -> anyhow::Result<()> {
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
default patterned(_) := [value | some value in input.fallback]
patterned({"kind": "match"}) := "matched"
p := {
    "false": choose("false"),
    "null": choose("null"),
    "empty": choose("empty"),
    "equal": choose("same"),
    "one": branch(1),
    "two": branch(2),
    "branch_fallback": branch(3),
    "pattern_match": patterned({"kind": "match"}),
    "pattern_fallback": patterned({"kind": "miss"})
}
"#;
    let modules = [("test.rego", source)];
    let entry_point = "data.test.p";
    let inputs = [Value::from_json_str(r#"{"fallback":["fallback"]}"#)?];
    let expected = Value::from_json_str(
        r#"{"false":false,"null":null,"empty":[],"equal":"same","one":"one","two":"two","branch_fallback":["fallback"],"pattern_match":"matched","pattern_fallback":["fallback"]}"#,
    )?;
    let observations = observe_rgp_input_cases(&modules, entry_point, &inputs)?;

    assert_eq!(observations.interpreter, vec![Ok(expected.clone())]);
    assert_eq!(
        observations.run_to_completion,
        vec![Ok(expected.clone())],
        "RunToCompletion must preserve distinct and equal ordinary results"
    );
    assert_eq!(
        observations.suspendable,
        vec![Ok(expected)],
        "Suspendable must preserve distinct and equal ordinary results"
    );
    Ok(())
}

#[test]
fn rgp_02_conflicting_ordinary_results_do_not_select_dynamic_default() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [input.fallback | true]
f(x) := "first" if x == 1
f(x) := "second" if x == 1
p := f(1)
"#;
    let modules = [("test.rego", source)];
    let inputs = [Value::from_json_str(r#"{"fallback":"default"}"#)?];
    let observations = observe_rgp_input_cases(&modules, "data.test.p", &inputs)?;

    assert!(
        observations.interpreter[0].is_err(),
        "the interpreter must preserve its existing conflict error: {:?}",
        observations.interpreter
    );
    let expected_vm = vec![Ok(Value::Undefined)];
    assert_eq!(
        observations.run_to_completion, expected_vm,
        "a VM conflict must remain Undefined rather than selecting the default"
    );
    assert_eq!(
        observations.suspendable, expected_vm,
        "a suspendable VM conflict must remain Undefined rather than selecting the default"
    );
    Ok(())
}

#[test]
fn rgp_02_default_expression_uses_its_owning_module_imports_in_either_order() -> anyhow::Result<()>
{
    let helper = r#"package helpers
import rego.v1
import data.owner as source
default f(_) := source.value
"#;
    let main = r#"package main
import rego.v1
import data.caller as source
import data.helpers.f as f
p := f(0)
"#;
    let module_orders = [
        [("helper.rego", helper), ("main.rego", main)],
        [("main.rego", main), ("helper.rego", helper)],
    ];
    let expected = Value::from("owner");

    for modules in module_orders {
        let mut engine = Engine::new();
        for (module_id, content) in &modules {
            engine.add_policy((*module_id).to_string(), (*content).to_string())?;
        }
        engine.add_data(Value::from_json_str(
            r#"{"owner":{"value":"owner"},"caller":{"value":"caller"}}"#,
        )?)?;
        assert_eq!(
            engine.eval_rule("data.main.p".to_string())?,
            expected,
            "interpreter default must resolve imports in its defining module"
        );

        let entry_point = "data.main.p";
        let compiled = engine.compile_with_entrypoint(&Rc::from(entry_point))?;
        let program = Compiler::compile_from_policy(&compiled, &[entry_point])?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_data(Value::from_json_str(
                r#"{"owner":{"value":"owner"},"caller":{"value":"caller"}}"#,
            )?)?;
            assert_eq!(
                vm.execute_entry_point_by_name(entry_point)?,
                expected,
                "{mode:?} default must resolve imports in its defining module"
            );
        }
    }
    Ok(())
}

#[test]
fn rgp_e1_dynamic_default_comprehension_undefined_yields_survive_v6_round_trips(
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
            r#"{"set_count":4,"set_drop_key":true,"set_false":true,"set_null":true,"set_kept":true,"object":{"false":false,"null":null,"valid":"kept"}}"#,
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
fn rgp_02_host_await_runs_only_for_default_fallback_and_resumes_once() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [count(input.value) | true]
f(x) := "ordinary" if x == 1
p := f(input.value)
"#;
    let options = CompilerOptions {
        host_await_builtins: vec![("count".to_string(), 1)],
        ..CompilerOptions::default()
    };
    let modules = [("test.rego", source)];
    let program = compile_modules_with_options(&modules, "data.test.p", &options)?;

    let mut run_to_completion = RegoVM::new();
    run_to_completion.load_program(program.clone());
    run_to_completion
        .set_host_await_responses([(Value::from("count"), [Value::from("host-result")])]);
    run_to_completion.set_input(Value::from_json_str(r#"{"value":1}"#)?);
    assert_eq!(
        run_to_completion.execute_entry_point_by_name("data.test.p")?,
        Value::from("ordinary"),
        "an ordinary success must not execute the default host call"
    );
    run_to_completion.set_input(Value::from_json_str(r#"{"value":2}"#)?);
    assert_eq!(
        run_to_completion.execute_entry_point_by_name("data.test.p")?,
        Value::from_json_str(r#"["host-result"]"#)?,
        "the fallback host call must consume exactly one response"
    );
    run_to_completion.set_input(Value::from_json_str(r#"{"value":3}"#)?);
    assert_eq!(
        run_to_completion.execute_entry_point_by_name("data.test.p")?,
        Value::Undefined,
        "a missing default host response remains a failed rule result"
    );

    let mut suspendable = RegoVM::new();
    suspendable.load_program(program);
    suspendable.set_execution_mode(ExecutionMode::Suspendable);
    suspendable.set_input(Value::from_json_str(r#"{"value":1}"#)?);
    assert_eq!(
        suspendable.execute_entry_point_by_name("data.test.p")?,
        Value::from("ordinary")
    );
    suspendable.set_input(Value::from_json_str(r#"{"value":2}"#)?);
    let _suspended_result = suspendable.execute_entry_point_by_name("data.test.p")?;
    assert!(matches!(
        suspendable.execution_state(),
        ExecutionState::Suspended { .. }
    ));
    assert_eq!(
        suspendable.resume(Some(Value::from("resumed")))?,
        Value::from_json_str(r#"["resumed"]"#)?
    );
    suspendable.set_input(Value::from_json_str(r#"{"value":1}"#)?);
    assert_eq!(
        suspendable.execute_entry_point_by_name("data.test.p")?,
        Value::from("ordinary"),
        "the VM must remain reusable after resume"
    );
    Ok(())
}

#[test]
fn rgp_02_dynamic_default_does_not_absorb_policy_or_resource_errors() -> anyhow::Result<()> {
    let source = r#"package test
import rego.v1
default f(_) := [count(input.values) | true]
f(x) := "ordinary" if x == 1
p := f(input.value)
"#;
    let modules = [("test.rego", source)];
    let program =
        compile_modules_with_options(&modules, "data.test.p", &CompilerOptions::default())?;
    let disabled_count =
        BuiltinPolicy::from_disabled_names(&["count"]).expect("count is a registered builtin");

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(r#"{"value":2,"values":[]}"#)?);
        vm.set_builtin_policy(disabled_count.clone())?;
        assert!(matches!(
            vm.execute_entry_point_by_name("data.test.p"),
            Err(VmError::BuiltinDisabled { name, .. }) if name == "count"
        ));
    }

    let mut limited = RegoVM::new();
    limited.load_program(program);
    limited.set_input(Value::from_json_str(r#"{"value":2,"values":[]}"#)?);
    limited.set_max_instructions(0);
    assert!(matches!(
        limited.execute_entry_point_by_name("data.test.p"),
        Err(VmError::InstructionLimitExceeded { .. })
    ));
    Ok(())
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
