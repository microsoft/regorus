// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::{Compiler, CompilerError, SpannedCompilerError};
use regorus::rvm::instructions::GuardMode;
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
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

fn compile_rule_with_host_await(
    module: &str,
    host_await_builtins: &[(&str, usize)],
) -> anyhow::Result<std::sync::Arc<Program>> {
    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), module.to_string())?;
    let compiled = engine.compile_with_entrypoint(&Rc::from("data.test.p"))?;
    Ok(Compiler::compile_from_policy_with_host_await(
        &compiled,
        &["data.test.p"],
        host_await_builtins,
    )?)
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
fn registered_host_await_compiles_zero_two_and_nine_inputs() {
    for (arg_count, call) in [
        (0, "lookup()"),
        (1, "lookup(\"ping\")"),
        (2, "lookup(1, 2)"),
        (9, "lookup(1, 2, 3, 4, 5, 6, 7, 8, 9)"),
    ] {
        let module = format!("package test\np := {call}");
        compile_rule_with_host_await(&module, &[("lookup", arg_count)])
            .unwrap_or_else(|error| panic!("failed to compile arity {arg_count}: {error}"));
    }
}

#[test]
fn registered_host_await_accepts_many_reused_input_registers() -> anyhow::Result<()> {
    const ARG_COUNT: usize = 253;
    let args = std::iter::repeat_n("input", ARG_COUNT)
        .collect::<Vec<_>>()
        .chunks(12)
        .map(|line| format!("  {}", line.join(", ")))
        .collect::<Vec<_>>()
        .join(",\n");
    let module = format!("package test\np := lookup(\n{args}\n)");
    let program = compile_rule_with_host_await(&module, &[("lookup", ARG_COUNT)])?;
    let input_json = r#"{"nested":[1,{"key":"value"}]}"#;
    let input = Value::from_json_str(input_json)?;
    let expected_payload = Value::from_json_str(&format!(
        "[{}]",
        std::iter::repeat_n(input_json, ARG_COUNT)
            .collect::<Vec<_>>()
            .join(",")
    ))?;

    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    vm.set_input(input);
    vm.execute()?;

    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended {
            reason: SuspendReason::HostAwait { argument, .. },
            ..
        } if argument == &expected_payload
    ));
    vm.resume(Some(Value::from("host-response")))?;
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Completed { result } if result == &Value::from("host-response")
    ));
    Ok(())
}

#[test]
fn registered_host_await_round_trip_preserves_array_payload() {
    let cases = [
        (0, "", "[]"),
        (1, r#""ping""#, r#"["ping"]"#),
        (2, r#"5, {"nested": [1, 2]}"#, r#"[5, {"nested": [1, 2]}]"#),
    ];

    for (arg_count, args, expected_payload) in cases {
        let module = format!("package test\np := lookup({args})");
        let program = compile_rule_with_host_await(&module, &[("lookup", arg_count)])
            .unwrap_or_else(|error| panic!("failed to compile arity {arg_count}: {error}"));
        let serialized = program
            .serialize_binary()
            .expect("failed to serialize program");
        let deserialized = match Program::deserialize_binary(&serialized)
            .expect("failed to deserialize program")
        {
            DeserializationResult::Complete(program) => std::sync::Arc::new(program),
            DeserializationResult::Partial(_) => panic!("expected a complete program"),
        };
        let expected_payload =
            Value::from_json_str(expected_payload).expect("invalid expected payload");

        for program in [program, deserialized] {
            let mut vm = RegoVM::new();
            vm.set_execution_mode(ExecutionMode::Suspendable);
            vm.load_program(program);
            let _ = vm.execute().expect("failed to execute program");
            match vm.execution_state() {
                ExecutionState::Suspended {
                    reason:
                        SuspendReason::HostAwait {
                            identifier,
                            argument,
                            ..
                        },
                    ..
                } => {
                    assert_eq!(identifier, &Value::from("lookup"));
                    assert_eq!(argument, &expected_payload);
                }
                state => panic!("expected HostAwait suspension, got {state:?}"),
            }

            vm.resume(Some(Value::from("pong")))
                .expect("failed to resume HostAwait");
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Completed { result } if result == &Value::from("pong")
            ));
        }
    }
}

#[test]
fn registered_host_await_legacy_program_keeps_raw_payload() {
    // Captured before array packing at e39a1d16; SHA-256:
    // 43DFCEED1CFD2761D385F9CAE518CDCBB385F04FB3AA1ADC7DF312E7884DD547.
    let program = match Program::deserialize_binary(include_bytes!(
        "fixtures/host_await_registered_raw_e39a1d16.rvm"
    ))
    .expect("failed to deserialize baseline program")
    {
        DeserializationResult::Complete(program) => std::sync::Arc::new(program),
        DeserializationResult::Partial(_) => panic!("expected a complete baseline program"),
    };
    let mut vm = RegoVM::new();
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.load_program(program);
    let _ = vm.execute().expect("failed to execute baseline program");

    match vm.execution_state() {
        ExecutionState::Suspended {
            reason:
                SuspendReason::HostAwait {
                    identifier,
                    argument,
                    ..
                },
            ..
        } => {
            assert_eq!(identifier, &Value::from("lookup"));
            assert_eq!(argument, &Value::from("legacy"));
        }
        state => panic!("expected raw-payload HostAwait suspension, got {state:?}"),
    }
}

#[test]
fn programs_without_runtime_defaults_keep_v6_and_flat_json_compatibility() {
    let program = compile_rule("package test\ndefault p := true");
    assert!(program
        .rule_infos
        .iter()
        .any(|rule_info| rule_info.default_literal_index.is_some()));
    let binary = program
        .serialize_binary()
        .expect("failed to serialize legacy-compatible program");
    assert_eq!(u32::from_le_bytes(binary[4..8].try_into().unwrap()), 6);
    assert!(Program::can_deserialize(&binary).unwrap());
    let binary_program = match Program::deserialize_binary(&binary).unwrap() {
        DeserializationResult::Complete(program) => std::sync::Arc::new(program),
        DeserializationResult::Partial(_) => panic!("expected a complete v6 program"),
    };

    let json = program
        .serialize_json()
        .expect("failed to serialize legacy-compatible JSON");
    let json_value: serde_json::Value = serde_json::from_str(&json).unwrap();
    assert!(json_value.get("version").is_none());
    assert!(json_value.get("program").is_none());
    assert!(json_value["rule_infos"]
        .as_array()
        .unwrap()
        .iter()
        .all(|rule_info| rule_info.get("default_entry_point").is_none()));
    let json_program = std::sync::Arc::new(
        Program::deserialize_json(&json).expect("failed to deserialize flat legacy JSON"),
    );
    for program in [binary_program, json_program] {
        let mut vm = RegoVM::new();
        vm.set_execution_mode(ExecutionMode::Suspendable);
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.test.p")
                .expect("failed to execute serialized literal default"),
            Value::Bool(true)
        );
    }
}

#[test]
fn e39_v6_frozen_dynamic_default_keeps_historical_value_after_reload() {
    // Frozen by the actual e39 compiler from the Mark policy with compile data
    // {"probe":{"other":false}}; e39 stored [] as a v6 literal instead of
    // evaluating the default from runtime data.
    let binary = include_bytes!("fixtures/e39-mark-frozen-dynamic-default-v6.bin");
    assert_eq!(u32::from_le_bytes(binary[4..8].try_into().unwrap()), 6);
    assert!(Program::can_deserialize(binary).unwrap());
    let binary_program = match Program::deserialize_binary(binary).unwrap() {
        DeserializationResult::Complete(program) => std::sync::Arc::new(program),
        DeserializationResult::Partial(_) => panic!("expected a complete e39 v6 program"),
    };

    let json = include_str!("fixtures/e39-mark-frozen-dynamic-default-v6.json");
    let json_value: serde_json::Value = serde_json::from_str(json).unwrap();
    assert!(
        json_value.get("version").is_none(),
        "e39 JSON must remain flat"
    );
    let json_program = std::sync::Arc::new(
        Program::deserialize_json(json).expect("failed to deserialize e39 flat JSON"),
    );

    for (format, program) in [("binary", binary_program), ("JSON", json_program)] {
        let rule = program
            .rule_infos
            .iter()
            .find(|rule| rule.name == "data.probe.value")
            .expect("e39 artifact omitted the default rule");
        assert!(
            rule.default_literal_index.is_some(),
            "e39 dynamic default must be frozen as a v6 literal"
        );
        assert_eq!(
            program.literals[usize::from(rule.default_literal_index.unwrap())],
            Value::from_json_str("[]").unwrap()
        );
        assert!(
            rule.default_entry_point.is_none(),
            "legacy v6 artifacts must not gain runtime-default metadata"
        );

        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.set_execution_mode(mode);
            vm.load_program(program.clone());
            vm.set_data(Value::from_json_str("{}").unwrap()).unwrap();
            vm.set_input(Value::from_json_str("{}").unwrap());
            assert_eq!(
                vm.execute_entry_point_by_name("data.probe.value").unwrap(),
                Value::from_json_str("[]").unwrap(),
                "reloaded e39 {format} artifact must retain its compile-time-frozen empty default"
            );
        }
    }
}

#[test]
fn runtime_default_artifacts_advertise_v7_and_reject_invalid_metadata() -> anyhow::Result<()> {
    let program = compile_rule("package test\ndefault p := [x | x := input.values[_]]");
    let binary = program
        .serialize_binary()
        .expect("failed to serialize runtime-default program");
    assert_eq!(u32::from_le_bytes(binary[4..8].try_into().unwrap()), 7);
    assert!(Program::can_deserialize(&binary).map_err(anyhow::Error::msg)?);

    let json = program
        .serialize_json()
        .expect("failed to serialize runtime-default JSON");
    let mut json_value: serde_json::Value = serde_json::from_str(&json)?;
    assert_eq!(json_value["version"].as_u64(), Some(7));
    assert!(json_value["program"].is_object());
    Program::deserialize_json(&json).map_err(anyhow::Error::msg)?;

    let default_entry_point = json_value["program"]["rule_infos"][0]["default_entry_point"]
        .as_u64()
        .expect("compiled rule should have runtime default metadata");
    json_value["program"]["rule_infos"][0]["default_entry_point"] =
        serde_json::json!(default_entry_point + 100_000);
    let malformed_json = serde_json::to_string(&json_value)?;
    assert!(
        Program::deserialize_json(&malformed_json)
            .unwrap_err()
            .contains("default entry point"),
        "malformed runtime default entry point should be rejected"
    );

    let mut malformed_rule_infos = json_value.clone();
    malformed_rule_infos["program"]["rule_infos"] = serde_json::json!("not a rule table");
    assert!(
        Program::deserialize_json(&serde_json::to_string(&malformed_rule_infos)?)
            .unwrap_err()
            .contains("Failed to deserialize rule_infos"),
        "invalid executable rule metadata must not be silently replaced"
    );

    let mut future_version = binary.clone();
    future_version[4..8].copy_from_slice(&8_u32.to_le_bytes());
    assert!(!Program::can_deserialize(&future_version).map_err(anyhow::Error::msg)?);
    assert!(Program::deserialize_binary(&future_version)
        .unwrap_err()
        .contains("Unsupported version 8"));
    let mut truncated_binary = binary.clone();
    truncated_binary.pop();
    assert!(
        Program::deserialize_binary(&truncated_binary).is_err(),
        "truncated runtime-default artifact should be rejected"
    );

    let mut malformed_program = (*program).clone();
    let runtime_rule = malformed_program
        .rule_infos
        .iter()
        .position(|rule_info| rule_info.default_entry_point.is_some())
        .expect("compiled rule should have runtime default metadata");
    malformed_program.rule_infos[runtime_rule].default_entry_point =
        Some(u32::try_from(malformed_program.instructions.len()).unwrap());
    assert!(
        malformed_program
            .serialize_binary()
            .unwrap_err()
            .contains("default entry point"),
        "serialization should reject an out-of-range runtime default entry point"
    );

    let mut bad_result_register = (*program).clone();
    let rule_info = &mut bad_result_register.rule_infos[runtime_rule];
    rule_info.result_reg = rule_info.num_registers;
    assert!(
        bad_result_register
            .serialize_binary()
            .unwrap_err()
            .contains("result register"),
        "serialization should reject a runtime default result outside its register window"
    );

    let mut conflicting_default_forms = (*program).clone();
    conflicting_default_forms.rule_infos[runtime_rule].default_literal_index = Some(0);
    assert!(
        conflicting_default_forms
            .serialize_json()
            .unwrap_err()
            .contains("both literal and runtime"),
        "serialization should reject simultaneous literal and runtime defaults"
    );

    let mut entry_at_return = (*program).clone();
    let return_pc = entry_at_return
        .instructions
        .iter()
        .enumerate()
        .find(|(_, instruction)| matches!(instruction, Instruction::RuleReturn {}))
        .map(|(pc, _)| pc)
        .expect("compiled program should contain RuleReturn");
    entry_at_return.rule_infos[runtime_rule].default_entry_point =
        Some(u32::try_from(return_pc).unwrap());
    assert!(
        entry_at_return
            .serialize_binary()
            .unwrap_err()
            .contains("RuleReturn"),
        "serialization should reject a runtime default entry at its terminator"
    );
    Ok(())
}

#[test]
fn dynamic_defaults_reject_direct_references_and_calls_with_source_diagnostics(
) -> anyhow::Result<()> {
    for (module, expected_error) in [
        ("package test\ndefault p := input.value", "invalid `ref`"),
        ("package test\ndefault p := count([1])", "invalid `call`"),
    ] {
        let mut engine = Engine::new();
        engine.add_policy("test.rego".to_string(), module.to_string())?;
        let compiled = engine.compile_with_entrypoint(&Rc::from("data.test.p"))?;
        let error = Compiler::compile_from_policy(&compiled, &["data.test.p"])
            .expect_err("an invalid direct default expression should be rejected");
        let message = error.to_string();
        assert!(
            message.contains(expected_error),
            "unexpected default validation error: {message}"
        );
        assert!(
            message.contains("test.rego"),
            "default validation should preserve source diagnostics: {message}"
        );
    }
    Ok(())
}

#[test]
fn dynamic_default_dependency_cycles_use_the_existing_recursion_check() -> anyhow::Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "test.rego".to_string(),
        r#"
        package test
        default a := [x | x := data.test.b]
        default b := [x | x := data.test.a]
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&Rc::from("data.test.a"))?;
    let error = Compiler::compile_from_policy(&compiled, &["data.test.a"])
        .expect_err("cyclic default dependencies should be rejected");
    assert!(
        error.to_string().contains("recursion"),
        "unexpected cycle diagnostic: {error}"
    );
    Ok(())
}

#[test]
fn emitted_default_builtins_are_registered_before_fallback_execution() -> anyhow::Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "test.rego".to_string(),
        r#"
        package test
        default p := [count(input.values) | input.use_default]
        p := false if input.use_definition
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&Rc::from("data.test.p"))?;
    let program = Compiler::compile_from_policy(&compiled, &["data.test.p"])?;
    assert!(
        program
            .builtin_info_table
            .iter()
            .any(|builtin| builtin.name == "count"),
        "builtin in emitted fallback code must be present before execution"
    );

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(Value::from_json_str(
            r#"{"use_default":true,"use_definition":true}"#,
        )?);
        assert_eq!(
            vm.execute_entry_point_by_name("data.test.p")?,
            Value::Bool(false),
            "{mode:?} ordinary result should suppress the emitted default"
        );
    }

    Ok(())
}

#[test]
fn registered_host_await_rejects_wrong_arity_before_compiling_inputs() {
    for (arg_count, call, actual_count) in [
        (2, "lookup(undefined_variable)", 1),
        (
            2,
            "lookup(undefined_0, undefined_1, undefined_2, undefined_3)",
            4,
        ),
        (usize::MAX, "lookup(undefined_variable)", 1),
    ] {
        let error = compile_rule_with_host_await(
            &format!("package test\np := {call}"),
            &[("lookup", arg_count)],
        )
        .expect_err("mismatched registered arity should fail");
        assert!(
            error.to_string().contains(&format!(
                "expects {arg_count} input arguments, got {actual_count}"
            )),
            "expected arity error, got {error}"
        );
    }
}

#[test]
fn registered_host_await_rejects_duplicate_name_with_different_arities() {
    let error = compile_rule_with_host_await(
        "package test\np := lookup(input.value)",
        &[("lookup", 1), ("lookup", 2)],
    )
    .expect_err("duplicate registration with different arities should fail");

    assert!(
        error.to_string().contains("already registered"),
        "expected duplicate-registration error, got {error}"
    );
}

#[derive(Debug, PartialEq)]
enum StrictProbeOutcome {
    Value(Value),
    DivisionError,
}

fn observe_strict_probe(result: Result<Value, VmError>) -> StrictProbeOutcome {
    match result {
        Ok(value) => StrictProbeOutcome::Value(value),
        Err(VmError::InvalidDivision { .. }) => StrictProbeOutcome::DivisionError,
        Err(VmError::ArithmeticError { message, .. }) if message.contains("Cannot divide") => {
            StrictProbeOutcome::DivisionError
        }
        Err(error) => panic!("expected strict divide-by-zero outcome, got {error:?}"),
    }
}

#[test]
fn registered_host_await_output_guard_restores_input_cache_run_to_completion() -> anyhow::Result<()>
{
    check_registered_host_await_output_guard_cache("input", "data", ExecutionMode::RunToCompletion)
}

#[test]
fn registered_host_await_output_guard_restores_input_cache_suspendable() -> anyhow::Result<()> {
    check_registered_host_await_output_guard_cache("input", "data", ExecutionMode::Suspendable)
}

#[test]
fn registered_host_await_output_guard_restores_data_cache_run_to_completion() -> anyhow::Result<()>
{
    check_registered_host_await_output_guard_cache("data", "input", ExecutionMode::RunToCompletion)
}

#[test]
fn registered_host_await_output_guard_restores_data_cache_suspendable() -> anyhow::Result<()> {
    check_registered_host_await_output_guard_cache("data", "input", ExecutionMode::Suspendable)
}

fn check_registered_host_await_output_guard_cache(
    output_root: &str,
    argument_root: &str,
    mode: ExecutionMode,
) -> anyhow::Result<()> {
    let program = compile_rule_with_host_await(
        &format!(
            r#"
            package test
            import rego.v1
            default p := false
            p if {{
                not echo({argument_root}.missing, {output_root}.expected)
                not {output_root}.blocked
            }}
            "#
        ),
        &[("echo", 1)],
    )?;
    let mut vm = RegoVM::new();
    vm.set_execution_mode(mode);
    vm.load_program(program);

    for (arguments, blocked, response, expected) in [
        ("{}", true, None, false),
        ("{}", false, None, true),
        (r#"{"missing":"request"}"#, true, Some("ok"), false),
        (r#"{"missing":"request"}"#, true, Some("mismatch"), false),
        (r#"{"missing":"request"}"#, false, Some("ok"), false),
        (r#"{"missing":"request"}"#, false, Some("mismatch"), true),
        ("{}", true, None, false),
    ] {
        let output = Value::from_json_str(&format!(r#"{{"expected":"ok","blocked":{blocked}}}"#))?;
        let arguments = Value::from_json_str(arguments)?;
        let (input, data) = if output_root == "input" {
            (output, arguments)
        } else {
            (arguments, output)
        };
        vm.set_input(input);
        vm.set_data(data)?;
        vm.set_host_await_responses([(
            Value::from("echo"),
            response.map(Value::from).into_iter().collect::<Vec<_>>(),
        )]);

        let mut result = vm.execute_entry_point_by_index(0)?;
        if let (ExecutionMode::Suspendable, Some(response)) = (mode, response) {
            let payload = Value::from_json_str(r#"["request"]"#)?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason: SuspendReason::HostAwait { argument, .. },
                    ..
                } if argument == &payload
            ));
            result = vm.resume(Some(Value::from(response)))?;
        }
        assert_eq!(
            result,
            Value::Bool(expected),
            "{output_root} cache in {mode:?}: blocked={blocked}, response={response:?}"
        );
        if matches!(mode, ExecutionMode::Suspendable) {
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Completed { result } if result == &Value::Bool(expected)
            ));
        }
    }

    Ok(())
}

#[test]
fn registered_host_await_strict_output_division_matches_explicit_control_in_both_modes(
) -> anyhow::Result<()> {
    let entry_points = ["data.demo.allow", "data.demo.next"];
    let mut engine = Engine::new();
    engine.add_policy(
        "test.rego".to_string(),
        r#"
        package demo
        import rego.v1
        default allow := false
        allow if { echo(1, 1 / input.zero) }
        next := echo("next")
        "#
        .to_string(),
    )?;
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry_points[0]))?;
    let registered_program =
        Compiler::compile_from_policy_with_host_await(&compiled, &entry_points, &[("echo", 1)])?;

    let mut explicit_engine = Engine::new();
    explicit_engine.add_policy(
        "test.rego".to_string(),
        r#"
        package demo
        import rego.v1
        default allow := false
        allow if { __builtin_host_await([1], "echo", 1 / input.zero) }
        next := __builtin_host_await("next", "echo")
        "#
        .to_string(),
    )?;
    let explicit_compiled = explicit_engine.compile_with_entrypoint(&Rc::from(entry_points[0]))?;
    let explicit_program = Compiler::compile_from_policy(&explicit_compiled, &entry_points)?;

    let run = |program: std::sync::Arc<Program>,
               mode: ExecutionMode,
               registered: bool|
     -> anyhow::Result<(StrictProbeOutcome, StrictProbeOutcome)> {
        let is_run_to_completion = matches!(mode, ExecutionMode::RunToCompletion);
        let mut vm = RegoVM::new();
        vm.set_execution_mode(mode);
        vm.set_strict_builtin_errors(true);
        vm.load_program(program);
        vm.set_input(Value::from_json_str(r#"{"zero":0}"#)?);
        if is_run_to_completion {
            vm.set_host_await_responses([(
                Value::from("echo"),
                vec![
                    Value::from("first-response"),
                    Value::from("second-response"),
                ],
            )]);
        }

        let first_result = if is_run_to_completion {
            vm.execute_entry_point_by_index(0)
        } else {
            vm.execute_entry_point_by_index(0)?;
            let first_payload = Value::from_json_str("[1]")?;
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason:
                        SuspendReason::HostAwait {
                            identifier,
                            argument,
                            ..
                        },
                    ..
                } if identifier == &Value::from("echo") && argument == &first_payload
            ));
            vm.resume(Some(Value::from("first-response")))
        };
        let first_outcome = observe_strict_probe(first_result);

        let second_result = if is_run_to_completion {
            vm.execute_entry_point_by_index(1)
        } else {
            vm.execute_entry_point_by_index(1)?;
            let second_payload = if registered {
                Value::from_json_str(r#"["next"]"#)?
            } else {
                Value::from("next")
            };
            assert!(matches!(
                vm.execution_state(),
                ExecutionState::Suspended {
                    reason:
                        SuspendReason::HostAwait {
                            identifier,
                            argument,
                            ..
                        },
                    ..
                } if identifier == &Value::from("echo") && argument == &second_payload
            ));
            vm.resume(Some(Value::from("second-response")))
        };

        Ok((first_outcome, observe_strict_probe(second_result)))
    };

    let mut division_program = Program::new();
    division_program
        .entry_points
        .insert("divide".to_string(), 0);
    division_program.dispatch_window_size = 3;
    division_program.max_rule_window_size = 3;
    division_program.literals = vec![Value::from(1_u64), Value::from(0_u64)];
    division_program.add_instruction(
        Instruction::Load {
            dest: 0,
            literal_idx: 0,
        },
        None,
    );
    division_program.add_instruction(
        Instruction::Load {
            dest: 1,
            literal_idx: 1,
        },
        None,
    );
    division_program.add_instruction(
        Instruction::Div {
            dest: 2,
            left: 0,
            right: 1,
        },
        None,
    );
    division_program.add_instruction(Instruction::Return { value: 2 }, None);
    let division_program = std::sync::Arc::new(division_program);

    let mut non_strict_vm = RegoVM::new();
    non_strict_vm.set_strict_builtin_errors(false);
    non_strict_vm.load_program(division_program.clone());
    assert_eq!(non_strict_vm.execute()?, Value::Undefined);

    let mut strict_vm = RegoVM::new();
    strict_vm.set_strict_builtin_errors(true);
    strict_vm.load_program(division_program);
    assert!(
        matches!(strict_vm.execute(), Err(VmError::InvalidDivision { .. })),
        "strict divide-by-zero control must produce InvalidDivision"
    );

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let registered = run(registered_program.clone(), mode, true)?;
        let explicit = run(explicit_program.clone(), mode, false)?;
        assert_eq!(
            registered, explicit,
            "registered/explicit mismatch in {mode:?}"
        );
        assert_eq!(
            registered.0,
            StrictProbeOutcome::Value(Value::Bool(false)),
            "the default-false rule should absorb the output-expression failure"
        );
        assert_eq!(
            registered.1,
            StrictProbeOutcome::Value(Value::from("second-response")),
            "the following call must receive the next response"
        );
    }

    Ok(())
}

#[test]
fn registered_host_await_nested_arguments_report_register_overflow() {
    let nested_inputs = (0..40)
        .map(|_| "[1 + 2, 3 + 4, 5 + 6]")
        .collect::<Vec<_>>()
        .join(", ");
    let module = format!("package test\np := lookup({nested_inputs})");
    let error = compile_rule_with_host_await(&module, &[("lookup", 40)])
        .expect_err("nested inputs beyond the register window should fail compilation");
    assert!(
        error.to_string().contains("register"),
        "expected a register-capacity error, got {error}"
    );
}

#[test]
fn dynamic_default_nested_host_await_arguments_report_register_overflow() {
    let nested_inputs = (0..40)
        .map(|_| "[1 + 2, 3 + 4, 5 + 6]")
        .collect::<Vec<_>>()
        .join(", ");
    let module = format!("package test\ndefault p := [result | result := lookup({nested_inputs})]");
    let error = compile_rule_with_host_await(&module, &[("lookup", 40)])
        .expect_err("nested default inputs beyond the register window should fail compilation");

    match error
        .downcast_ref::<SpannedCompilerError>()
        .map(|error| &error.error)
    {
        Some(CompilerError::General { message }) => {
            let message = message.to_ascii_lowercase();
            assert!(
                message.contains("register overflow")
                    && message.contains("within the 255-register window"),
                "unexpected register-capacity diagnostic: {message}"
            )
        }
        other => panic!("expected explicit register-overflow diagnostic, got {other:?}: {error}"),
    }
}

#[test]
fn registered_host_await_uses_last_supported_register_window() {
    let compile_call = |arg_count: usize| {
        let args = std::iter::repeat_n("1", arg_count)
            .collect::<Vec<_>>()
            .join(", ");
        compile_rule_with_host_await(
            &format!("package test\np := lookup({args})"),
            &[("lookup", arg_count)],
        )
    };

    let mut last_supported = 0;
    let mut first_rejected = 253;
    while last_supported + 1 < first_rejected {
        let candidate = last_supported + (first_rejected - last_supported) / 2;
        if compile_call(candidate).is_ok() {
            last_supported = candidate;
        } else {
            first_rejected = candidate;
        }
    }

    let program = compile_call(last_supported)
        .expect("last supported registered HostAwait arity should compile");
    assert!(
        program.max_rule_window_size >= u8::MAX - 5,
        "expected a near-capacity program, got a {}-register window at arity {last_supported}",
        program.max_rule_window_size
    );

    let error = compile_call(first_rejected)
        .expect_err("first rejected registered HostAwait arity should fail");
    assert_eq!(first_rejected, last_supported + 1);
    match error
        .downcast_ref::<SpannedCompilerError>()
        .map(|error| &error.error)
    {
        Some(CompilerError::RegisterOverflow {
            current,
            additional,
        }) => {
            assert!(
                usize::from(*current) + *additional > usize::from(u8::MAX),
                "overflow error does not cross the register window: {current} + {additional}"
            );
        }
        other => panic!("expected structured register-overflow error, got {other:?}: {error}"),
    }
}
