// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::instructions::{ComprehensionBeginParams, ComprehensionMode};
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
use regorus::rvm::Instruction;
use regorus::{Engine, Rc, Value};
use std::sync::Arc;

fn assert_output(rule: &str, expected: Value) {
    let mut engine = Engine::new();
    engine
        .add_policy("test.rego".to_string(), format!("package test\n{rule}"))
        .unwrap();
    let policy = engine
        .compile_with_entrypoint(&Rc::from("data.test.p"))
        .unwrap();
    let program = Compiler::compile_from_policy(&policy, &["data.test.p"]).unwrap();
    assert_program_output(program, expected, rule);
}

fn assert_program_output(program: Arc<Program>, expected: Value, label: &str) {
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        for strict in [false, true] {
            let mut vm = RegoVM::new();
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(strict);
            vm.load_program(program.clone());
            let actual = vm.execute_entry_point_by_name("data.test.p").unwrap();
            assert_eq!(actual, expected, "{label}; {mode:?}; strict={strict}");
            if matches!(mode, ExecutionMode::Suspendable) {
                assert!(
                    matches!(vm.execution_state(), ExecutionState::Completed { result } if result == &expected),
                    "{label}; strict={strict}: {:?}",
                    vm.execution_state()
                );
            }
        }
    }
}

#[test]
fn complete_yields_preserve_defined_candidates() {
    for rows in [
        r#"[{"k":1},{}]"#,
        r#"[{},{"k":1}]"#,
        r#"[{},{"k":1},{},{"k":1},{}]"#,
    ] {
        assert_output(&format!("p := x.k if some x in {rows}"), Value::from(1));
    }
    assert_output("p := x.k if some x in [{},{}]", Value::Undefined);
    assert_output(
        r#"p := x.k if some x in [{"k":false},{}]"#,
        Value::Bool(false),
    );
    assert_output(r#"p := x.k if some x in [{"k":null},{}]"#, Value::Null);
    assert_output("p := {}.missing", Value::Undefined);
}

#[test]
fn partial_yields_skip_missing_keys_and_values() {
    assert_output(
        r#"p[x.key] := x.value if some x in [
            {"key":"ok","value":false}, {"key":"ok"},
            {"value":1}, {"key":"null","value":null}, {}
        ]"#,
        Value::from_json_str(r#"{"ok":false,"null":null}"#).unwrap(),
    );
    assert_output(
        r#"p[x.key] := x.value if some x in [{}, {"key":"absent"}]"#,
        Value::new_object(),
    );
    assert_output(
        r#"p contains x.k if some x in [{"k":false},{},{"k":null}]"#,
        Value::from(
            [Value::Bool(false), Value::Null]
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>(),
        ),
    );
}

#[test]
fn comprehension_yields_skip_missing_keys_and_values() {
    assert_output(
        r#"p := [x.k | some x in [{},{"k":false},{},{"k":null}]]"#,
        Value::from_json_str("[false,null]").unwrap(),
    );
    assert_output(
        r#"p := {x.k | some x in [{},{"k":false},{},{"k":null}]}"#,
        Value::from(
            [Value::Bool(false), Value::Null]
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>(),
        ),
    );
    assert_output(
        r#"p := {x.key:x.value | some x in [
            {"key":"ok","value":false}, {"key":"ok"},
            {"value":1}, {"key":"null","value":null}, {}
        ]}"#,
        Value::from_json_str(r#"{"ok":false,"null":null}"#).unwrap(),
    );
}

#[test]
fn nested_comprehension_missing_yields_do_not_fail_enclosing_loop() {
    for (expression, expected) in [
        ("[x.missing | true]", Value::new_array()),
        ("{x.missing | true}", Value::new_set()),
        ("{x.missing: false | true}", Value::new_object()),
        (r#"{"key": x.missing | true}"#, Value::new_object()),
    ] {
        assert_output(&format!("p := {expression} if some x in [{{}}]"), expected);
    }

    assert_output(
        r#"p := [[x.k | true] | some x in [{},{"k":false},{}]]"#,
        Value::from_json_str("[[],[false],[]]").unwrap(),
    );
    assert_output(
        r#"p := [[y.k | some y in x] | some x in [[{},{"k":false},{}], [{}]]]"#,
        Value::from_json_str("[[false],[]]").unwrap(),
    );
}

#[test]
fn automatic_comprehension_iteration_advances_after_missing_yields() {
    for (mode, expected) in [
        (
            ComprehensionMode::Array,
            Value::from_json_str(r#"["ok"]"#).unwrap(),
        ),
        (
            ComprehensionMode::Set,
            Value::from(
                [Value::from("ok")]
                    .into_iter()
                    .collect::<std::collections::BTreeSet<_>>(),
            ),
        ),
        (
            ComprehensionMode::Object,
            Value::from_json_str(r#"{"ok":"ok"}"#).unwrap(),
        ),
    ] {
        let mut program = Program::new();
        program.entry_points.insert("data.test.p".to_string(), 0);
        program.dispatch_window_size = 6;
        program.max_rule_window_size = 6;
        program.literals = vec![
            Value::from_json_str(r#"[{},{"k":"ok"},{}]"#).unwrap(),
            Value::from("k"),
        ];
        let params_index = program.add_comprehension_begin_params(ComprehensionBeginParams {
            mode,
            collection_reg: 0,
            result_reg: 1,
            key_reg: 2,
            value_reg: 3,
            body_start: 3,
            comprehension_end: 6,
        });
        for instruction in [
            Instruction::Load {
                dest: 0,
                literal_idx: 0,
            },
            Instruction::Load {
                dest: 5,
                literal_idx: 1,
            },
            Instruction::ComprehensionBegin { params_index },
            Instruction::Index {
                dest: 4,
                container: 3,
                key: 5,
            },
            Instruction::ComprehensionYield {
                value_reg: 4,
                key_reg: Some(4),
            },
            Instruction::ComprehensionEnd {},
            Instruction::Return { value: 1 },
        ] {
            program.add_instruction(instruction, None);
        }
        assert_program_output(Arc::new(program), expected, "automatic comprehension");
    }
}

#[test]
fn generic_index_move_and_object_set_keep_undefined_overwrite_semantics() {
    let mut program = Program::new();
    program.entry_points.insert("data.test.p".to_string(), 0);
    program.dispatch_window_size = 5;
    program.max_rule_window_size = 5;
    program.literals = vec![
        Value::from_json_str(r#"{"k":1}"#).unwrap(),
        Value::from("absent"),
        Value::from("k"),
    ];
    for instruction in [
        Instruction::Load {
            dest: 0,
            literal_idx: 0,
        },
        Instruction::Load {
            dest: 1,
            literal_idx: 1,
        },
        Instruction::LoadTrue { dest: 2 },
        Instruction::Index {
            dest: 2,
            container: 0,
            key: 1,
        },
        Instruction::LoadTrue { dest: 3 },
        Instruction::Move { dest: 3, src: 2 },
        Instruction::Load {
            dest: 1,
            literal_idx: 2,
        },
        Instruction::ObjectSet {
            obj: 0,
            key: 1,
            value: 3,
        },
        Instruction::LoadTrue { dest: 4 },
        Instruction::Index {
            dest: 4,
            container: 0,
            key: 1,
        },
        Instruction::ArrayNew { dest: 0 },
        Instruction::ArrayPush { arr: 0, value: 2 },
        Instruction::ArrayPush { arr: 0, value: 3 },
        Instruction::ArrayPush { arr: 0, value: 4 },
        Instruction::Return { value: 0 },
    ] {
        program.add_instruction(instruction, None);
    }
    assert_program_output(
        Arc::new(program),
        Value::from(vec![Value::Undefined; 3]),
        "generic undefined overwrite",
    );
}
