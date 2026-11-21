// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(all(feature = "rvm", feature = "history"))]

use history_syntax::{Component, RuleMode};
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use regorus::languages::rego::compiler::{Compiler, HISTORY_BATCH_SIZE};
use regorus::rvm::program::{
    generate_assembly_listing, AssemblyListingConfig, DeserializationResult, Program,
};
use regorus::rvm::vm::{ExecutionMode, RegoVM, VmError};
use regorus::rvm::Instruction;
use regorus::Engine;
use std::sync::Arc;

const MODES: [ExecutionMode; 2] = [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable];
const REQUEST: &str = r#"{"action": "release", "principal": actor, "resource": doc}"#;
const LANGUAGE: &str = r#"[any, {principal == actor, action == "edit", resource == doc}, any]"#;

/// Compile a Rego module through the engine and the RVM compiler.
fn program(source: &str, entry_points: &[&str]) -> Arc<Program> {
    let mut engine = Engine::new();
    engine.add_policy("t.rego".into(), source.into()).unwrap();
    let policy = engine
        .compile_with_entrypoint(&entry_points[0].into())
        .unwrap();
    Compiler::compile_from_policy(&policy, entry_points).unwrap()
}

fn module(body: &str) -> String {
    format!("package t\nimport rego.v1\n{body}")
}

fn prior_edit_source() -> FlatPair<String> {
    FlatPair {
        head: vec![
            FlatHead::Bind,
            FlatHead::Constant("release".to_owned()),
            FlatHead::Bind,
        ],
        tests: vec![
            FlatTest::Atom {
                field: Component(0),
                term: FlatTerm::Variable(Component(0)),
                positive: true,
            },
            FlatTest::Atom {
                field: Component(1),
                term: FlatTerm::Constant("edit".to_owned()),
                positive: true,
            },
            FlatTest::Atom {
                field: Component(2),
                term: FlatTerm::Variable(Component(2)),
                positive: true,
            },
            FlatTest::And(vec![0, 1, 2]),
        ],
        regexes: vec![
            FlatRegex::All,
            FlatRegex::Test(3),
            FlatRegex::All,
            FlatRegex::Concat(vec![0, 1, 2]),
        ],
        root: 3,
    }
}

fn history_steps(program: &Program) -> usize {
    program
        .instructions
        .iter()
        .filter(|instruction| matches!(instruction, Instruction::HistoryStep { .. }))
        .count()
}

/// A `require` row followed by a `forbid` row.
fn two_rules() -> Arc<Program> {
    program(
        &module(&format!(
            "r0 := history.require({REQUEST}, {LANGUAGE})\n\
             r1 := history.forbid({{\"principal\": p}}, star({{principal == p}}))\n"
        )),
        &["data.t.r0", "data.t.r1"],
    )
}

#[test]
fn rego_history_rules_lower_to_one_table_and_history_step() {
    let program = program(
        &module(&format!("r0 := history.require({REQUEST}, {LANGUAGE})\n")),
        &["data.t.r0"],
    );
    assert_eq!(program.history_tables.len(), 1);
    let rules = &program.history_tables[0].rules;
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].mode, RuleMode::Require);
    assert_eq!(rules[0].source, prior_edit_source());
    let steps = &program.instruction_data.history_step_params;
    assert_eq!(steps.len(), 1);
    assert_eq!(
        (steps[0].table, steps[0].rule, steps[0].batch_size),
        (0, 0, HISTORY_BATCH_SIZE)
    );
    assert_eq!(history_steps(&program), 1);
    let listing = generate_assembly_listing(&program, &AssemblyListingConfig::default());
    assert!(
        listing.contains(&format!(
            "HistoryStep table[0].rule[0] batch_size={HISTORY_BATCH_SIZE} dest=r{}",
            steps[0].dest
        )),
        "{listing}"
    );

    // Each call adds one ordered row to the same table and one step instruction.
    let program = two_rules();
    assert_eq!(program.history_tables.len(), 1);
    let modes: Vec<_> = program.history_tables[0]
        .rules
        .iter()
        .map(|rule| rule.mode)
        .collect();
    assert_eq!(modes, [RuleMode::Require, RuleMode::Forbid]);
    let rows: Vec<_> = program
        .instruction_data
        .history_step_params
        .iter()
        .map(|step| (step.table, step.rule))
        .collect();
    assert_eq!(rows, [(0, 0), (0, 1)]);
    assert_eq!(history_steps(&program), 2);
}

fn history_rule_error(call: &str) -> String {
    let mut engine = Engine::new();
    engine
        .add_policy("t.rego".into(), module(&format!("r0 := history.{call}\n")))
        .unwrap();
    let policy = engine.compile_with_entrypoint(&"data.t.r0".into()).unwrap();
    Compiler::compile_from_policy(&policy, &["data.t.r0"])
        .unwrap_err()
        .to_string()
}

#[test]
fn malformed_history_rules_report_compile_errors() {
    for (call, message) in [
        (
            r#"require({"actor": a}, any)"#,
            "request pattern must be an object",
        ),
        (r#"require([], any)"#, "request pattern must be an object"),
        (
            r#"require({"action": "a", "action": "b"}, any)"#,
            "duplicate request coordinate",
        ),
        (
            r#"require({"principal": action}, any)"#,
            "shadows the coordinate name",
        ),
        (
            r#"require({"principal": 1}, any)"#,
            "must be a string constant or a variable",
        ),
        (
            r#"require({}, [any, {action < "x"}])"#,
            "comparison must be",
        ),
        (
            r#"require({}, [any, {"edit" == action}])"#,
            "comparison must be",
        ),
        (
            r#"require({}, [any, {"action": "edit"}, any])"#,
            "unsupported history expression",
        ),
        (r#"require({}, everything)"#, "unknown name `everything`"),
        (r#"require({}, star())"#, "star takes one argument"),
        (r#"require({})"#, "take two arguments"),
        (r#"forbid({}, any, any)"#, "take two arguments"),
        (
            r#"require({}, {principal == any})"#,
            "comparison term must be",
        ),
        (
            r#"require({}, {principal == action})"#,
            "comparison term must be",
        ),
        (
            r#"require({"action": "release", "principal": x}, {resource == x})"#,
            "invalid history rule",
        ),
        (
            r#"require({}, {principal == missing})"#,
            "invalid history rule",
        ),
    ] {
        let error = history_rule_error(call);
        assert!(error.contains(message), "{call}: {error}");
    }
}

#[test]
fn history_step_is_a_fatal_unimplemented_error() {
    let source = module(&format!(
        "r0 := history.require({REQUEST}, {LANGUAGE})\nallow if {{\n    r0\n}}\n"
    ));
    let program = program(&source, &["data.t.r0", "data.t.allow"]);
    for entry in ["data.t.r0", "data.t.allow"] {
        for mode in MODES {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            let result = vm.execute_entry_point_by_name(entry);
            assert!(
                matches!(result, Err(VmError::HistoryUnimplemented { .. })),
                "{entry} {mode:?}: {result:?}"
            );
        }
    }

    // History rules are RVM-only.
    let mut engine = Engine::new();
    engine.add_policy("t.rego".into(), source).unwrap();
    assert!(engine.eval_rule("data.t.allow".into()).is_err());
}

#[test]
fn compiled_programs_roundtrip_history_tables() {
    let program = two_rules();
    let DeserializationResult::Complete(binary) =
        Program::deserialize_binary(&program.serialize_binary().unwrap()).unwrap()
    else {
        panic!("current version must deserialize completely");
    };
    let json = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
    for restored in [binary, json] {
        assert_eq!(restored.history_tables.len(), 1);
        for (restored, original) in restored.history_tables[0]
            .rules
            .iter()
            .zip(&program.history_tables[0].rules)
        {
            assert_eq!(restored.mode, original.mode);
            assert_eq!(restored.source, original.source);
        }
        let steps = |program: &Program| -> Vec<_> {
            program
                .instruction_data
                .history_step_params
                .iter()
                .map(|step| (step.table, step.rule, step.batch_size, step.dest))
                .collect()
        };
        assert_eq!(steps(&restored), steps(&program));
        assert_eq!(restored.instructions.len(), program.instructions.len());
        assert_eq!(history_steps(&restored), 2);
    }
}
