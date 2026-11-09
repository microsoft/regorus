// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for failing conditions inside comprehensions.
//!
//! A failed condition in a comprehension body ends that comprehension
//! iteration only. It must not fail an enclosing loop iteration, and once the
//! comprehension is finished it must not catch later failures in the same
//! body. The interpreter is the oracle for both RVM execution modes.

use anyhow::{bail, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
use regorus::{Engine, Value};

const ENTRYPOINT: &str = "data.t.p";

const INPUTS: &[&str] = &[
    r#"{}"#,
    r#"{"a": [1, 2]}"#,
    r#"{"a": [1, 2], "f": true}"#,
    r#"{"a": [1, 2], "f": 2}"#,
    r#"{"a": [1, 2], "g": true}"#,
    r#"{"a": [], "f": 1}"#,
    r#"{"a": [1, 2, 3], "f": 2, "g": true}"#,
];

/// Comprehensions whose body holds condition `COND`.
const COMPREHENSIONS: &[&str] = &["[1 | COND]", "{1 | COND}", "{\"k\": 1 | COND}"];

const CONDITIONS: &[&str] = &["input.f", "input.f == x"];

/// Statements that use comprehension `COMP`.
const BODIES: &[&str] = &[
    "count(COMP) == 0",
    "count(COMP) == 1",
    "count(COMP) == 0\n  input.g",
    "y := COMP\n  count(y) == count(COMP)\n  input.g",
];

/// The statements around the comprehension; `x` is bound in each of them.
const WRAPPERS: &[(&str, &str)] = &[
    ("body", "p if {\n  x := 1\n  BODY\n}\n"),
    ("some_in", "p if {\n  some x in input.a\n  BODY\n}\n"),
    ("index", "p if {\n  x := input.a[_]\n  BODY\n}\n"),
    ("every", "p if {\n  every x in input.a {\n  BODY\n  }\n}\n"),
    (
        "comprehension",
        "p := [x |\n  some x in input.a\n  BODY\n]\n",
    ),
];

fn policies() -> Vec<(String, String)> {
    let mut out = Vec::new();
    for comprehension in COMPREHENSIONS {
        for condition in CONDITIONS {
            let comprehension = comprehension.replace("COND", condition);
            for body in BODIES {
                let body = body.replace("COMP", &comprehension);
                for (wrapper_name, wrapper) in WRAPPERS {
                    out.push((
                        format!("{wrapper_name} / {}", body.replace('\n', ";")),
                        format!("package t\n{}", wrapper.replace("BODY", &body)),
                    ));
                }
            }
        }
    }
    out
}

fn describe(result: &Result<Value>) -> String {
    match result {
        Ok(value) => format!("{value}"),
        Err(err) => format!("error: {err:#}"),
    }
}

#[test]
fn comprehension_condition_failures_match_interpreter() -> Result<()> {
    let inputs = INPUTS
        .iter()
        .map(|input| Value::from_json_str(input))
        .collect::<Result<Vec<_>>>()?;

    let mut divergences = Vec::new();
    let mut checked = 0usize;
    for (name, policy) in policies() {
        let mut engine = Engine::new();
        engine.add_policy("t.rego".to_string(), policy.clone())?;

        let expected: Vec<Result<Value>> = inputs
            .iter()
            .map(|input| {
                engine.set_input(input.clone());
                engine.eval_rule(ENTRYPOINT.to_string())
            })
            .collect();
        if let Some(Err(err)) = expected.iter().find(|r| r.is_err()) {
            bail!("interpreter error for `{name}`:\n{policy}\n{err}");
        }

        let compiled = engine.compile_with_entrypoint(&ENTRYPOINT.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[ENTRYPOINT])?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            for ((input_json, input), want) in INPUTS.iter().zip(&inputs).zip(&expected) {
                checked += 1;
                vm.set_input(input.clone());
                let got = vm
                    .execute_entry_point_by_name(ENTRYPOINT)
                    .map_err(anyhow::Error::from);
                let same = match (want, &got) {
                    (Ok(want), Ok(got)) => want == got,
                    _ => false,
                };
                if !same {
                    divergences.push(format!(
                        "{name} [{mode:?}] input {input_json}: interpreter {}, RVM {}",
                        describe(want),
                        describe(&got)
                    ));
                }
            }
        }
    }

    assert!(
        divergences.is_empty(),
        "{} of {checked} RVM results differ from the interpreter:\n{}",
        divergences.len(),
        divergences.join("\n")
    );
    Ok(())
}

#[test]
fn rejected_query_preserves_root_availability() -> Result<()> {
    let cases = [
        "not [input.x | 1 = 2] == [1]; input.x == 7",
        "not [data.x | 1 = 2] == [1]; data.x == 7",
        "input.x == 7; not [input.x | 1 = 2] == [1]; input.x == 7",
        "data.x == 7; not [data.x | 1 = 2] == [1]; data.x == 7",
        "not [[input.x, data.x] | 1 = 2] == [1]; input.x == 7; data.x == 7",
        "not {input.x | 1 = 2} == {1}; input.x == 7",
        r#"not {"k": data.x | 1 = 2} == {"k": 1}; data.x == 7"#,
        "not [input.x | 1 = 1] == [1]; input.x == 7",
        "not [data.x | 1 = 1] == [1]; data.x == 7",
        "not [input.x | not [data.x | 1 = 2] = [1]] = [1]; input.x == 7; data.x == 7",
        "not [input.x | every y in [1] { not [data.x | 1 = 2] = [1] }] = [1]; input.x == 7; data.x == 7",
        "every y in [] { input.x == y }; input.x == 7",
        "every y in [] { data.x == y }; data.x == 7",
        "[input.x | 1 = 2] == []; input.x == 7",
        "[data.x | 1 = 2] == []; data.x == 7",
    ];
    let mut divergences = Vec::new();
    for body in cases {
        let mut engine = Engine::new();
        engine.add_policy(
            "t.rego".into(),
            format!("package t\nimport rego.v1\ndefault p := false\np if {{ {body} }}"),
        )?;
        let roots = Value::from_json_str(r#"{"x":7}"#)?;
        engine.set_input(roots.clone());
        engine.add_data(roots.clone())?;
        let expected = Value::Bool(true);
        assert_eq!(engine.eval_rule(ENTRYPOINT.into())?, expected, "{body}");
        let compiled = engine.compile_with_entrypoint(&ENTRYPOINT.into())?;
        let program = Compiler::compile_from_policy(&compiled, &[ENTRYPOINT])?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.set_execution_mode(mode);
            vm.load_program(program.clone());
            vm.set_input(roots.clone());
            vm.set_data(roots.clone())?;
            let got = vm.execute_entry_point_by_name(ENTRYPOINT)?;
            if mode == ExecutionMode::Suspendable {
                assert_eq!(
                    vm.execution_state(),
                    &ExecutionState::Completed {
                        result: got.clone()
                    }
                );
            }
            if got != expected {
                divergences.push(format!("{body}, {mode:?}: {got:?} != {expected:?}"));
            }
        }
    }
    assert!(divergences.is_empty(), "{}", divergences.join("\n"));
    Ok(())
}

#[test]
fn nested_query_assertion_mode_matches_interpreter() -> Result<()> {
    let cases = [
        ("not [1 | not [1 | not 1 = input.x] == [1]] = [1]", 2, true),
        ("not [1 | not [1 | not 1 = input.x] == [1]] = [1]", 1, false),
        (
            "not [1 | every y in [input.x] { not [1 | not 1 = y] == [1] }] = [1]",
            2,
            true,
        ),
        (
            "not [1 | every y in [input.x] { not [1 | not 1 = y] == [1] }] = [1]",
            1,
            false,
        ),
        ("not [1 | 1 = input.x] = [1]", 2, true),
        ("not [1 | 1 = input.x] = [1]", 1, false),
        ("not [1 | 1 = input.missing] = [1]", 2, true),
        ("not [1 | 1 = input.x] = input.missing", 2, true),
        ("not [1 | [y] := input.payload] = []", 2, false),
        ("not [1 | [y] := input.payload] = [1]", 2, true),
        ("not [1 | [y] := input.payload] = [1]", 1, false),
        ("not [1 | [1] = input.elements] = [1]", 2, true),
        ("not [1 | [1] = input.elements] = [1]", 1, false),
        ("not [1 | [input.expected] = input.elements] = [1]", 2, true),
        (
            "not [1 | [input.expected] = input.elements] = [1]",
            1,
            false,
        ),
        // Binding y selects destructuring, not a whole-array EqualityCheck.
        ("not [1 | [y, 1] = input.pattern_elements] = [1]", 2, true),
        ("not [1 | [y, 1] = input.pattern_elements] = [1]", 1, false),
        (
            "not [1 | [y, input.expected] = input.pattern_elements] = [1]",
            2,
            true,
        ),
        (
            "not [1 | [y, input.expected] = input.pattern_elements] = [1]",
            1,
            false,
        ),
        ("not [1 | 1 = input.x] == [1]", 2, true),
        ("not [1 | 1 = input.x] == [1]", 1, false),
        ("[1 | 1 = input.x] == []", 2, true),
        ("[1 | 1 = input.x] == [1]", 1, true),
        ("not [1 | not 1 = input.x] == [1]", 2, false),
        ("not [1 | not 1 = input.x] == [1]", 1, true),
        ("not {1 | 1 = input.x} == {1}", 2, true),
        (r#"not {"k": 1 | 1 = input.x} == {"k": 1}"#, 2, true),
        ("not [1 | every x in [input.x] { 1 = x }] == [1]", 2, true),
    ];
    let mut divergences = Vec::new();
    for (body, x, want) in cases {
        for strict in [false, true] {
            let mut engine = Engine::new();
            engine.set_strict_builtin_errors(strict);
            engine.add_policy(
                "t.rego".to_string(),
                format!("package t\nimport rego.v1\ndefault p := false\np if {{ {body} }}"),
            )?;
            let payload = if x == 1 { "[7]" } else { "[]" };
            let input = Value::from_json_str(&format!(
                r#"{{"x": {x}, "payload": {payload}, "elements": [{x}], "pattern_elements": [7, {x}], "expected": 1}}"#
            ))?;
            engine.set_input(input.clone());
            let expected = Value::Bool(want);
            assert_eq!(engine.eval_rule(ENTRYPOINT.into())?, expected, "{body}");
            let compiled = engine.compile_with_entrypoint(&ENTRYPOINT.into())?;
            let program = Compiler::compile_from_policy(&compiled, &[ENTRYPOINT])?;
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.set_strict_builtin_errors(strict);
                vm.set_execution_mode(mode);
                vm.load_program(program.clone());
                vm.set_input(input.clone());
                let got = vm.execute_entry_point_by_name(ENTRYPOINT)?;
                if got != expected {
                    divergences.push(format!(
                        "{body}, x={x}, {mode:?}, strict={strict}: {got:?} != {expected:?}"
                    ));
                }
                if mode == ExecutionMode::Suspendable {
                    assert_eq!(
                        vm.execution_state(),
                        &ExecutionState::Completed {
                            result: got.clone()
                        }
                    );
                }
            }
        }
    }
    assert!(divergences.is_empty(), "{}", divergences.join("\n"));
    Ok(())
}
