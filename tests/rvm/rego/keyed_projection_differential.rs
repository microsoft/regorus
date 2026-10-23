// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for keyed partial-set projection.
//!
//! Querying `data.test.values.a` lets both engines skip rule bodies whose key
//! cannot be "a". That pruning must never change the answer, so for every
//! generated policy and input the projected result has to equal the "a" entry
//! of the unprojected `data.test.values`, on the interpreter and on the RVM in
//! both execution modes.

use anyhow::{anyhow, bail, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{Engine, Rc, Value};

const PROJECTED: &str = "data.test.values.a";
const FULL: &str = "data.test.values";

// Head key expressions; each must be safe once the body binds `x`/`y`.
const KEYS: &[&str] = &["x", "input.key", "input.groups[_]", "y[_]", "x[0]"];

// Body statements; combined in order, so binding/use order varies.
const STMTS: &[&str] = &[
    "x := input.key",
    "x := \"a\"",
    "x := \"b\"",
    "x := input.missing",
    "some x in input.groups",
    "some i; x := input.groups[i]",
    "[x, _] := [input.key, 1]",
    "x := [input.key]",
    "y := input.groups",
    "y := [g | some g in input.groups; g != \"b\"]",
    "count(input.groups) > 0",
    "not input.deny",
    "every g in input.groups { g != \"z\" }",
    "input.key == \"a\"",
];

const INPUTS: &[&str] = &[
    r#"{"key": "a", "groups": ["a", "b"]}"#,
    r#"{"key": "b", "groups": ["b", "c"]}"#,
    r#"{"key": "a", "groups": [], "deny": true}"#,
    r#"{"groups": ["z", "a"]}"#,
    r#"{}"#,
];

fn bodies() -> Vec<Vec<&'static str>> {
    let mut bodies: Vec<Vec<&str>> = STMTS.iter().map(|s| vec![*s]).collect();
    for a in STMTS {
        for b in STMTS {
            if a != b {
                bodies.push(vec![*a, *b]);
            }
        }
    }
    bodies
}

// Rego v0 lets a body shadow `input`; projection must not filter on the
// global input before the shadow is bound.
const V0_SHADOWS: &[&str] = &[
    "input := {\"key\": \"a\", \"groups\": [\"a\"]}",
    "some input in [{\"key\": \"a\", \"groups\": [\"c\", \"a\"]}]",
];

fn v0_bodies() -> Vec<Vec<&'static str>> {
    let mut bodies = Vec::new();
    for shadow in V0_SHADOWS {
        bodies.push(vec![*shadow]);
        for stmt in STMTS {
            bodies.push(vec![*shadow, *stmt]);
            bodies.push(vec![*stmt, *shadow]);
        }
    }
    bodies
}

fn policy(key: &str, body: &[&str], v0: bool) -> String {
    format!(
        "package test\n{}\
         values.a contains 0\n\
         values[{key}] contains 1 if {{\n  {}\n}}\n\
         values[{key}] contains 2 if {{\n  {}\n  input.key != \"b\"\n}}\n",
        if v0 { "import future.keywords\n" } else { "" },
        body.join("\n  "),
        body.join("\n  "),
    )
}

fn engine(policy: &str) -> Result<Engine> {
    let mut engine = Engine::new();
    engine.set_rego_v0(policy.contains("import future.keywords"));
    engine.add_policy("test.rego".to_string(), policy.to_string())?;
    Ok(engine)
}

fn rvm_eval(policy: &str, entry: &str, input: &Value, mode: ExecutionMode) -> Result<Value> {
    let mut engine = engine(policy)?;
    let compiled = engine.compile_with_entrypoint(&Rc::from(entry))?;
    let program = Compiler::compile_from_policy(&compiled, &[entry])
        .map_err(|err| anyhow!("rvm compile {entry}\n{policy}{err}"))?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(Value::new_object())?;
    vm.set_execution_mode(mode);
    vm.set_input(input.clone());
    vm.execute_entry_point_by_name(entry)
        .map_err(|err| anyhow!("rvm {mode:?} {entry}\n{policy}input {input}\n{err}"))
}

fn is_invalid_policy(err: &anyhow::Error) -> bool {
    let err = err.to_string();
    ["unsafe", "used before definition", "Undefined variable"]
        .iter()
        .any(|msg| err.contains(msg))
}

fn check(key: &str, body: &[&str], v0: bool) -> Result<usize> {
    check_policy(&policy(key, body, v0), INPUTS)
}

fn check_policy(policy: &str, inputs: &[&str]) -> Result<usize> {
    let policy = policy.to_string();
    let mut oracle = match engine(&policy) {
        Ok(engine) => engine,
        // Unsafe or otherwise invalid generated policy.
        Err(_) => return Ok(0),
    };
    let mut checked = 0;
    let mut rvm_rejects_policy = false;
    for input in inputs {
        let input = Value::from_json_str(input)?;
        oracle.set_input(input.clone());
        let expected = match oracle.eval_rule(FULL.to_string()) {
            Ok(full) => full["a"].clone(),
            // Generated policies that are statically invalid.
            Err(err) if is_invalid_policy(&err) => return Ok(0),
            Err(err) => return Err(err),
        };
        let mut projected = engine(&policy)?;
        projected.set_input(input.clone());
        let projected = projected.eval_rule(PROJECTED.to_string())?;
        if projected != expected {
            bail!(
                "interpreter\n{policy}input {input}\nprojected {projected}\nunprojected {expected}"
            );
        }

        // The RVM is compared with its own unprojected result so that
        // pre-existing interpreter/RVM differences unrelated to projection
        // do not mask projection bugs.
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            if rvm_rejects_policy {
                break;
            }
            // The interpreter can skip a statically invalid head when the
            // body fails first; the RVM compiler rejects it up front. Only
            // that compile-time rejection is tolerated, and only for the RVM.
            let expected = match rvm_eval(&policy, FULL, &input, mode) {
                Ok(full) => full["a"].clone(),
                Err(err)
                    if is_invalid_policy(&err) && err.to_string().starts_with("rvm compile") =>
                {
                    rvm_rejects_policy = true;
                    break;
                }
                Err(err) => return Err(err),
            };
            let projected = rvm_eval(&policy, PROJECTED, &input, mode)?;
            if projected != expected {
                bail!("rvm {mode:?}\n{policy}input {input}\nprojected {projected}\nunprojected {expected}");
            }
        }
        checked += 1;
    }
    Ok(checked)
}

#[test]
fn keyed_projection_matches_unprojected_evaluation() -> Result<()> {
    let mut checked = 0;
    let mut failures = Vec::new();
    for key in KEYS {
        let cases = bodies()
            .into_iter()
            .map(|body| (body, false))
            .chain(v0_bodies().into_iter().map(|body| (body, true)));
        for (body, v0) in cases {
            match check(key, &body, v0) {
                Ok(count) => checked += count,
                Err(err) => failures.push(format!("{err:#}")),
            }
        }
    }
    if !failures.is_empty() {
        bail!(
            "{} of the generated cases diverged:\n{}",
            failures.len(),
            failures.join("\n---\n")
        );
    }
    // Guard against the generator silently producing only invalid policies.
    anyhow::ensure!(checked > 1000, "only {checked} cases checked");
    Ok(())
}

// Head keys bound only by head value loops: the key cannot be checked before
// the value loop that binds it.
const VALUE_LOOP_RULES: &[&str] = &[
    "values[k] contains input.items[k]",
    "values[k] contains input.items[k][_]",
    "values[k] contains input.items[k] if { input.items }",
    "values[input.keys[i]] contains input.vals[i]",
    "values[k] contains [k, v][_] if { some v in input.vals; k := input.keys[_] }",
    "values[k] contains input.items[k] if { k := input.key }",
];

const VALUE_LOOP_INPUTS: &[&str] = &[
    r#"{"items": {"a": 7, "b": 8}, "keys": ["b", "a"], "vals": [1, 2], "key": "a"}"#,
    r#"{"items": {"a": [7, 9], "b": []}, "keys": ["a"], "vals": [], "key": "b"}"#,
    r#"{"items": {}, "keys": [], "vals": [3]}"#,
    r#"{}"#,
];

#[test]
fn keyed_projection_value_loop_bound_keys() -> Result<()> {
    let mut checked = 0;
    let mut failures = Vec::new();
    for rule in VALUE_LOOP_RULES {
        for shadow in ["", "k := \"b\"\n"] {
            let policy = format!("package test\n{shadow}values.a contains 0\n{rule}\n");
            match check_policy(&policy, VALUE_LOOP_INPUTS) {
                Ok(count) => checked += count,
                Err(err) => failures.push(format!("{err:#}")),
            }
        }
    }
    if !failures.is_empty() {
        bail!(
            "{} cases diverged:\n{}",
            failures.len(),
            failures.join("\n---\n")
        );
    }
    anyhow::ensure!(checked >= 30, "only {checked} cases checked");
    Ok(())
}

// Self-referencing contributions: a rule whose head value or body reads
// `values.a` must be rejected by key before that read whenever its key is not
// "a", and must report recursion when it is. Unprojected evaluation always
// recurses here, so the oracle is a variant with the self-reference replaced
// by a constant and the contribution replaced by a marker.
const SELF_KEYS: &[&str] = &["target", "data.test.target", "targets[_]", "input.key", "x"];
const SELF_AUX: &[(&str, &str)] = &[("\"b\"", "[\"b\", \"c\"]"), ("\"a\"", "[\"c\", \"a\"]")];
// (projected value, oracle value, body). A body that reads `values.a` before
// a key derived from another rule is known may conservatively report
// recursion: early filtering never evaluates other rules before the body.
const SELF_SHAPES: &[(&str, &str, Option<&str>)] = &[
    ("[count(values.a)][_]", "[\"m\"][_]", None),
    ("count(values.a)", "\"m\"", None),
    ("[n, count(values.a)][_]", "[\"m\"][_]", Some("n := 1")),
    ("n", "\"m\"", Some("n := count(values.a)")),
    ("[count(values.a)][_]", "[\"m\"][_]", Some("x := input.key")),
    (
        "[count(values.a)][_]",
        "[\"m\"][_]",
        Some("some x in input.groups"),
    ),
    ("count(values.a)", "\"m\"", Some("x := target")),
    (
        "[g | some g in input.groups; count(values.a) > 0][_]",
        "[\"m\" | some g in input.groups][_]",
        Some("x := input.key"),
    ),
];

fn self_policy(key: &str, value: &str, body: Option<&str>, aux: (&str, &str)) -> String {
    let rule = match body {
        Some(body) => format!("values[{key}] contains {value} if {{\n  {body}\n}}"),
        None => format!("values[{key}] contains {value}"),
    };
    format!(
        "package test\ntarget := {}\ntargets := {}\nvalues.a contains 0\n{rule}\n",
        aux.0, aux.1
    )
}

fn check_self(key: &str, shape: &(&str, &str, Option<&str>), aux: (&str, &str)) -> Result<usize> {
    let (value, oracle_value, body) = *shape;
    let oracle_body = body.map(|body| body.replace("count(values.a)", "1"));
    let policy = self_policy(key, value, body, aux);
    let oracle_policy = self_policy(key, oracle_value, oracle_body.as_deref(), aux);
    if engine(&oracle_policy).is_err() {
        return Ok(0);
    }
    let body_reads_self =
        key.contains("target") && body.is_some_and(|body| body.contains("values.a"));
    let marker = Value::from("m");
    let verdict = |oracle: Value, projected: Result<Value>, label: &str, input: &Value| {
        let recursive = oracle.as_set().is_ok_and(|set| set.contains(&marker));
        let expected = if recursive {
            Value::Undefined
        } else {
            oracle.clone()
        };
        match projected {
            Err(err)
                if (recursive || body_reads_self)
                    && err.to_string().contains("recursion detected") =>
            {
                Ok(())
            }
            Ok(projected) if !recursive && projected == expected => Ok(()),
            other => Err(anyhow!(
                "{label}\n{policy}input {input}\nprojected {}\nexpected {}",
                match other {
                    Ok(value) => value.to_string(),
                    Err(err) => format!("error {err}"),
                },
                if recursive {
                    "recursion error".to_string()
                } else {
                    expected.to_string()
                }
            )),
        }
    };
    let mut checked = 0;
    for input in INPUTS {
        let input = Value::from_json_str(input)?;
        let mut oracle = engine(&oracle_policy)?;
        oracle.set_input(input.clone());
        let expected = match oracle.eval_rule(FULL.to_string()) {
            Ok(full) => full["a"].clone(),
            Err(err) if is_invalid_policy(&err) => return Ok(checked),
            Err(err) => return Err(err),
        };
        let mut projected = engine(&policy)?;
        projected.set_input(input.clone());
        verdict(
            expected,
            projected.eval_rule(PROJECTED.to_string()),
            "interpreter",
            &input,
        )?;
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let expected = match rvm_eval(&oracle_policy, FULL, &input, mode) {
                Ok(full) => full["a"].clone(),
                Err(err) if is_invalid_policy(&err) => return Ok(checked),
                Err(err) => return Err(err),
            };
            verdict(
                expected,
                rvm_eval(&policy, PROJECTED, &input, mode),
                &format!("rvm {mode:?}"),
                &input,
            )?;
        }
        checked += 1;
    }
    Ok(checked)
}

#[test]
fn keyed_projection_rejects_self_reads_by_key() -> Result<()> {
    let mut checked = 0;
    let mut failures = Vec::new();
    for key in SELF_KEYS {
        for shape in SELF_SHAPES {
            for aux in SELF_AUX {
                match check_self(key, shape, *aux) {
                    Ok(count) => checked += count,
                    Err(err) => failures.push(format!("{err:#}")),
                }
            }
        }
    }
    if !failures.is_empty() {
        bail!(
            "{} of the generated cases diverged:\n{}",
            failures.len(),
            failures.join("\n---\n")
        );
    }
    anyhow::ensure!(checked > 200, "only {checked} cases checked");
    Ok(())
}
