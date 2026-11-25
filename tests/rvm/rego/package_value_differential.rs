// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for reading a package as a value.
//!
//! A rule that is undefined contributes no key to the document of its package:
//! `data.probe.sub` omits it, so `count`, `object.keys`, iteration, equality and
//! serialization never see it. Rules that are defined (including `false`,
//! defaults and empty partial sets/objects) are kept, and subpackages read as
//! objects even when all their rules are undefined or they have no rules.
//! Expected values were checked against OPA 1.2.0. Each query is evaluated in
//! the interpreter and in both RVM execution modes.

use anyhow::Result;
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{Engine, Value};

const SUB: &str = r#"
package probe.sub
import rego.v1
defined := 1
f := false
default d := "dflt"
d := "x" if input.x == 1
s contains x if x := input.missing[0]
o[k] := 1 if k := input.missing[0]
undefined_body if input.x == 1
undefined_value := input.missing
"#;

const INNER: &str = r#"
package probe.sub.inner
import rego.v1
u if input.x == 1
"#;

const CONSUMERS: &str = r#"
package probe
import rego.v1
result := data.probe.sub
n := count(data.probe.sub)
keys := object.keys(data.probe.sub)
pairs contains k if some k, _ in data.probe.sub
eq_check := data.probe.sub == {"defined": 1, "f": false, "d": "dflt", "o": {}, "s": set(), "inner": {}}
has_undefined_body if "undefined_body" in object.keys(data.probe.sub)
ser := json.marshal(data.probe.sub)
"#;

const WHOLE: &str = r#"
package top
whole := data.probe
"#;

const ALL_UNDEFINED: &str = r#"
package probe.sub
import rego.v1
undefined_body if input.x == 1
undefined_value := input.missing
"#;

const ALL_UNDEFINED_CONSUMERS: &str = r#"
package probe
result := data.probe.sub
n := count(data.probe.sub)
"#;

const EMPTY: &str = r#"{}"#;
const X1: &str = r#"{"x": 1}"#;
const ALL_DEFINED: &str = r#"{"x": 1, "missing": ["a"]}"#;

const SUB_EMPTY: &str = r#"{"d": "dflt", "defined": 1, "f": false, "inner": {}, "o": {}, "s": []}"#;
const SUB_X1: &str = r#"{"d": "x", "defined": 1, "f": false, "inner": {"u": true}, "o": {}, "s": [], "undefined_body": true}"#;
const SUB_ALL_DEFINED: &str = r#"{"d": "x", "defined": 1, "f": false, "inner": {"u": true}, "o": {"a": 1}, "s": ["a"], "undefined_body": true, "undefined_value": ["a"]}"#;
const KEYS_EMPTY: &str = r#"["d", "defined", "f", "inner", "o", "s"]"#;
const KEYS_X1: &str = r#"["d", "defined", "f", "inner", "o", "s", "undefined_body"]"#;

/// Normalizes a value to JSON (sets become arrays); `None` means undefined.
fn normalize(value: Result<Value>) -> Result<Option<Value>, String> {
    match value {
        Ok(Value::Undefined) => Ok(None),
        Ok(value) => value
            .to_json_str()
            .and_then(|json| Value::from_json_str(&json))
            .map(Some)
            .map_err(|err| format!("{value:?} ({err})")),
        Err(err) => Err(format!("error: {err:#}")),
    }
}

fn eval_rvm(engine: &mut Engine, query: &str, input: &Value, mode: ExecutionMode) -> Result<Value> {
    let compiled = engine.compile_with_entrypoint(&query.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[query])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data())?;
    vm.set_input(input.clone());
    vm.set_execution_mode(mode);
    Ok(vm.execute_entry_point_by_name(query)?)
}

fn check(modules: &[&str], cases: &[(&str, &str, Option<&str>)]) -> Result<()> {
    check_with_data(modules, "{}", cases)
}

/// Requires `query` on `input` with base `data` to produce `want` (`None` for
/// undefined) in the interpreter and in both RVM modes.
fn check_with_data(
    modules: &[&str],
    data: &str,
    cases: &[(&str, &str, Option<&str>)],
) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_data(Value::from_json_str(data)?)?;
    for (idx, module) in modules.iter().enumerate() {
        engine.add_policy(format!("p{idx}.rego"), module.to_string())?;
    }
    let mut failures = Vec::new();
    for &(query, input, want) in cases {
        let want = want.map(Value::from_json_str).transpose()?;
        let input_value = Value::from_json_str(input)?;
        engine.set_input(input_value.clone());

        let mut results = vec![("interpreter", engine.eval_rule(query.to_string()))];
        for (name, mode) in [
            ("run-to-completion", ExecutionMode::RunToCompletion),
            ("suspendable", ExecutionMode::Suspendable),
        ] {
            results.push((name, eval_rvm(&mut engine, query, &input_value, mode)));
        }
        for (name, got) in results {
            let got = normalize(got);
            if got.as_ref() != Ok(&want) {
                failures.push(format!(
                    "{query} [{name}] input {input}: want {want:?}, got {got:?}"
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}

#[test]
fn package_value_omits_undefined_rules() -> Result<()> {
    check(
        &[CONSUMERS, SUB, INNER],
        &[
            ("data.probe.result", EMPTY, Some(SUB_EMPTY)),
            ("data.probe.result", X1, Some(SUB_X1)),
            ("data.probe.result", ALL_DEFINED, Some(SUB_ALL_DEFINED)),
            ("data.probe.n", EMPTY, Some("6")),
            ("data.probe.n", X1, Some("7")),
            ("data.probe.n", ALL_DEFINED, Some("8")),
            ("data.probe.keys", EMPTY, Some(KEYS_EMPTY)),
            ("data.probe.keys", X1, Some(KEYS_X1)),
            ("data.probe.pairs", EMPTY, Some(KEYS_EMPTY)),
            ("data.probe.pairs", X1, Some(KEYS_X1)),
            ("data.probe.eq_check", EMPTY, Some("true")),
            ("data.probe.eq_check", X1, Some("false")),
            ("data.probe.has_undefined_body", EMPTY, None),
            ("data.probe.has_undefined_body", X1, Some("true")),
            (
                "data.probe.ser",
                EMPTY,
                Some(
                    r#""{\"d\":\"dflt\",\"defined\":1,\"f\":false,\"inner\":{},\"o\":{},\"s\":[]}""#,
                ),
            ),
            (
                "data.probe.ser",
                X1,
                Some(
                    r#""{\"d\":\"x\",\"defined\":1,\"f\":false,\"inner\":{\"u\":true},\"o\":{},\"s\":[],\"undefined_body\":true}""#,
                ),
            ),
        ],
    )
}

#[test]
fn parent_package_value_omits_undefined_rules_of_subpackages() -> Result<()> {
    check(
        &[WHOLE, SUB, INNER],
        &[
            (
                "data.top.whole",
                EMPTY,
                Some(&format!(r#"{{"sub": {SUB_EMPTY}}}"#)),
            ),
            (
                "data.top.whole",
                X1,
                Some(&format!(r#"{{"sub": {SUB_X1}}}"#)),
            ),
            (
                "data.top.whole",
                ALL_DEFINED,
                Some(&format!(r#"{{"sub": {SUB_ALL_DEFINED}}}"#)),
            ),
        ],
    )
}

#[test]
fn package_of_only_undefined_rules_is_empty_object() -> Result<()> {
    check(
        &[ALL_UNDEFINED_CONSUMERS, ALL_UNDEFINED],
        &[
            ("data.probe.result", EMPTY, Some("{}")),
            ("data.probe.n", EMPTY, Some("0")),
            ("data.probe.result", X1, Some(r#"{"undefined_body": true}"#)),
        ],
    )
}

#[test]
fn subpackages_without_rules_are_empty_objects() -> Result<()> {
    check(
        &[
            "package a\nx := 1",
            "package a.b\nf(v) := v",
            "package a.z",
            "package a.c.d.e\ny if false",
            "package q\nr := data.a\nb := data.a.b\nz := data.a.z\nn := count(data.a)\ndyn := data.a[input.k]",
        ],
        &[
            (
                "data.q.r",
                EMPTY,
                Some(r#"{"b": {}, "c": {"d": {"e": {}}}, "x": 1, "z": {}}"#),
            ),
            ("data.q.b", EMPTY, Some("{}")),
            ("data.q.z", EMPTY, Some("{}")),
            ("data.q.n", EMPTY, Some("4")),
            ("data.q.dyn", r#"{"k": "b"}"#, Some("{}")),
            ("data.q.dyn", r#"{"k": "z"}"#, Some("{}")),
            ("data.q.dyn", r#"{"k": "x"}"#, Some("1")),
            ("data.q.dyn", r#"{"k": "c"}"#, Some(r#"{"d": {"e": {}}}"#)),
            ("data.q.dyn", r#"{"k": "nope"}"#, None),
        ],
    )
}

#[test]
fn base_data_merges_with_packages_without_rules() -> Result<()> {
    let reads = "package q\np := data.a\nr := data.a.b\nc := data.a.b.c";
    let str_ab = r#"{"a": {"b": "str"}}"#;
    let p_str_ab = ("data.q.p", EMPTY, Some(r#"{"b": "str"}"#));
    let r_str = ("data.q.r", EMPTY, Some(r#""str""#));
    check_with_data(&["package a.b", reads], str_ab, &[p_str_ab, r_str])?;
    check_with_data(
        &[
            "package a\nx := 1",
            "package a.b\nf(v) := v",
            "package a.z",
            reads,
        ],
        r#"{"a": {"b": {"k": 1}}}"#,
        &[
            (
                "data.q.p",
                EMPTY,
                Some(r#"{"b": {"k": 1}, "x": 1, "z": {}}"#),
            ),
            ("data.q.r", EMPTY, Some(r#"{"k": 1}"#)),
        ],
    )?;
    check_with_data(
        &["package a.b", reads],
        r#"{"a": "str"}"#,
        &[
            ("data.q.p", EMPTY, Some(r#""str""#)),
            ("data.q.r", EMPTY, Some("{}")),
        ],
    )?;
    check_with_data(
        &["package a.b.c", reads],
        str_ab,
        &[p_str_ab, r_str, ("data.q.c", EMPTY, Some("{}"))],
    )
}

#[test]
fn packages_without_rules_at_or_below_base_arrays() -> Result<()> {
    // Some shapes in the interpreter YAML cases, such as iterating over a non-object value
    // with packages below it, still differ in the RVM.
    check_with_data(
        &[
            r#"package n["0"].b"#,
            "package q\nx := data.n[0].b\ny := data.n[\"0\"].b",
        ],
        r#"{"n": [{"x": 1}]}"#,
        &[("data.q.x", EMPTY, None), ("data.q.y", EMPTY, Some("{}"))],
    )?;
    check_with_data(
        &[
            "package a",
            "package e",
            "package q\nvalues := [v | v := data.a[_]]\nempty := [v | v := data.e[_]]",
        ],
        r#"{"a": [7], "e": []}"#,
        &[
            ("data.q.values", EMPTY, Some("[7]")),
            ("data.q.empty", EMPTY, Some("[]")),
        ],
    )
}

#[test]
fn packages_without_rules_below_base_strings_on_iterated_paths() -> Result<()> {
    check_with_data(
        &[
            "package a.b",
            "package q\nmissing := [v | v := data.rows[_].missing]",
        ],
        r#"{"a": "str", "rows": [{}]}"#,
        &[("data.q.missing", EMPTY, Some("[]"))],
    )?;
    // OPA 1.2.0 returns [{}, {}]: it binds k to "b" once for base data and once for the package.
    check_with_data(
        &[
            "package a.b.c",
            "package q\nvalues := [v | v := data.a[k][input.key]]",
        ],
        r#"{"a": {"b": "str"}}"#,
        &[("data.q.values", r#"{"key": "c"}"#, Some("[{}]"))],
    )
}
