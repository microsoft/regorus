// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for variables bound by `every`.
//!
//! The key and value variables of `every k, v in D { ... }` are bound for the
//! whole body. Using them in an index (`m[k]`), a call, a comparison, a
//! unification or a nested quantifier must refer to the current element and
//! never start a new iteration. The interpreter is the oracle: each generated
//! policy must evaluate to the same value in the interpreter and in both RVM
//! execution modes.

use anyhow::{bail, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, RegoVM};
use regorus::{Engine, Value};

const ENTRYPOINT: &str = "data.t.p";

const DATA: &str = r#"{
  "mo": {"a": 3, "b": 5},
  "ma": [3, 5],
  "lo": {"a": [3, 4], "b": [9]},
  "la": [[3, 4], [9]],
  "no": {"a": {"lim": 3}, "b": {"lim": 5}},
  "na": [{"lim": 3}, {"lim": 5}],
  "idx": [0, 1, 2, 3, 4]
}"#;

const INPUTS: &[&str] = &[
    r#"{}"#,
    r#"{"o": {}, "a": []}"#,
    r#"{"o": {"a": 3}, "a": [3]}"#,
    r#"{"o": {"a": 4}, "a": [4]}"#,
    r#"{"o": {"a": 1, "b": 5}, "a": [1, 5]}"#,
    r#"{"o": {"a": 1, "b": 6}, "a": [1, 6]}"#,
    r#"{"o": {"z": 1}, "a": [1, 2, 3]}"#,
    r#"{"o": {"b": 2}, "a": [0, 2]}"#,
];

/// A domain of the quantifier and the data collections indexed by its keys.
struct Domain {
    name: &'static str,
    expr: &'static str,
    /// Collection whose keys are the domain's keys.
    m: &'static str,
    /// Collection of lists keyed like the domain.
    l: &'static str,
    /// Collection of objects keyed like the domain.
    n: &'static str,
}

const DOMAINS: &[Domain] = &[
    Domain {
        name: "object",
        expr: "input.o",
        m: "data.mo",
        l: "data.lo",
        n: "data.no",
    },
    Domain {
        name: "array",
        expr: "input.a",
        m: "data.ma",
        l: "data.la",
        n: "data.na",
    },
    Domain {
        name: "set",
        expr: "{x | some x in input.a}",
        m: "data.ma",
        l: "data.la",
        n: "data.na",
    },
];

/// Bodies that use the key `k` (and possibly the value `v`).
const KEY_BODIES: &[&str] = &[
    "v <= M[k]",
    "M[k] >= v",
    "v = M[k]",
    "M[k] = v",
    "x := M[k]\n    v <= x",
    "N[k].lim >= v",
    "count([1 | M[k] >= v]) == 1",
    "sprintf(\"%v\", [k]) != \"b\"",
    "k != \"b\"",
    "k != 1",
    "some kk, mv in M\n    kk == k\n    v <= mv",
    "some kk\n    M[kk] >= v\n    kk == k",
    "every w in L[k] { w >= v }",
    "every j, w in L[k] { w >= v + j }",
    "every k2, w in L { k2 != k; w > v }",
];

/// Bodies that use only the value `v`.
const VALUE_BODIES: &[&str] = &[
    "v <= 4",
    "data.idx[v] == v",
    "M[v] >= 0",
    "x := data.idx[v]\n    x >= 1",
    "count([1 | data.idx[v]]) == 1",
    "every w in [v] { data.idx[w] == v }",
];

/// The contexts that contain the `every` literal.
const WRAPPERS: &[(&str, &str)] = &[
    ("rule", "p if {\n  EVERY\n}\n"),
    ("default_rule", "default p := false\np if {\n  EVERY\n}\n"),
    ("function", "f(d) if {\n  EVERY_D\n}\np := f(DOMAIN)\n"),
    ("comprehension", "p := [1 |\n  EVERY\n]\n"),
];

fn quantifiers(domain: &Domain) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for body in KEY_BODIES {
        let body = body
            .replace('M', domain.m)
            .replace('L', domain.l)
            .replace('N', domain.n);
        out.push((
            format!("every k, v in DOM {{\n    {body}\n  }}"),
            format!("kv: {body}"),
        ));
        // An outer `every` whose value is the inner domain: `k` and `v` of the
        // inner quantifier are bound in the inner body only.
        out.push((
            format!("every _, outer in [DOM] {{\n    every k, v in outer {{\n      {body}\n    }}\n  }}"),
            format!("nested kv: {body}"),
        ));
    }
    for body in VALUE_BODIES {
        let body = body.replace('M', domain.m);
        out.push((
            format!("every v in DOM {{\n    {body}\n  }}"),
            format!("v: {body}"),
        ));
        out.push((
            format!("every _, v in DOM {{\n    {body}\n  }}"),
            format!("_v: {body}"),
        ));
    }
    out
}

fn policies() -> Vec<(String, String)> {
    let mut out = Vec::new();
    for domain in DOMAINS {
        for (quantifier, label) in quantifiers(domain) {
            for (wrapper_name, wrapper) in WRAPPERS {
                let policy = format!(
                    "package t\n{}",
                    wrapper
                        .replace("EVERY_D", &quantifier.replace("DOM", "d"))
                        .replace("EVERY", &quantifier.replace("DOM", domain.expr))
                        .replace("DOMAIN", domain.expr)
                );
                out.push((
                    format!("{} / {} / {}", domain.name, wrapper_name, label),
                    policy,
                ));
            }
        }
    }
    out
}

fn eval_rvm(
    engine: &mut Engine,
    inputs: &[Value],
    mode: ExecutionMode,
) -> Result<Vec<Result<Value>>> {
    let compiled = engine.compile_with_entrypoint(&ENTRYPOINT.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[ENTRYPOINT])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_data(engine.get_data())?;
    vm.set_execution_mode(mode);
    Ok(inputs
        .iter()
        .map(|input| {
            vm.set_input(input.clone());
            vm.execute_entry_point_by_name(ENTRYPOINT)
                .map_err(anyhow::Error::from)
        })
        .collect())
}

fn describe(result: &Result<Value>) -> String {
    match result {
        Ok(value) => format!("{value}"),
        Err(err) => format!("error: {err:#}"),
    }
}

#[test]
fn every_bound_variables_match_interpreter() -> Result<()> {
    let data = Value::from_json_str(DATA)?;
    let inputs = INPUTS
        .iter()
        .map(|input| Value::from_json_str(input))
        .collect::<Result<Vec<_>>>()?;

    let mut divergences = Vec::new();
    let mut checked = 0usize;
    for (name, policy) in policies() {
        let mut engine = Engine::new();
        engine.add_policy("t.rego".to_string(), policy.clone())?;
        engine.add_data(data.clone())?;

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

        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let actual = eval_rvm(&mut engine, &inputs, mode)?;
            for ((input, want), got) in INPUTS.iter().zip(&expected).zip(&actual) {
                checked += 1;
                let same = match (want, got) {
                    (Ok(want), Ok(got)) => want == got,
                    _ => false,
                };
                if !same {
                    divergences.push(format!(
                        "{name} [{mode:?}] input {input}: interpreter {}, RVM {}",
                        describe(want),
                        describe(got)
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

/// Evaluates `policy` on each input in the interpreter and in both RVM modes
/// and requires the expected value (`None` for undefined).
fn check_expected(policy: &str, data: &str, cases: &[(&str, Option<&str>)]) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy("t.rego".to_string(), policy.to_string())?;
    engine.add_data(Value::from_json_str(data)?)?;
    let inputs = cases
        .iter()
        .map(|(input, _)| Value::from_json_str(input))
        .collect::<Result<Vec<_>>>()?;
    let expected = cases
        .iter()
        .map(|(_, want)| want.map_or(Ok(Value::Undefined), Value::from_json_str))
        .collect::<Result<Vec<_>>>()?;

    for ((input, want), (input_json, _)) in inputs.iter().zip(&expected).zip(cases) {
        engine.set_input(input.clone());
        assert_eq!(
            &engine.eval_rule(ENTRYPOINT.to_string())?,
            want,
            "interpreter, input {input_json}\n{policy}"
        );
    }
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let actual = eval_rvm(&mut engine, &inputs, mode)?;
        for ((got, want), (input_json, _)) in actual.into_iter().zip(&expected).zip(cases) {
            assert_eq!(&got?, want, "{mode:?}, input {input_json}\n{policy}");
        }
    }
    Ok(())
}

/// The reduced reproducer, with expected values checked against OPA:
/// a value above its own key's limit or a key missing from the limits must
/// fail the quantifier even when another key's limit would allow it.
#[test]
fn every_key_indexes_current_element_in_both_vm_modes() -> Result<()> {
    let policy = r#"
        package t
        p if {
          every k, v in input.limits {
            v <= data.max[k]
          }
        }
    "#;
    check_expected(
        policy,
        r#"{"max": {"cpu": 4, "memory": 8}}"#,
        &[
            (r#"{"limits": {"cpu": 2, "memory": 8}}"#, Some("true")),
            (r#"{"limits": {"cpu": 8, "memory": 1}}"#, None),
            (r#"{"limits": {"cpu": 4}}"#, Some("true")),
            (r#"{"limits": {"cpu": 5}}"#, None),
            (r#"{"limits": {"gpu": 1}}"#, None),
            (r#"{"limits": {}}"#, Some("true")),
        ],
    )
}

/// Array and set domains, a function, a comprehension and a nested `every`,
/// with expected values checked against OPA 1.2.0. The interpreter and the
/// RVM share loop hoisting, so fixed expectations guard both.
#[test]
fn every_bound_variables_match_opa() -> Result<()> {
    const DATA: &str = r#"{"max": {"cpu": 4, "memory": 8}, "ma": [3, 5]}"#;
    const INPUTS: [&str; 6] = [
        r#"{"a": [3, 5], "limits": {"cpu": 2, "memory": 8}}"#,
        r#"{"a": [4, 1], "limits": {"cpu": 8, "memory": 1}}"#,
        r#"{"a": [1, 2, 3], "limits": {"gpu": 1}}"#,
        r#"{"a": [0, 1], "limits": {"cpu": 5}}"#,
        r#"{"a": [], "limits": {}}"#,
        r#"{"a": [0, 2], "limits": {"cpu": 4}}"#,
    ];
    const T: Option<&str> = Some("true");
    let policies: [(&str, [Option<&str>; 6]); 5] = [
        (
            "p if { every i, v in input.a { v <= data.ma[i] } }",
            [T, None, None, T, T, T],
        ),
        (
            "p if { every k, v in {x | some x in input.a} { k == v; data.ma[k] >= 3 } }",
            [None, None, None, T, T, None],
        ),
        (
            "f(d) if { every k, v in d { v <= data.max[k] } }\np := f(input.limits)",
            [T, None, None, None, T, T],
        ),
        (
            "p := [1 | every k, v in input.limits { v <= data.max[k] }]",
            [
                Some("[1]"),
                Some("[]"),
                Some("[]"),
                Some("[]"),
                Some("[1]"),
                Some("[1]"),
            ],
        ),
        (
            "p if { every _, o in [input.limits] { every k, v in o { v <= data.max[k] } } }",
            [T, None, None, None, T, T],
        ),
    ];
    for (rules, expected) in policies {
        let cases: Vec<_> = INPUTS.into_iter().zip(expected).collect();
        check_expected(&format!("package t\n{rules}"), DATA, &cases)?;
    }
    Ok(())
}

/// A `some .. in` in a nested scope (comprehension or nested `every`) may
/// redeclare a variable bound by an enclosing `every`, as in OPA 1.2.0, and the
/// nested scope then uses its own binding.
#[test]
fn every_bound_variables_can_be_shadowed_in_nested_scopes() -> Result<()> {
    const INPUTS: [&str; 3] = [
        r#"{"a": [1, 2], "o": {"p": 1}}"#,
        r#"{"a": [], "o": {}}"#,
        r#"{"a": [0], "o": {"p": 0}}"#,
    ];
    const T: Option<&str> = Some("true");
    let policies: [(&str, [Option<&str>; 3]); 5] = [
        (
            "p := [r | some n in input.a; r := [x | some x in [5, 6]; x > n]] if {\n  every x in input.a { x > 0; [x | some x in [5, 6]] == [5, 6] }\n}",
            [Some("[[5, 6], [5, 6]]"), Some("[]"), None],
        ),
        (
            "p if { every k, x in input.o { k != \"\"; x > 0; {a: x | some a, x in {\"q\": 5}} == {\"q\": 5} } }",
            [T, T, None],
        ),
        (
            "p if { every x in input.a { x > 0; every y in [3] { y > 0; some x in [5]; x == 5 } } }",
            [T, T, None],
        ),
        (
            "p if { every x in input.a { x > 0; count([1 | count([2 | some x in [5, 6]]) == 2]) == 1 } }",
            [T, T, None],
        ),
        (
            "p if { every x in input.a { x > 0; {x | some x in [5]} == {5} } }",
            [T, T, None],
        ),
    ];
    for (rules, expected) in policies {
        let cases: Vec<_> = INPUTS.into_iter().zip(expected).collect();
        check_expected(&format!("package t\n{rules}"), "{}", &cases)?;
    }
    Ok(())
}

/// Redeclaring a variable bound by `every` inside its body is a compile error,
/// as in OPA (`var x declared above` / `var x assigned above`). Regorus reports
/// the earlier binding as a use before the redeclaration.
#[test]
fn every_bound_variables_cannot_be_redeclared() -> Result<()> {
    const POLICIES: &[(&str, &str)] = &[
        ("p if { every x in [1] { x := 2 } }", "x"),
        ("p if { every k, x in [1] { k := 0 } }", "k"),
        ("p if { every k, v in [1] { some k in [0] } }", "k"),
        ("p if { every v in [1, 2] { some v in [3] } }", "v"),
        ("p if { every v in [1, 2] { some v in [1, 2, 3] } }", "v"),
        ("p := [1 | every x in [1] { x := 2 }]", "x"),
        ("f(d) if { every x in d { x := 2 } }\np := f([1])", "x"),
    ];
    for (rules, var) in POLICIES {
        let policy = format!("package t\n{rules}");
        let mut engine = Engine::new();
        let outcome = engine
            .add_policy("t.rego".into(), policy)
            .and_then(|_| engine.eval_rule(ENTRYPOINT.into()));
        let Err(err) = outcome else {
            bail!("`{rules}` was accepted: {outcome:?}");
        };
        let message = format!("{err:#}");
        if !message.contains(&format!("var `{var}` used before definition")) {
            bail!("`{rules}` failed with an unexpected error: {message}");
        }
    }
    Ok(())
}
