// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Regression tests: the state edited by `with` modifiers (the with-document
//! and function mocks) must be restored even when the statement fails, and
//! must not survive into the rest of the evaluation or into a later
//! evaluation on a reused `Engine`.
//!
//! Each policy has a trigger rule `r` whose statement fails after its `with`
//! modifiers were applied, either in a later modifier's `as` expression or in
//! the statement's loop expression. The object rule `o[r]["k"]` has an
//! undefined body, so the interpreter evaluates its head reference `r` and
//! ignores the error. `probe` then checks whether the `with` edits leaked.
//!
//! Run with `cargo test --test with_state_leak -- --nocapture --test-threads=1`
//! to print the observed values.

use regorus::{Engine, Value};

const UNDEFINED: &str = "undefined";

const PROBE_DATA: &str = r#"probe = v { _ = [k | o[k]]; v := data.leak with input.z as 1 }"#;
const PROBE_MOCK: &str = r#"probe = v { _ = [k | o[k]]; v := count([1, 2]) }"#;

struct Case {
    name: &'static str,
    trigger: &'static str,
    probe: &'static str,
    request1: &'static str,
    request2: &'static str,
    // The answer when nothing leaks.
    clean: &'static str,
}

fn policy(case: &Case) -> String {
    format!(
        "package t\n\n{}\n\no[r][\"k\"] = 1 {{ false }}\n\n{}\n",
        case.trigger, case.probe
    )
}

fn new_engine(case: &Case) -> Engine {
    let mut engine = Engine::new();
    engine.set_rego_v0(true);
    engine
        .add_policy("with_state_leak.rego".to_string(), policy(case))
        .expect("policy should parse");
    engine
}

fn eval(engine: &mut Engine, input: &str, query: &str) -> Result<String, String> {
    engine.set_input(Value::from_json_str(input).expect("valid input"));
    let results = engine
        .eval_query(query.to_string(), false)
        .map_err(|e| e.to_string())?;
    match results.result.first() {
        None => Ok(UNDEFINED.to_string()),
        Some(r) => Ok(r.expressions[0]
            .value
            .to_json_str()
            .map_err(|e| e.to_string())?
            .trim()
            .to_string()),
    }
}

fn fmt(r: &Result<String, String>) -> String {
    match r {
        Ok(v) => v.clone(),
        Err(e) => {
            let line = e.lines().map(str::trim).rfind(|l| !l.is_empty());
            format!("error({})", line.unwrap_or_default())
        }
    }
}

fn run(case: &Case) {
    // The trigger must fail for request 1 and succeed for request 2.
    let trigger1 = eval(&mut new_engine(case), case.request1, "data.t.r");
    let trigger2 = eval(&mut new_engine(case), case.request2, "data.t.r");

    let fresh1 = eval(&mut new_engine(case), case.request1, "data.t.probe");
    let fresh2 = eval(&mut new_engine(case), case.request2, "data.t.probe");

    let mut engine = new_engine(case);
    let reused1 = eval(&mut engine, case.request1, "data.t.probe");
    let reused2 = eval(&mut engine, case.request2, "data.t.probe");

    println!(
        "{} | trigger r: req1={} req2={} | fresh: req1={} req2={} | reused: req1={} req2={}",
        case.name,
        fmt(&trigger1),
        fmt(&trigger2),
        fmt(&fresh1),
        fmt(&fresh2),
        fmt(&reused1),
        fmt(&reused2),
    );

    assert!(
        matches!(&trigger1, Err(e) if e.contains("divide by zero")),
        "{}: request 1 must hit the trigger, got {trigger1:?}",
        case.name
    );
    assert!(
        trigger2.is_ok(),
        "{}: request 2 must not fail, got {trigger2:?}",
        case.name
    );

    let clean = Ok(case.clean.to_string());
    assert_eq!(fresh2, clean, "{}: fresh engine, request 2", case.name);
    assert_eq!(
        reused2, fresh2,
        "{}: reused engine, request 2 sees state left by request 1",
        case.name
    );
    assert_eq!(fresh1, clean, "{}: fresh engine, request 1", case.name);
    assert_eq!(reused1, clean, "{}: reused engine, request 1", case.name);
}

#[test]
fn modifier_error_with_data() {
    run(&Case {
        name: "1 modifier/data",
        trigger: r#"r = v { v := input.a with data.leak as input.secret with input.b as (1 / input.d) }"#,
        probe: PROBE_DATA,
        request1: r#"{"secret":"r1","d":0}"#,
        request2: r#"{"d":1}"#,
        clean: UNDEFINED,
    });
}

#[test]
fn modifier_error_with_function_mock() {
    run(&Case {
        name: "2 modifier/mock",
        trigger: r#"r = v { v := input.a with count as 42 with input.b as (1 / input.d) }"#,
        probe: PROBE_MOCK,
        request1: r#"{"d":0}"#,
        request2: r#"{"d":1}"#,
        clean: "2",
    });
}

#[test]
fn loop_expression_error_with_data() {
    run(&Case {
        name: "3 loop/data",
        trigger: r#"r = v { v := [1 / input.d][_] with data.leak as input.secret }"#,
        probe: PROBE_DATA,
        request1: r#"{"secret":"r1","d":0}"#,
        request2: r#"{"d":1}"#,
        clean: UNDEFINED,
    });
}

#[test]
fn loop_expression_error_with_function_mock() {
    run(&Case {
        name: "4 loop/mock",
        trigger: r#"r = v { v := [1 / input.d][_] with count as 42 }"#,
        probe: PROBE_MOCK,
        request1: r#"{"d":0}"#,
        request2: r#"{"d":1}"#,
        clean: "2",
    });
}

// Rego v1, data override and function mock in one policy. `r` and `r2` fail
// for request 1 only. Neither `leaked` nor `counted` has a `with` of its own,
// so both must ignore the overrides of the failed statements: `leaked` is
// "none" and `counted` is 2 for every request, on a new engine per request
// and on one reused engine.
const REUSED_ENGINE_POLICY: &str = r#"
package t

r := v if {
	v := [1 / input.d][_] with data.secret as input.secret
}

o[r]["k"] := 1 if false

default leaked := "none"

leaked := v if {
	_ = [k | o[k]]
	v := data.secret with input.z as 1
}

r2 := v if {
	v := [1 / input.d][_] with count as 42
}

o2[r2]["k"] := 1 if false

counted := n if {
	_ = [k | o2[k]]
	n := count([1, 2])
}
"#;

#[test]
fn reused_engine_matches_new_engine_per_request() {
    let new_engine = || {
        let mut engine = Engine::new();
        engine
            .add_policy(
                "reused_engine.rego".to_string(),
                REUSED_ENGINE_POLICY.to_string(),
            )
            .expect("policy should parse");
        engine
    };
    let request1 = r#"{"secret": "request-1-secret", "d": 0}"#;
    let request2 = r#"{"d": 1}"#;

    for (query, expected) in [("data.t.leaked", "\"none\""), ("data.t.counted", "2")] {
        let expected = Ok(expected.to_string());
        assert_eq!(
            eval(&mut new_engine(), request1, query),
            expected,
            "{query}: new engine, request 1"
        );
        assert_eq!(
            eval(&mut new_engine(), request2, query),
            expected,
            "{query}: new engine, request 2"
        );

        let mut engine = new_engine();
        assert_eq!(
            eval(&mut engine, request1, query),
            expected,
            "{query}: reused engine, request 1"
        );
        assert_eq!(
            eval(&mut engine, request2, query),
            expected,
            "{query}: reused engine, request 2"
        );
    }
}
