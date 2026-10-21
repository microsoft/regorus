// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "history")]

use anyhow::Result;
use regorus::{Engine, Value};
use serde_json::{json, Value as Json};

#[cfg(feature = "rvm")]
use regorus::languages::rego::compiler::Compiler;
#[cfg(feature = "rvm")]
use regorus::rvm::program::{DeserializationResult, Program};
#[cfg(feature = "rvm")]
use regorus::rvm::vm::{ExecutionMode, RegoVM, VmError};
#[cfg(feature = "rvm")]
use std::sync::Arc;

const RESULT: &str = "data.history_cases.result";
const OUTPUT: &str = "data.history_cases.output";
const NESTED: &str = "data.history_cases.nested";
const NEGATED: &str = "data.history_cases.negated";
const SOURCE: &str = r#"
package history_cases
import rego.v1
result := history.match(input.policy, input.history, input.request)
output := answer if { history.match(input.policy, input.history, input.request, answer) }
helper(policy, events, request) := history.match(policy, events, request)
nested := helper(input.policy, input.history, input.request)
negated := true if { not helper(input.policy, input.history, input.request) }
"#;

fn engine(strict: bool) -> Result<Engine> {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(strict);
    engine.add_policy("history.rego".to_string(), SOURCE.to_string())?;
    engine.add_data_json(r#"{"unrelated":"base data"}"#)?;
    Ok(engine)
}

fn value(json: Json) -> Result<Value> {
    Value::from_json_str(&json.to_string())
}

fn input(regex: Json, pattern: Json, events: Json, request: Json) -> Result<Value> {
    value(json!({"policy":{"history":regex,"request":pattern},"history":events,"request":request}))
}

fn example_pair() -> Json {
    json!({
        "request":{"object":{
            "action":{"value":"release"},
            "resource":{"var":"r"}
        }},
        "history":{"concat":[
            {"all":true},
            {"test":{"and":[
                {"eq":{"path":["action"],"term":{"value":"edit"}}},
                {"eq":{"path":["resource"],"term":{"var":"r"}}}
            ]}},
            {"all":true}
        ]}
    })
}

fn example_input(events: Json, request: Json) -> Result<Value> {
    value(json!({"policy":example_pair(),"history":events,"request":request}))
}

struct Case {
    label: String,
    input: Value,
    expected: Value,
}

fn semantic_cases() -> Result<Vec<Case>> {
    let mut cases = Vec::new();
    let any = json!({"any":true});
    let read = json!({"test":{"eq":{"path":["action"],"term":{"value":"read"}}}});
    let edit = json!({"test":{"eq":{"path":["action"],"term":{"value":"edit"}}}});
    let eq = json!({"eq":{"path":["x"],"term":{"value":1}}});
    let neq = json!({"neq":{"path":["x"],"term":{"value":1}}});
    let mut add = |label: &str, regex: Json, events: Json, expected: bool| -> Result<()> {
        cases.push(Case {
            label: label.to_string(),
            input: input(regex, any.clone(), events, Json::Null)?,
            expected: Value::Bool(expected),
        });
        Ok(())
    };

    for (events, expected) in [
        (json!([]), false),
        (json!([{"action":"read"}]), true),
        (json!([{"action":"read"},{"action":"read"}]), false),
    ] {
        add("one-event test", read.clone(), events, expected)?;
    }
    for (events, expected) in [
        (json!([]), true),
        (json!([{"action":"edit"}]), true),
        (json!([{"action":"edit"},{"action":"edit"}]), true),
        (json!([{"action":"read"}]), false),
    ] {
        add(
            "whole-language complement",
            json!({"not":read}),
            events,
            expected,
        )?;
    }
    add(
        "complete history suffix",
        json!({"concat":[{"all":true},edit]}),
        json!([{"action":"edit"},{"action":"read"}]),
        false,
    )?;
    add(
        "contains history event",
        json!({"concat":[{"all":true},edit,{"all":true}]}),
        json!([{"action":"edit"},{"action":"read"}]),
        true,
    )?;
    for (events, expected) in [
        (json!([{"action":"edit"}]), true),
        (json!([{"action":"read"},{"action":"edit"}]), true),
        (json!([{"action":"read"},{"action":"read"}]), false),
    ] {
        add(
            "ordered star concat",
            json!({"concat":[{"star":read},edit]}),
            events,
            expected,
        )?;
    }
    for test in [eq.clone(), neq.clone(), json!({"or":[eq,neq]})] {
        add(
            "missing comparison remains false",
            json!({"test":test}),
            json!([{}]),
            false,
        )?;
    }
    add(
        "distinct constants preserve presence",
        json!({"test":{"or":[
            {"neq":{"path":["x"],"term":{"value":1}}},
            {"neq":{"path":["x"],"term":{"value":2}}}
        ]}}),
        json!([{}]),
        false,
    )?;
    for (op, events, expected) in [
        ("eq", json!([{"x":null}]), true),
        ("eq", json!([{}]), false),
        ("neq", json!([{}]), false),
        ("neq", json!([{"x":1}]), true),
    ] {
        add(
            "null versus missing",
            json!({"test":{(op):{"path":["x"],"term":{"value":null}}}}),
            events,
            expected,
        )?;
    }
    for (regex, empty, one) in [
        (json!({"empty":true}), false, false),
        (json!({"all":true}), true, true),
        (json!({"epsilon":true}), true, false),
        (json!({"union":[]}), false, false),
        (json!({"concat":[]}), true, false),
        (json!({"intersect":[]}), true, true),
        (json!({"star":{"empty":true}}), true, false),
        (json!({"test":{"and":[]}}), false, true),
        (json!({"test":{"or":[]}}), false, false),
        (json!({"test":true}), false, true),
        (json!({"test":false}), false, false),
    ] {
        add("empty algebra identity", regex.clone(), json!([]), empty)?;
        add("one-event algebra identity", regex, json!([{}]), one)?;
    }
    add(
        "test true is not all",
        json!({"test":true}),
        json!([{}, {}]),
        false,
    )?;
    for (events, expected) in [
        (json!([]), false),
        (json!([{}]), true),
        (json!([{}, {}]), true),
    ] {
        add(
            "sequential intersection retains nonnullable witness",
            json!({"intersect":[
                {"not":{"epsilon":true}},
                {"union":[{"not":{"epsilon":true}},{"test":true}]}
            ]}),
            events,
            expected,
        )?;
    }
    add(
        "intersection and complement",
        json!({"intersect":[{"not":read},{"test":true}]}),
        json!([{"action":"edit"}]),
        true,
    )?;
    add(
        "intersection excludes matching read",
        json!({"intersect":[{"not":read},{"test":true}]}),
        json!([{"action":"read"}]),
        false,
    )?;
    add(
        "event root path",
        json!({"test":{"eq":{"path":[],"term":{"value":{"nested":[null,1]}}}}}),
        json!([{"nested":[null,1]}]),
        true,
    )?;
    add(
        "nested array selection",
        json!({"test":{"eq":{"path":["items",1,"x"],"term":{"value":2}}}}),
        json!([{"items":[null,{"x":2}]}]),
        true,
    )?;
    for path in [
        json!(["items", -1]),
        json!(["items", 0.5]),
        json!(["items", "0"]),
        json!(["items", 99]),
        json!(["items", 0, "x"]),
    ] {
        add(
            "invalid traversal is missing",
            json!({"test":{"neq":{"path":path,"term":{"value":null}}}}),
            json!([{"items":[null]}]),
            false,
        )?;
    }
    for (events, request, expected) in [
        (json!([]), json!({"action":"release","resource":"a"}), false),
        (
            json!([{"action":"edit","resource":"a"}]),
            json!({"action":"release","resource":"a"}),
            true,
        ),
        (
            json!([{"action":"edit","resource":"a"},{"action":"read","resource":"other"}]),
            json!({"action":"release","resource":"a"}),
            true,
        ),
        (
            json!([{"action":"edit","resource":"b"}]),
            json!({"action":"release","resource":"a"}),
            false,
        ),
        (
            json!([{"action":"edit","resource":"a"}]),
            json!({"action":"edit","resource":"a"}),
            false,
        ),
        (
            json!([{"action":"edit","resource":"a"}]),
            json!({"action":"release"}),
            false,
        ),
        (json!([]), json!({"action":"edit","resource":"a"}), false),
    ] {
        cases.push(Case {
            label: "resource release example".to_string(),
            input: example_input(events, request)?,
            expected: Value::Bool(expected),
        });
    }
    for (pattern, request, expected) in [
        (json!({"value":{"var":"x"}}), json!({"var":"x"}), true),
        (json!({"value":{"var":"x"}}), json!({"var":"other"}), false),
        (
            json!({"object":{"a":{"var":"v"},"b":{"var":"v"}}}),
            json!({"a":{"x":[1,null]},"b":{"x":[1,null]},"extra":true}),
            true,
        ),
        (
            json!({"object":{"a":{"var":"v"},"b":{"var":"v"}}}),
            json!({"a":1,"b":2}),
            false,
        ),
        (json!({"object":{"a":{"any":true}}}), json!({}), false),
        (json!({"object":{"a":{"var":"v"}}}), json!({}), false),
        (
            json!({"object":{"a":{"any":true}}}),
            json!({"a":null}),
            true,
        ),
        (
            json!({"array":[{"var":"v"},{"var":"v"}]}),
            json!([null, null]),
            true,
        ),
        (
            json!({"array":[{"var":"v"},{"var":"v"}]}),
            json!([1, 2]),
            false,
        ),
        (json!({"array":[{"any":true}]}), json!([1, 2]), false),
        (json!({"array":[]}), json!([]), true),
        (json!({"object":{}}), json!([]), false),
    ] {
        cases.push(Case {
            label: "request pattern".to_string(),
            input: input(json!({"all":true}), pattern, json!([]), request)?,
            expected: Value::Bool(expected),
        });
    }
    for binding in [1, 2] {
        for (events, expected) in [
            (json!([{"x":1}]), binding == 1),
            (json!([{"x":2}]), binding == 2),
            (json!([{}]), false),
        ] {
            cases.push(Case {
                label: "request-bound event term".to_string(),
                input: input(
                    json!({"test":{"eq":{"path":["x"],"term":{"var":"v"}}}}),
                    json!({"var":"v"}),
                    events,
                    json!(binding),
                )?,
                expected: Value::Bool(expected),
            });
        }
    }
    for pattern in [json!({"any":true}), json!({"var":"v"})] {
        let mut request = Value::new_object();
        request
            .as_object_mut()?
            .insert(Value::from("x"), Value::Undefined);
        let mut candidate = input(
            json!({"all":true}),
            json!({"object":{"x":pattern}}),
            json!([]),
            Json::Null,
        )?;
        candidate
            .as_object_mut()?
            .insert(Value::from("request"), request);
        cases.push(Case {
            label: "undefined required field".to_string(),
            input: candidate,
            expected: Value::Bool(false),
        });
    }
    for op in ["eq", "neq"] {
        let mut event = Value::new_object();
        event
            .as_object_mut()?
            .insert(Value::from("x"), Value::Undefined);
        let mut events = Value::new_array();
        events.as_array_mut()?.push(event);
        let mut candidate = input(
            json!({"test":{(op):{"path":["x"],"term":{"value":null}}}}),
            json!({"any":true}),
            json!([]),
            Json::Null,
        )?;
        candidate
            .as_object_mut()?
            .insert(Value::from("history"), events);
        cases.push(Case {
            label: "undefined event field is missing".to_string(),
            input: candidate,
            expected: Value::Bool(false),
        });
    }
    let baseline = example_input(
        json!([{"action":"edit","resource":"a"}]),
        json!({"action":"release","resource":"a"}),
    )?;
    cases.push(Case {
        label: "shared baseline".to_string(),
        input: baseline.clone(),
        expected: Value::Bool(true),
    });
    let mut changed = baseline.clone();
    changed
        .as_object_mut()?
        .get_mut(&Value::from("history"))
        .ok_or_else(|| anyhow::anyhow!("missing history"))?
        .as_array_mut()?
        .get_mut(0)
        .ok_or_else(|| anyhow::anyhow!("missing event"))?
        .as_object_mut()?
        .insert(Value::from("resource"), Value::from("b"));
    cases.push(Case {
        label: "nested COW replacement".to_string(),
        input: changed,
        expected: Value::Bool(false),
    });
    cases.push(Case {
        label: "original snapshot remains unchanged".to_string(),
        input: baseline,
        expected: Value::Bool(true),
    });
    // Direct Values retain binary64 payloads and integers beyond JSON's exact range.
    let object = |fields: Vec<(&str, Value)>| {
        Value::from(
            fields
                .into_iter()
                .map(|(key, value)| (Value::from(key), value))
                .collect::<std::collections::BTreeMap<_, _>>(),
        )
    };
    let numeric_eq = |constant: Value| {
        object(vec![(
            "eq",
            object(vec![
                ("path", Value::from(vec![])),
                ("term", object(vec![("value", constant)])),
            ]),
        )])
    };
    for (label, constant, event, expected) in [
        (
            "rounded neighbor is unequal",
            Value::from(9_007_199_254_740_995_u64),
            Value::from(9_007_199_254_740_996.0_f64),
            false,
        ),
        (
            "exact mixed integer equality",
            Value::from(9_007_199_254_740_996_u64),
            Value::from(9_007_199_254_740_996.0_f64),
            true,
        ),
        (
            "big integer equals float at two to sixty four",
            Value::from(1_u128 << 64),
            Value::from(18_446_744_073_709_551_616.0_f64),
            true,
        ),
        (
            "big integer neighbor differs",
            Value::from((1_u128 << 64) + 1),
            Value::from(18_446_744_073_709_551_616.0_f64),
            false,
        ),
        (
            "unsigned maximum differs from rounded float",
            Value::from(u64::MAX),
            Value::from(18_446_744_073_709_551_616.0_f64),
            false,
        ),
        (
            "subnormal differs from zero",
            Value::from(0_u64),
            Value::from(5e-324_f64),
            false,
        ),
        (
            "signed zeros equal",
            Value::from(0_i64),
            Value::from(-0.0_f64),
            true,
        ),
    ] {
        cases.push(Case {
            label: label.to_string(),
            input: object(vec![
                (
                    "policy",
                    object(vec![
                        ("request", value(any.clone())?),
                        ("history", object(vec![("test", numeric_eq(constant))])),
                    ]),
                ),
                ("history", Value::from(vec![event])),
                ("request", Value::Null),
            ]),
            expected: Value::Bool(expected),
        });
    }
    let conjunction = object(vec![(
        "and",
        Value::from(vec![
            numeric_eq(Value::from(9_007_199_254_740_995_u64)),
            numeric_eq(Value::from(9_007_199_254_740_996_u64)),
        ]),
    )]);
    cases.push(Case {
        label: "distinct numeric constants remain exclusive".to_string(),
        input: object(vec![
            (
                "policy",
                object(vec![
                    ("request", value(any.clone())?),
                    ("history", object(vec![("test", conjunction)])),
                ]),
            ),
            (
                "history",
                Value::from(vec![Value::from(9_007_199_254_740_996.0_f64)]),
            ),
            ("request", Value::Null),
        ]),
        expected: Value::Bool(false),
    });
    let zero = Value::from(0_u64);
    let negative_zero = Value::from(-0.0_f64);
    let zero_set = Value::from(
        [
            Value::from(0_i64),
            Value::from(0_u64),
            Value::from(0.0_f64),
            Value::from(-0.0_f64),
        ]
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>(),
    );
    let mut zero_keys = Value::new_object();
    zero_keys
        .as_object_mut()?
        .insert(Value::from(0_u64), Value::Bool(false));
    zero_keys
        .as_object_mut()?
        .insert(Value::from(-0.0_f64), Value::Bool(true));
    let mut one_zero_key = Value::new_object();
    one_zero_key
        .as_object_mut()?
        .insert(Value::from(0_i64), Value::Bool(true));
    for (label, left, right, expected) in [
        (
            "repeated complete structure differs",
            Value::from(vec![zero, Value::from(1)]),
            Value::from(vec![negative_zero, Value::from(2)]),
            false,
        ),
        (
            "zero set elements coalesce",
            zero_set,
            Value::from(
                [Value::from(0_u64)]
                    .into_iter()
                    .collect::<std::collections::BTreeSet<_>>(),
            ),
            true,
        ),
        ("zero object keys coalesce", zero_keys, one_zero_key, true),
    ] {
        let mut candidate = input(
            json!({"epsilon":true}),
            json!({"array":[{"var":"same"},{"var":"same"}]}),
            json!([]),
            Json::Null,
        )?;
        candidate
            .as_object_mut()?
            .insert(Value::from("request"), Value::from(vec![left, right]));
        cases.push(Case {
            label: label.to_string(),
            input: candidate,
            expected: Value::Bool(expected),
        });
    }
    let mut undefined = input(json!({"all":true}), any, json!([]), Json::Null)?;
    undefined
        .as_object_mut()?
        .insert(Value::from("request"), Value::Undefined);
    cases.push(Case {
        label: "top-level undefined".to_string(),
        input: undefined,
        expected: Value::Undefined,
    });
    Ok(cases)
}

#[test]
fn complete_history_semantics_in_all_evaluators() -> Result<()> {
    let cases = semantic_cases()?;
    for strict in [false, true] {
        let mut retained = engine(strict)?;
        #[cfg(feature = "rvm")]
        let program = {
            let compiled = retained.compile_with_entrypoint(&RESULT.into())?;
            Compiler::compile_from_policy(&compiled, &[RESULT, OUTPUT, NESTED])
                .map_err(|error| anyhow::anyhow!("{error}"))?
        };
        // The program is compiled once, before any input in the table is evaluated.
        for case in &cases {
            let unchanged = case.input.clone();
            retained.set_input(case.input.clone());
            for entry in [RESULT, OUTPUT, NESTED] {
                for _ in 0..2 {
                    assert_eq!(
                        retained.eval_rule(entry.to_string())?,
                        case.expected,
                        "{} strict={strict} {entry}",
                        case.label
                    );
                }
                let mut fresh = engine(strict)?;
                fresh.set_input(case.input.clone());
                assert_eq!(
                    fresh.eval_rule(entry.to_string())?,
                    case.expected,
                    "fresh {} {entry}",
                    case.label
                );
            }
            assert_eq!(case.input, unchanged, "caller input was mutated");
        }
        #[cfg(feature = "rvm")]
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut retained_vm = RegoVM::new();
            retained_vm.load_program(program.clone());
            retained_vm
                .set_data(retained.get_data())
                .map_err(|error| anyhow::anyhow!("{error}"))?;
            retained_vm.set_execution_mode(mode);
            retained_vm.set_strict_builtin_errors(strict);
            for case in &cases {
                retained_vm.set_input(case.input.clone());
                for entry in [RESULT, OUTPUT, NESTED] {
                    for _ in 0..2 {
                        assert_eq!(
                            retained_vm
                                .execute_entry_point_by_name(entry)
                                .map_err(|error| anyhow::anyhow!("{error}"))?,
                            case.expected,
                            "{} strict={strict} {mode:?} {entry}",
                            case.label
                        );
                    }
                    let mut fresh = RegoVM::new();
                    fresh.load_program(program.clone());
                    fresh
                        .set_data(retained.get_data())
                        .map_err(|error| anyhow::anyhow!("{error}"))?;
                    fresh.set_execution_mode(mode);
                    fresh.set_strict_builtin_errors(strict);
                    fresh.set_input(case.input.clone());
                    assert_eq!(
                        fresh
                            .execute_entry_point_by_name(entry)
                            .map_err(|error| anyhow::anyhow!("{error}"))?,
                        case.expected,
                        "fresh {} {mode:?} {entry}",
                        case.label
                    );
                }
            }
        }
    }
    Ok(())
}

#[test]
fn malformed_inputs_follow_strictness_and_validate_discarded_branches() -> Result<()> {
    let mut invalid = Vec::new();
    for regex in [
        json!({"unknown":true}),
        json!({"all":false}),
        json!({"all":true,"empty":true}),
        json!({"union":{}}),
        json!({"test":{"eq":{"path":[],"term":{"var":"missing"}}}}),
        json!({"union":[{"all":true},{"test":{"eq":{"path":[],"term":{"var":"missing"}}}}]}),
        json!({"test":{"eq":{"path":"x","term":{"value":1}}}}),
        json!({"test":{"neq":{"path":[],"term":{"value":1},"extra":true}}}),
        json!({"test":{"not":true}}),
    ] {
        invalid.push(input(
            regex,
            json!({"value":"never matches"}),
            json!([]),
            Json::Null,
        )?);
    }
    for pattern in [
        json!({"var":""}),
        json!({"any":false}),
        json!({"array":{}}),
        json!({"object":[]}),
        json!({"value":1,"any":true}),
    ] {
        invalid.push(input(json!({"all":true}), pattern, json!([]), Json::Null)?);
    }
    invalid.push(value(
        json!({"policy":{"history":{"all":true}},"history":[],"request":null}),
    )?);
    invalid.push(value(json!({"policy":{"history":{"all":true},"request":{"any":true},"extra":1},"history":[],"request":null}))?);
    invalid.push(input(
        json!({"all":true}),
        json!({"any":true}),
        json!({}),
        Json::Null,
    )?);
    for strict in [false, true] {
        let mut retained = engine(strict)?;
        #[cfg(feature = "rvm")]
        let program = {
            let compiled = retained.compile_with_entrypoint(&RESULT.into())?;
            Compiler::compile_from_policy(&compiled, &[RESULT, NESTED, NEGATED])
                .map_err(|error| anyhow::anyhow!("{error}"))?
        };
        for input in &invalid {
            retained.set_input(input.clone());
            for entry in [RESULT, NESTED, NEGATED] {
                let result = retained.eval_rule(entry.to_string());
                if strict {
                    assert!(result.is_err(), "invalid policy accepted: {entry} {input}");
                } else {
                    let expected = if entry == NEGATED {
                        Value::Bool(true)
                    } else {
                        Value::Undefined
                    };
                    assert_eq!(result?, expected);
                }
            }
        }
        #[cfg(feature = "rvm")]
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_data(retained.get_data())
                .map_err(|error| anyhow::anyhow!("{error}"))?;
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(strict);
            for input in &invalid {
                vm.set_input(input.clone());
                for entry in [RESULT, NESTED, NEGATED] {
                    let result = vm.execute_entry_point_by_name(entry);
                    if strict {
                        assert!(matches!(result, Err(VmError::HistoryMatchValidationError { .. })), "invalid policy accepted or wrong error: {mode:?} {entry} {input}: {result:?}");
                    } else {
                        let expected = if entry == NEGATED {
                            Value::Bool(true)
                        } else {
                            Value::Undefined
                        };
                        assert_eq!(
                            result.map_err(|error| anyhow::anyhow!("{error}"))?,
                            expected
                        );
                    }
                }
            }
        }
    }
    Ok(())
}

#[test]
fn oversized_graph_is_fatal_through_helper_and_negation_and_recovers() -> Result<()> {
    let oversized = input(
        json!({"concat":vec![json!({"test":true});30_000]}),
        json!({"any":true}),
        json!([]),
        Json::Null,
    )?;
    let valid = example_input(
        json!([{"action":"edit","resource":"a"}]),
        json!({"action":"release","resource":"a"}),
    )?;
    for strict in [false, true] {
        let mut retained = engine(strict)?;
        #[cfg(feature = "rvm")]
        let program = {
            let compiled = retained.compile_with_entrypoint(&NESTED.into())?;
            Compiler::compile_from_policy(&compiled, &[RESULT, NESTED, NEGATED])
                .map_err(|error| anyhow::anyhow!("{error}"))?
        };
        for entry in [RESULT, NESTED, NEGATED] {
            retained.set_input(oversized.clone());
            let error = retained
                .eval_rule(entry.to_string())
                .expect_err("graph limit must be fatal");
            assert!(
                error
                    .to_string()
                    .contains("history.match symbolic graph payload exceeds"),
                "wrong error: {error}"
            );
            retained.set_input(valid.clone());
            assert_eq!(retained.eval_rule(RESULT.to_string())?, Value::Bool(true));
        }
        #[cfg(feature = "rvm")]
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_data(retained.get_data())
                .map_err(|error| anyhow::anyhow!("{error}"))?;
            vm.set_execution_mode(mode);
            vm.set_strict_builtin_errors(strict);
            for entry in [RESULT, NESTED, NEGATED] {
                vm.set_input(oversized.clone());
                let error = vm
                    .execute_entry_point_by_name(entry)
                    .expect_err("graph limit must be fatal");
                match error {
                    VmError::HistoryMatchFailure { message, pc } => {
                        assert!(message.contains("history.match symbolic graph payload exceeds"));
                        assert_ne!(pc, 0, "contextual failure must preserve its builtin PC");
                    }
                    other => panic!("wrong hard error: {other}"),
                }
                vm.set_input(valid.clone());
                assert_eq!(
                    vm.execute_entry_point_by_name(RESULT)
                        .map_err(|error| anyhow::anyhow!("{error}"))?,
                    Value::Bool(true),
                    "recovery {strict} {mode:?}"
                );
            }
        }
    }
    Ok(())
}

#[test]
fn interpreter_with_replacement_and_wrong_arity_keep_existing_behavior() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy("with.rego".to_string(), r#"
package replacement
import rego.v1
replacement(policy, events, request) := false
result := answer if {
    answer := history.match({"history":{"all":true},"request":{"any":true}}, [], null) with history.match as replacement
}
"#.to_string())?;
    assert_eq!(
        engine.eval_rule("data.replacement.result".to_string())?,
        Value::Bool(false)
    );
    for strict in [false, true] {
        engine.set_strict_builtin_errors(strict);
        for query in [
            "history.match({}, [])",
            "history.match({}, [], null, true, false)",
        ] {
            let result = engine.eval_query(query.to_string(), false);
            if strict {
                assert!(result.is_err());
            } else {
                assert!(result?.result.is_empty());
            }
        }
    }
    Ok(())
}

#[test]
fn policy_function_can_shadow_native_namespace() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "shadow_function.rego".to_string(),
        r#"
package shadow_functions
import rego.v1
match(policy, events, request) := "shadow"
"#
        .to_string(),
    )?;
    engine.add_policy(
        "shadow.rego".to_string(),
        r#"
package shadow_consumer
import rego.v1
import data.shadow_functions as history
result := history.match({}, [], null)
"#
        .to_string(),
    )?;
    let entry = "data.shadow_consumer.result";
    #[cfg(feature = "rvm")]
    let program = {
        let compiled = engine.compile_with_entrypoint(&entry.into())?;
        Compiler::compile_from_policy(&compiled, &[entry])
            .map_err(|error| anyhow::anyhow!("{error}"))?
    };
    for strict in [false, true] {
        engine.set_strict_builtin_errors(strict);
        assert_eq!(engine.eval_rule(entry.to_string())?, Value::from("shadow"));
    }
    #[cfg(feature = "rvm")]
    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_data(engine.get_data())
            .map_err(|error| anyhow::anyhow!("{error}"))?;
        vm.set_execution_mode(mode);
        for strict in [false, true] {
            vm.set_strict_builtin_errors(strict);
            assert_eq!(
                vm.execute_entry_point_by_name(entry)
                    .map_err(|error| anyhow::anyhow!("{error}"))?,
                Value::from("shadow")
            );
        }
    }
    Ok(())
}

#[cfg(feature = "rvm")]
#[test]
fn example_program_json_and_complete_binary_roundtrips() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "roundtrip.rego".to_string(),
        r#"
package roundtrip
import rego.v1
result := history.match(data.pair, input.history, input.request)
"#
        .to_string(),
    )?;
    engine.add_data(value(json!({"pair":example_pair()}))?)?;
    let entry = "data.roundtrip.result";
    let compiled = engine.compile_with_entrypoint(&entry.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[entry])
        .map_err(|error| anyhow::anyhow!("{error}"))?;
    let json_program =
        Program::deserialize_json(&program.serialize_json().map_err(anyhow::Error::msg)?)
            .map_err(anyhow::Error::msg)?;
    let binary_program =
        match Program::deserialize_binary(&program.serialize_binary().map_err(anyhow::Error::msg)?)
            .map_err(anyhow::Error::msg)?
        {
            DeserializationResult::Complete(program) => program,
            DeserializationResult::Partial(_) => {
                anyhow::bail!("history program unexpectedly requires recompilation")
            }
        };
    for program in [Arc::new(json_program), Arc::new(binary_program)] {
        for strict in [false, true] {
            engine.set_strict_builtin_errors(strict);
            for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_data(engine.get_data())
                    .map_err(|error| anyhow::anyhow!("{error}"))?;
                vm.set_strict_builtin_errors(strict);
                vm.set_execution_mode(mode);
                for (events, resource, expected) in [
                    (json!([]), "a", false),
                    (json!([{"action":"edit","resource":"a"}]), "a", true),
                    (
                        json!([{"action":"edit","resource":"a"},{"action":"read","resource":"other","trace":"noise"}]),
                        "a",
                        true,
                    ),
                    (json!([{"action":"edit","resource":"a"}]), "b", false),
                ] {
                    let input = value(
                        json!({"history":events,"request":{"action":"release","resource":resource}}),
                    )?;
                    let unchanged = input.clone();
                    engine.set_input(input.clone());
                    vm.set_input(input.clone());
                    assert_eq!(engine.eval_rule(entry.to_string())?, Value::Bool(expected));
                    assert_eq!(
                        vm.execute_entry_point_by_name(entry)
                            .map_err(|error| anyhow::anyhow!("{error}"))?,
                        Value::Bool(expected)
                    );
                    assert_eq!(input, unchanged);
                }
            }
        }
    }
    Ok(())
}
