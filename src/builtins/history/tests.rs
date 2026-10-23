// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::unreachable, clippy::similar_names)]

use super::{HistoryError, HistoryMatchState};
use crate::utils::limits::ExecutionTimer;
use crate::value::Array;
use crate::{Rc, Value};
use alloc::{boxed::Box, string::ToString as _, vec, vec::Vec};
use serde_json::{json, Value as Json};

#[derive(Clone, Debug)]
enum Test {
    Bool(bool),
    Compare {
        unequal: bool,
        variable: bool,
        literal: i64,
    },
    And(Vec<Test>),
    Or(Vec<Test>),
}

#[derive(Clone, Debug)]
enum Regex {
    Empty,
    All,
    Epsilon,
    Test(Test),
    Union(Vec<Regex>),
    Concat(Vec<Regex>),
    Star(Box<Regex>),
    Intersect(Vec<Regex>),
    Not(Box<Regex>),
}

// Deliberately recursive, bounded test oracle: language membership enumerates
// splits rather than sharing any production derivative or normalization code.
fn test_matches(test: &Test, event: &Json, binding: i64) -> bool {
    match test {
        Test::Bool(value) => *value,
        Test::Compare {
            unequal,
            variable,
            literal,
        } => event.get("x").is_some_and(|value| {
            (value == &json!(if *variable { binding } else { *literal })) != *unequal
        }),
        Test::And(children) => children.iter().all(|t| test_matches(t, event, binding)),
        Test::Or(children) => children.iter().any(|t| test_matches(t, event, binding)),
    }
}

fn accepts(regex: &Regex, history: &[Json], binding: i64) -> bool {
    match regex {
        Regex::Empty => false,
        Regex::All => true,
        Regex::Epsilon => history.is_empty(),
        Regex::Test(test) => match history {
            [event] => test_matches(test, event, binding),
            _ => false,
        },
        Regex::Union(children) => children.iter().any(|r| accepts(r, history, binding)),
        Regex::Intersect(children) => children.iter().all(|r| accepts(r, history, binding)),
        Regex::Not(inner) => !accepts(inner, history, binding),
        Regex::Concat(factors) => accepts_concat(factors, history, binding),
        Regex::Star(inner) => {
            history.is_empty()
                || (1..=history.len()).any(|split| {
                    accepts(inner, &history[..split], binding)
                        && accepts(regex, &history[split..], binding)
                })
        }
    }
}

fn accepts_concat(factors: &[Regex], history: &[Json], binding: i64) -> bool {
    match factors {
        [] => history.is_empty(),
        [first, rest @ ..] => (0..=history.len()).any(|split| {
            accepts(first, &history[..split], binding)
                && accepts_concat(rest, &history[split..], binding)
        }),
    }
}

// Independent concrete derivative produces unnormalized source expressions.
fn derivative(regex: &Regex, event: &Json, binding: i64) -> Regex {
    match regex {
        Regex::Empty | Regex::Epsilon => Regex::Empty,
        Regex::All => Regex::All,
        Regex::Test(test) => {
            if test_matches(test, event, binding) {
                Regex::Epsilon
            } else {
                Regex::Empty
            }
        }
        Regex::Union(children) => Regex::Union(
            children
                .iter()
                .map(|r| derivative(r, event, binding))
                .collect(),
        ),
        Regex::Intersect(children) => Regex::Intersect(
            children
                .iter()
                .map(|r| derivative(r, event, binding))
                .collect(),
        ),
        Regex::Not(inner) => Regex::Not(Box::new(derivative(inner, event, binding))),
        Regex::Star(inner) => Regex::Concat(vec![derivative(inner, event, binding), regex.clone()]),
        Regex::Concat(children) => {
            let mut alternatives = Vec::new();
            for (index, child) in children.iter().enumerate() {
                let mut factors = vec![derivative(child, event, binding)];
                factors.extend_from_slice(&children[index + 1..]);
                alternatives.push(Regex::Concat(factors));
                if !accepts(child, &[], binding) {
                    break;
                }
            }
            Regex::Union(alternatives)
        }
    }
}

fn test_source(test: &Test) -> Json {
    match test {
        Test::Bool(value) => json!(value),
        Test::Compare {
            unequal,
            variable,
            literal,
        } => {
            let term = if *variable {
                json!({"var":"v"})
            } else {
                json!({"value":literal})
            };
            let payload = json!({"path":["x"],"term":term});
            if *unequal {
                json!({"neq":payload})
            } else {
                json!({"eq":payload})
            }
        }
        Test::And(children) => json!({"and":children.iter().map(test_source).collect::<Vec<_>>()}),
        Test::Or(children) => json!({"or":children.iter().map(test_source).collect::<Vec<_>>()}),
    }
}

fn regex_source(regex: &Regex) -> Json {
    match regex {
        Regex::Empty => json!({"empty":true}),
        Regex::All => json!({"all":true}),
        Regex::Epsilon => json!({"epsilon":true}),
        Regex::Test(test) => json!({"test":test_source(test)}),
        Regex::Union(children) => {
            json!({"union":children.iter().map(regex_source).collect::<Vec<_>>()})
        }
        Regex::Concat(children) => {
            json!({"concat":children.iter().map(regex_source).collect::<Vec<_>>()})
        }
        Regex::Star(inner) => json!({"star":regex_source(inner)}),
        Regex::Intersect(children) => {
            json!({"intersect":children.iter().map(regex_source).collect::<Vec<_>>()})
        }
        Regex::Not(inner) => json!({"not":regex_source(inner)}),
    }
}

fn value(json: &Json) -> Value {
    Value::from_json_str(&json.to_string()).expect("valid JSON value")
}
fn array(events: &[Json]) -> Rc<Array> {
    match value(&json!(events)) {
        Value::Array(array) => array,
        _ => unreachable!("array fixture"),
    }
}
fn policy(regex: &Regex) -> Value {
    value(&json!({"request":{"var":"v"},"history":regex_source(regex)}))
}
fn evaluate(
    state: &mut HistoryMatchState,
    policy: &Value,
    events: &Rc<Array>,
    binding: i64,
) -> bool {
    state
        .evaluate(
            policy,
            events,
            &Value::from(binding),
            &mut ExecutionTimer::new(None),
            &mut super::graph::ObservationWorld,
        )
        .expect("valid policy")
}

struct Generator(u64);
impl Generator {
    fn next(&mut self, upper: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from(self.0 >> 32).expect("32-bit generator sample") % upper
    }
    fn test(&mut self, depth: usize) -> Test {
        if depth > 0 {
            match self.next(4) {
                0 => return Test::And(vec![self.test(depth - 1), self.test(depth - 1)]),
                1 => return Test::Or(vec![self.test(depth - 1), self.test(depth - 1)]),
                _ => {}
            }
        }
        match self.next(6) {
            0 => Test::Bool(true),
            1 => Test::Bool(false),
            n => Test::Compare {
                unequal: n % 2 == 0,
                variable: n >= 4,
                literal: 1,
            },
        }
    }
    fn regex(&mut self, depth: usize) -> Regex {
        if depth == 0 {
            return match self.next(5) {
                0 => Regex::Empty,
                1 => Regex::All,
                2 => Regex::Epsilon,
                _ => Regex::Test(self.test(1)),
            };
        }
        match self.next(9) {
            0 => Regex::Empty,
            1 => Regex::All,
            2 => Regex::Epsilon,
            3 => Regex::Test(self.test(1)),
            4 => Regex::Union(vec![self.regex(depth - 1), self.regex(depth - 1)]),
            5 => Regex::Concat(vec![self.regex(depth - 1), self.regex(depth - 1)]),
            6 => Regex::Star(Box::new(self.regex(depth - 1))),
            7 => Regex::Intersect(vec![self.regex(depth - 1), self.regex(depth - 1)]),
            _ => Regex::Not(Box::new(self.regex(depth - 1))),
        }
    }
}

fn histories() -> Vec<Vec<Json>> {
    let alphabet = [json!({"x":1}), json!({"x":2}), json!({})];
    let mut all = vec![vec![]];
    let mut layer = vec![vec![]];
    for _ in 0..3 {
        let mut next = Vec::new();
        for prefix in &layer {
            for event in &alphabet {
                let mut word = prefix.clone();
                word.push(event.clone());
                next.push(word);
            }
        }
        all.extend(next.iter().cloned());
        layer = next;
    }
    all
}

#[test]
fn symbolic_matching_agrees_with_independent_membership_and_concrete_derivatives() {
    let atom = Test::Compare {
        unequal: false,
        variable: true,
        literal: 1,
    };
    let leaf = Regex::Test(atom);
    // Seed every constructor and empty connective; randomness cannot omit one.
    let mut corpus = vec![
        Regex::Empty,
        Regex::All,
        Regex::Epsilon,
        leaf.clone(),
        Regex::Union(vec![]),
        Regex::Concat(vec![]),
        Regex::Intersect(vec![]),
        Regex::Star(Box::new(leaf.clone())),
        Regex::Not(Box::new(leaf.clone())),
        Regex::Union(vec![leaf.clone(), Regex::Epsilon]),
        Regex::Concat(vec![leaf.clone(), leaf.clone()]),
        Regex::Intersect(vec![leaf.clone(), Regex::All]),
        Regex::Test(Test::And(vec![])),
        Regex::Test(Test::Or(vec![])),
    ];
    let mut generator = Generator(0x5eed_cafe_f00d_beef);
    corpus.extend((0..500).map(|_| generator.regex(2)));
    let words = histories();
    for regex in corpus {
        let policy = policy(&regex);
        let mut warm = HistoryMatchState::default();
        for binding in [1, 2] {
            for word in &words {
                let events = array(word);
                let expected = accepts(&regex, word, binding);
                assert_eq!(
                    evaluate(&mut HistoryMatchState::default(), &policy, &events, binding),
                    expected,
                    "cold {regex:?} {word:?} v={binding}"
                );
                assert_eq!(
                    evaluate(&mut warm, &policy, &events, binding),
                    expected,
                    "warm {regex:?} {word:?}"
                );
                assert_eq!(
                    evaluate(&mut warm, &policy, &events, binding),
                    expected,
                    "repeat {regex:?} {word:?}"
                );
                if let Some((first, tail)) = word.split_first() {
                    let concrete = derivative(&regex, first, binding);
                    assert_eq!(
                        accepts(&concrete, tail, binding),
                        expected,
                        "concrete derivative {regex:?}"
                    );
                    assert_eq!(
                        evaluate(
                            &mut HistoryMatchState::default(),
                            &self::policy(&concrete),
                            &array(tail),
                            binding
                        ),
                        expected,
                        "symbolic versus concrete derivative {regex:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn complete_language_cardinality_and_presence_guards() {
    let eq = Test::Compare {
        unequal: false,
        variable: false,
        literal: 1,
    };
    let neq = Test::Compare {
        unequal: true,
        variable: false,
        literal: 1,
    };
    let cases = [
        (Regex::Test(Test::Bool(true)), vec![false, true, false]),
        (
            Regex::Not(Box::new(Regex::Test(eq.clone()))),
            vec![true, false, true],
        ),
        (Regex::Test(eq.clone()), vec![false, true, false]),
        (Regex::Test(neq.clone()), vec![false, false, false]),
        (
            Regex::Test(Test::Or(vec![eq, neq.clone()])),
            vec![false, true, false],
        ),
    ];
    for (regex, expected) in cases {
        for (events, expected) in [
            vec![],
            vec![json!({"x":1})],
            vec![json!({"x":1}), json!({"x":1})],
        ]
        .iter()
        .zip(expected)
        {
            assert_eq!(
                evaluate(
                    &mut HistoryMatchState::default(),
                    &policy(&regex),
                    &array(events),
                    1
                ),
                expected
            );
        }
    }
    for test in [
        neq.clone(),
        Test::Or(vec![
            neq,
            Test::Compare {
                unequal: true,
                variable: false,
                literal: 2,
            },
        ]),
    ] {
        assert!(!evaluate(
            &mut HistoryMatchState::default(),
            &policy(&Regex::Test(test)),
            &array(&[json!({})]),
            1
        ));
    }
}

#[test]
fn all_source_children_are_validated_before_reduction_or_request_matching() {
    let invalid = [
        json!({"request":{"value":0},"history":{"union":[{"all":true},{"test":{"eq":{"path":[],"term":{"var":"missing"}}}}]}}),
        json!({"request":{"any":true},"history":{"concat":[{"empty":true},{"bogus":true}]}}),
        json!({"request":{"any":true},"history":{"all":true,"extra":true}}),
        json!({"request":{"any":false},"history":{"all":true}}),
        json!({"request":{"var":""},"history":{"all":true}}),
        json!({"request":{"any":true},"history":{"test":{"eq":{"path":[],"term":{"value":1},"extra":1}}}}),
    ];
    for source in invalid {
        let result = HistoryMatchState::default().evaluate(
            &value(&source),
            &array(&[]),
            &Value::from(99),
            &mut ExecutionTimer::new(None),
            &mut super::graph::ObservationWorld,
        );
        assert!(
            matches!(
                result,
                Err(HistoryError::InvalidPolicy { .. } | HistoryError::UnboundVariable { .. })
            ),
            "{source}: {result:?}"
        );
    }
}

#[test]
fn request_bindings_compare_complete_values_and_patterns_keep_shape() {
    let pattern =
        json!({"object":{"a":{"var":"same"},"b":{"array":[{"var":"same"},{"any":true}]} }});
    let p = value(&json!({"request":pattern,"history":{"epsilon":true}}));
    for (request, expected) in [
        (
            json!({"a":{"nested":[1,null]},"b":[{"nested":[1,null]},null],"extra":true}),
            true,
        ),
        (
            json!({"a":{"nested":[1,null]},"b":[{"nested":[1,0]},null]}),
            false,
        ),
        (json!({"a":1,"b":[1]}), false),
        (json!({"a":null,"b":[null,true]}), true),
        (json!({"b":[null,true]}), false),
    ] {
        assert_eq!(
            HistoryMatchState::default()
                .evaluate(
                    &p,
                    &array(&[]),
                    &value(&request),
                    &mut ExecutionTimer::new(None),
                    &mut super::graph::ObservationWorld,
                )
                .unwrap(),
            expected
        );
    }
    let p =
        value(&json!({"request":{"value":{"var":"operator-looking"}},"history":{"epsilon":true}}));
    assert!(HistoryMatchState::default()
        .evaluate(
            &p,
            &array(&[]),
            &value(&json!({"var":"operator-looking"})),
            &mut ExecutionTimer::new(None),
            &mut super::graph::ObservationWorld,
        )
        .unwrap());
}

#[test]
fn numeric_equivalence_preserves_symbolic_matching() {
    use crate::number::Number;
    use alloc::collections::{BTreeMap, BTreeSet};
    use num_bigint::BigInt;

    let object = |fields: Vec<(&str, Value)>| {
        Value::from(
            fields
                .into_iter()
                .map(|(k, v)| (Value::from(k), v))
                .collect::<BTreeMap<_, _>>(),
        )
    };
    let eq = |constant: Value| {
        object(vec![(
            "eq",
            object(vec![
                ("path", Value::from(vec![])),
                ("term", object(vec![("value", constant)])),
            ]),
        )])
    };
    let smaller = Value::Number(Number::UInt(9_007_199_254_740_995));
    let equal = Value::Number(Number::UInt(9_007_199_254_740_996));
    let big_equal = Value::Number(Number::BigInt(Rc::new(BigInt::from(
        9_007_199_254_740_996_u64,
    ))));
    let event = Value::Number(Number::Float(9_007_199_254_740_996.0));
    let unequal_test = eq(smaller);
    let equal_test = eq(equal);
    // The binary64 event is exactly this integer; JSON keeps the oracle's
    // arithmetic independent of Number comparison and graph normalization.
    let oracle_event = json!({"x":9_007_199_254_740_996_u64});
    let oracle_unequal = Test::Compare {
        unequal: false,
        variable: false,
        literal: 9_007_199_254_740_995,
    };
    let oracle_equal = Test::Compare {
        unequal: false,
        variable: false,
        literal: 9_007_199_254_740_996,
    };
    let mut state = HistoryMatchState::default();
    for ((test, expected), oracle) in [
        (unequal_test.clone(), false),
        (equal_test.clone(), true),
        (eq(big_equal), true),
        (
            object(vec![("and", Value::from(vec![unequal_test, equal_test]))]),
            false,
        ),
    ]
    .into_iter()
    .zip([
        oracle_unequal.clone(),
        oracle_equal.clone(),
        oracle_equal.clone(),
        Test::And(vec![oracle_unequal, oracle_equal]),
    ]) {
        assert_eq!(
            accepts(
                &Regex::Test(oracle),
                core::slice::from_ref(&oracle_event),
                0
            ),
            expected
        );
        let p = object(vec![
            ("request", value(&json!({"any":true}))),
            ("history", object(vec![("test", test)])),
        ]);
        let events = Rc::new(Array::from(vec![event.clone()]));
        assert_eq!(
            state
                .evaluate(
                    &p,
                    &events,
                    &Value::Null,
                    &mut ExecutionTimer::new(None),
                    &mut super::graph::ObservationWorld
                )
                .unwrap(),
            expected
        );
    }

    let zero = Value::Number(Number::Int(0));
    let negative_zero = Value::Number(Number::Float(-0.0));
    let p = value(&json!({
        "request":{"array":[{"var":"same"},{"var":"same"}]},
        "history":{"epsilon":true}
    }));
    for (left, right, expected) in [
        (zero.clone(), negative_zero.clone(), true),
        (
            Value::from(vec![zero, Value::from(1)]),
            Value::from(vec![negative_zero, Value::from(2)]),
            false,
        ),
    ] {
        assert_eq!(
            state
                .evaluate(
                    &p,
                    &array(&[]),
                    &Value::from(vec![left, right]),
                    &mut ExecutionTimer::new(None),
                    &mut super::graph::ObservationWorld,
                )
                .unwrap(),
            expected
        );
    }

    for equivalents in [vec![
        Value::Number(Number::Int(0)),
        Value::Number(Number::UInt(0)),
        Value::Number(Number::BigInt(Rc::new(BigInt::from(0)))),
        Value::Number(Number::Float(0.0)),
        Value::Number(Number::Float(-0.0)),
    ]] {
        let set = Value::from(equivalents.iter().cloned().collect::<BTreeSet<_>>());
        let mut keyed = Value::new_object();
        for key in &equivalents {
            keyed
                .as_object_mut()
                .unwrap()
                .insert(key.clone(), Value::Bool(true));
        }
        assert_eq!(set.as_set().unwrap().len(), 1);
        assert_eq!(keyed.as_object().unwrap().len(), 1);
        for key in equivalents {
            let p = object(vec![
                ("request", value(&json!({"any":true}))),
                (
                    "history",
                    object(vec![(
                        "test",
                        object(vec![(
                            "eq",
                            object(vec![
                                ("path", Value::from(vec![key])),
                                ("term", object(vec![("value", Value::Bool(true))])),
                            ]),
                        )]),
                    )]),
                ),
            ]);
            let events = Rc::new(Array::from(vec![keyed.clone()]));
            assert!(state
                .evaluate(
                    &p,
                    &events,
                    &Value::Null,
                    &mut ExecutionTimer::new(None),
                    &mut super::graph::ObservationWorld
                )
                .unwrap());
        }
    }
}

#[test]
fn null_missing_and_array_path_boundaries_are_not_conflated() {
    let tests = [
        (
            json!({"eq":{"path":["x"],"term":{"value":null}}}),
            json!({"x":null}),
            true,
        ),
        (
            json!({"eq":{"path":["x"],"term":{"value":null}}}),
            json!({}),
            false,
        ),
        (
            json!({"neq":{"path":["x"],"term":{"value":null}}}),
            json!({}),
            false,
        ),
        (
            json!({"eq":{"path":[0],"term":{"value":7}}}),
            json!([7]),
            true,
        ),
        (
            json!({"neq":{"path":[-1],"term":{"value":7}}}),
            json!([7]),
            false,
        ),
        (
            json!({"neq":{"path":[0.5],"term":{"value":7}}}),
            json!([7]),
            false,
        ),
        (
            json!({"neq":{"path":["0"],"term":{"value":7}}}),
            json!([7]),
            false,
        ),
        (
            json!({"neq":{"path":[u64::MAX],"term":{"value":7}}}),
            json!([7]),
            false,
        ),
        (
            json!({"eq":{"path":[],"term":{"value":{"x":1}}}}),
            json!({"x":1}),
            true,
        ),
    ];
    for (test, event, expected) in tests {
        let p = value(&json!({"request":{"any":true},"history":{"test":test}}));
        assert_eq!(
            HistoryMatchState::default()
                .evaluate(
                    &p,
                    &array(&[event]),
                    &Value::Null,
                    &mut ExecutionTimer::new(None),
                    &mut super::graph::ObservationWorld,
                )
                .unwrap(),
            expected
        );
    }
}

#[test]
fn float_path_steps_index_arrays_exactly() {
    use crate::number::Number;
    use alloc::collections::BTreeMap;

    let object = |fields: Vec<(&str, Value)>| {
        Value::from(
            fields
                .into_iter()
                .map(|(k, v)| (Value::from(k), v))
                .collect::<BTreeMap<_, _>>(),
        )
    };
    let float = |f: f64| Value::Number(Number::Float(f));
    let events = array(&[json!([7, 8])]);
    for (key, expected) in [
        (float(1.0), Some(8)),
        (float(0.0), Some(7)),
        (float(-0.0), Some(7)),
        (float(1.5), None),
        (float(-1.0), None),
        (float(f64::MIN_POSITIVE), None),
        (float(5e-324), None),
        (float(18446744073709551616.0), None),
        (float(1e300), None),
    ] {
        let defined = object(vec![(
            "neq",
            object(vec![
                ("path", Value::from(vec![key.clone()])),
                ("term", value(&json!({"value": null}))),
            ]),
        )]);
        let p = object(vec![
            ("request", value(&json!({"any":true}))),
            ("history", object(vec![("test", defined)])),
        ]);
        let selected = HistoryMatchState::default()
            .evaluate(
                &p,
                &events,
                &Value::Null,
                &mut ExecutionTimer::new(None),
                &mut super::graph::ObservationWorld,
            )
            .unwrap();
        assert_eq!(selected, expected.is_some(), "{key:?}");
        if let Some(element) = expected {
            let p = object(vec![
                ("request", value(&json!({"any":true}))),
                (
                    "history",
                    object(vec![(
                        "test",
                        object(vec![(
                            "eq",
                            object(vec![
                                ("path", Value::from(vec![key])),
                                ("term", value(&json!({ "value": element }))),
                            ]),
                        )]),
                    )]),
                ),
            ]);
            assert!(HistoryMatchState::default()
                .evaluate(
                    &p,
                    &events,
                    &Value::Null,
                    &mut ExecutionTimer::new(None),
                    &mut super::graph::ObservationWorld,
                )
                .unwrap());
        }
    }
}

#[test]
fn active_timer_expires_inside_compilation_and_prepared_replay() {
    use crate::tests::interpreter::timer_test_support::{configure_time_source, reset_time_source};
    use crate::utils::limits::{acquire_limits_test_lock, ExecutionTimerConfig, LimitError};
    use core::{num::NonZeroU32, time::Duration};

    let _guard = acquire_limits_test_lock();
    configure_time_source(None);
    let timed = || {
        reset_time_source();
        let mut timer = ExecutionTimer::new(Some(ExecutionTimerConfig {
            limit: Duration::from_millis(1),
            check_interval: NonZeroU32::MIN,
        }));
        timer.start(
            super::graph::ObservationWorld
                .now()
                .expect("configured test clock"),
        );
        timer
    };
    let regex = Regex::Star(Box::new(Regex::Test(Test::Compare {
        unequal: false,
        variable: true,
        literal: 1,
    })));
    let p = policy(&regex);
    let events = array(&vec![json!({"x":1}); 32]);
    let mut timer = timed();
    assert!(matches!(
        HistoryMatchState::default().evaluate(
            &p,
            &events,
            &Value::from(1),
            &mut timer,
            &mut super::graph::ObservationWorld
        ),
        Err(HistoryError::Limit(LimitError::TimeLimitExceeded { .. }))
    ));

    let mut prepared = super::source::compile_pair(
        &p,
        &mut ExecutionTimer::new(None),
        &mut super::graph::ObservationWorld,
    )
    .unwrap();
    let mut timer = timed();
    assert!(matches!(
        prepared.replay(
            &events,
            &[Value::from(1)],
            &mut timer,
            &mut super::graph::ObservationWorld
        ),
        Err(HistoryError::Limit(LimitError::TimeLimitExceeded { .. }))
    ));
    assert!(prepared
        .replay(
            &events,
            &[Value::from(1)],
            &mut ExecutionTimer::new(None),
            &mut super::graph::ObservationWorld
        )
        .unwrap());
    prepared.release();
    reset_time_source();
}

#[test]
fn ordinary_value_keys_sets_and_undefined_required_fields() {
    use alloc::collections::{BTreeMap, BTreeSet};
    fn object(entries: impl IntoIterator<Item = (Value, Value)>) -> Value {
        Value::from(entries.into_iter().collect::<BTreeMap<_, _>>())
    }
    let variable = value(&json!({"var":"v"}));
    let fields = object([(Value::from(1), variable)]);
    let head = object([(Value::from("object"), fields)]);
    let tail = value(&json!({"test":{"eq":{"path":[1],"term":{"var":"v"}}}}));
    let p = object([
        (Value::from("request"), head),
        (Value::from("history"), tail),
    ]);
    let request = object([(Value::from(1), Value::Null)]);
    let events = match Value::from(vec![request.clone()]) {
        Value::Array(events) => events,
        _ => unreachable!(),
    };
    assert!(HistoryMatchState::default()
        .evaluate(
            &p,
            &events,
            &request,
            &mut ExecutionTimer::new(None),
            &mut super::graph::ObservationWorld
        )
        .unwrap());

    let set = Value::from([Value::from(1)].into_iter().collect::<BTreeSet<_>>());
    let events = match Value::from(vec![set]) {
        Value::Array(events) => events,
        _ => unreachable!(),
    };
    let p = value(
        &json!({"request":{"any":true},"history":{"test":{"eq":{"path":[1],"term":{"value":1}}}}}),
    );
    assert!(HistoryMatchState::default()
        .evaluate(
            &p,
            &events,
            &Value::Null,
            &mut ExecutionTimer::new(None),
            &mut super::graph::ObservationWorld
        )
        .unwrap());

    for pattern in [json!({"any":true}), json!({"var":"v"})] {
        let p = value(&json!({"request":{"object":{"required":pattern}},"history":{"all":true}}));
        let request = object([(Value::from("required"), Value::Undefined)]);
        assert!(!HistoryMatchState::default()
            .evaluate(
                &p,
                &array(&[]),
                &request,
                &mut ExecutionTimer::new(None),
                &mut super::graph::ObservationWorld
            )
            .unwrap());
    }
    let p = value(
        &json!({"request":{"any":true},"history":{"test":{"neq":{"path":["x"],"term":{"value":1}}}}}),
    );
    let event = object([(Value::from("x"), Value::Undefined)]);
    let events = match Value::from(vec![event]) {
        Value::Array(events) => events,
        _ => unreachable!(),
    };
    assert!(!HistoryMatchState::default()
        .evaluate(
            &p,
            &events,
            &Value::Null,
            &mut ExecutionTimer::new(None),
            &mut super::graph::ObservationWorld
        )
        .unwrap());
}

#[test]
fn primitive_carriers_and_truth_words_are_validated_without_default_false() {
    use super::graph::RuntimeKernel;
    use super::kernel::{
        atom_set, KernelStore as _, PathId, Primitive, Term, TestView, VariableId,
    };
    use super::normalize::{nullable, regex_test, test_and};
    use super::symbolic::{interpret_transition, symbolic_derivative};
    let p = policy(&Regex::Test(Test::Compare {
        unequal: false,
        variable: true,
        literal: 1,
    }));
    let mut timer = ExecutionTimer::new(None);
    let mut pair =
        super::source::compile_pair(&p, &mut timer, &mut super::graph::ObservationWorld).unwrap();
    let mut store = RuntimeKernel {
        store: &mut pair.store,
        timer: &mut timer,
        world: &mut super::graph::ObservationWorld,
    };
    let has = store
        .intern_test(TestView::Atom {
            primitive: Primitive::HasValue(PathId(0)),
            positive: true,
        })
        .unwrap();
    let eq = store
        .intern_test(TestView::Atom {
            primitive: Primitive::EqCore(PathId(0), Term::Variable(VariableId(0))),
            positive: true,
        })
        .unwrap();
    let signed = store
        .intern_test(TestView::Atom {
            primitive: Primitive::HasValue(PathId(0)),
            positive: false,
        })
        .unwrap();
    let guarded = test_and(&mut store, &[has, eq]).unwrap();
    let regex = regex_test(&mut store, guarded).unwrap();
    let transition = symbolic_derivative(&mut store, &mut pair.derivatives, regex).unwrap();
    let mut ids = vec![has, eq];
    ids.sort_unstable();
    let atoms = atom_set(&mut store, ids.clone()).unwrap();
    let success = interpret_transition(&mut store, transition, &atoms, &[0b11]).unwrap();
    let missing = interpret_transition(&mut store, transition, &atoms, &[0b00]).unwrap();
    assert!(nullable(&store, success).unwrap());
    assert!(!nullable(&store, missing).unwrap());
    for words in [vec![], vec![0, 0], vec![0b100]] {
        assert!(matches!(
            interpret_transition(&mut store, transition, &atoms, &words),
            Err(HistoryError::Invariant {
                message: "invalid truth assignment"
            })
        ));
    }
    let empty_atoms = atom_set(&mut store, vec![]).unwrap();
    assert!(matches!(
        interpret_transition(&mut store, transition, &empty_atoms, &[]),
        Err(HistoryError::Invariant {
            message: "transition primitive missing from atom set"
        })
    ));
    for invalid in [
        vec![has, has],
        vec![signed],
        vec![store.constants().test_true],
        vec![super::kernel::TestId(u32::MAX)],
    ] {
        assert!(matches!(
            atom_set(&mut store, invalid),
            Err(HistoryError::Invariant {
                message: "invalid primitive atom set"
            })
        ));
    }
    ids.reverse();
    assert!(matches!(
        atom_set(&mut store, ids),
        Err(HistoryError::Invariant {
            message: "invalid primitive atom set"
        })
    ));
    pair.release();
}

#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
#[test]
fn pairs_release_their_chunks() {
    use crate::utils::limits::current_thread_live_bytes;

    let p = policy(&Regex::Test(Test::Compare {
        unequal: false,
        variable: true,
        literal: 1,
    }));
    let events = array(&[json!({"x":1})]);
    let before = current_thread_live_bytes();
    for _ in 0..200 {
        let mut state = HistoryMatchState::default();
        assert!(evaluate(&mut state, &p, &events, 1));
        state.release();
    }
    let growth = current_thread_live_bytes().saturating_sub(before);
    assert!(
        growth < 64 * 1024,
        "explicit release retained {growth} bytes"
    );

    let before = current_thread_live_bytes();
    for _ in 0..200 {
        let mut state = HistoryMatchState::default();
        assert!(evaluate(&mut state, &p, &events, 1));
    }
    let growth = current_thread_live_bytes().saturating_sub(before);
    assert!(growth < 64 * 1024, "state drop retained {growth} bytes");
}

#[cfg(all(feature = "std", feature = "arc", feature = "cache"))]
#[test]
fn compiled_histories_survive_engine_thread_transfer() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<crate::Engine>();

    let mut engine = crate::Engine::new();
    engine
        .add_policy(
            "thread.rego".to_string(),
            r#"package history_thread
import rego.v1
result := history.match({"request":{"var":"v"},"history":{"star":{"test":{"eq":{"path":["x"],"term":{"var":"v"}}}}}}, input.history, input.request)
"#
            .to_string(),
        )
        .unwrap();
    engine.set_input(value(&json!({"history":[{"x":1}],"request":1})));
    assert_eq!(
        engine
            .eval_rule("data.history_thread.result".to_string())
            .unwrap(),
        Value::Bool(true)
    );
    let result = std::thread::spawn(move || {
        engine.set_input(value(&json!({"history":[{"x":1},{"x":2}],"request":1})));
        engine
            .eval_rule("data.history_thread.result".to_string())
            .unwrap()
    })
    .join()
    .unwrap();
    assert_eq!(result, Value::Bool(false));
}
