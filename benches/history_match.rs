// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Timed scopes include Engine input assignment and rule evaluation, not Rego
//! preparation. Extension setup/warming is excluded except in the explicit COW
//! benchmark. `cache` enables cross-call pair/progress retention.

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use regorus::{Engine, Value};
use serde_json::json;
use std::{collections::BTreeMap, hint::black_box};

const RULE: &str = "data.history_bench.result";
const SOURCE: &str = r#"
package history_bench
import rego.v1
result := history.match(data.pair, input.history, input.request)
"#;

fn request(resource: &str) -> Value {
    json!({"resource":resource}).into()
}

fn event(resource: &str, metadata: usize) -> Value {
    json!({"resource":resource,"unused":metadata}).into()
}

fn input(history: Value, request: Value) -> Value {
    Value::from(BTreeMap::from([
        (Value::from("history"), history),
        (Value::from("request"), request),
    ]))
}

fn evaluate(engine: &mut Engine, input: &Value, expected: bool) {
    engine.set_input(black_box(input.clone()));
    let actual = engine.eval_rule(black_box(RULE.to_string())).unwrap();
    assert_eq!(black_box(actual), Value::Bool(expected));
}

fn prepared_template(baseline: &Value) -> Engine {
    let mut engine = Engine::new();
    engine
        .add_policy("history_bench.rego".to_string(), SOURCE.to_string())
        .unwrap();
    engine
        .add_data(
            json!({"pair": {
                "request":{"object":{"resource":{"var":"r"}}},
                "history":{"star":{"test":{"eq":{"path":["resource"],"term":{"var":"r"}}}}}
            }})
            .into(),
        )
        .unwrap();
    // Clones share the prepared Rego policy, but start with empty matcher state.
    evaluate(&mut engine, baseline, true);
    engine
}

fn warm(template: &Engine, baseline: &Value) -> Engine {
    let mut engine = template.clone();
    evaluate(&mut engine, baseline, true);
    engine
}

fn history_match(c: &mut Criterion) {
    let mut group = c.benchmark_group("history_match");
    for length in [16, 256, 4096] {
        let history = Value::from((0..length).map(|i| event("a", i)).collect::<Vec<_>>());
        let baseline = input(history.clone(), request("a"));
        let template = prepared_template(&baseline);
        group.bench_with_input(
            BenchmarkId::new("cold_first_evaluation", length),
            &length,
            |b, _| {
                b.iter_batched_ref(
                    || template.clone(),
                    |engine| evaluate(engine, &baseline, true),
                    BatchSize::SmallInput,
                );
            },
        );
        group.bench_with_input(
            BenchmarkId::new("same_array_warm", length),
            &length,
            |b, _| {
                let mut engine = warm(&template, &baseline);
                b.iter(|| evaluate(&mut engine, &baseline, true));
            },
        );
        group.bench_with_input(
            BenchmarkId::new("reconstructed_prefix_validation", length),
            &length,
            |b, _| {
                b.iter_batched_ref(
                    || {
                        let engine = warm(&template, &baseline);
                        let reconstructed =
                            Value::from((0..length).map(|i| event("a", i)).collect::<Vec<_>>());
                        (engine, input(reconstructed, request("a")))
                    },
                    |(engine, new_input)| evaluate(engine, new_input, true),
                    BatchSize::SmallInput,
                );
            },
        );
        for (label, resource, expected) in [
            ("appended_relevant", "b", false),
            ("appended_self_loop", "a", true),
        ] {
            let appended_event = event(resource, length);
            group.bench_with_input(BenchmarkId::new(label, length), &length, |b, _| {
                b.iter_batched_ref(
                    || {
                        let engine = warm(&template, &baseline);
                        let mut extended = history.clone();
                        extended
                            .as_array_mut()
                            .unwrap()
                            .push(appended_event.clone());
                        (engine, input(extended, request("a")))
                    },
                    |(engine, new_input)| evaluate(engine, new_input, expected),
                    BatchSize::SmallInput,
                );
            });
        }
        let appended_event = event("a", length);
        let bound_request = request("a");
        group.bench_with_input(
            BenchmarkId::new("caller_cow_append_and_evaluation", length),
            &length,
            |b, _| {
                b.iter_batched_ref(
                    || (warm(&template, &baseline), history.clone()),
                    |(engine, extended)| {
                        extended
                            .as_array_mut()
                            .unwrap()
                            .push(appended_event.clone());
                        let new_input = input(extended.clone(), bound_request.clone());
                        evaluate(engine, &new_input, true);
                    },
                    BatchSize::SmallInput,
                );
            },
        );
        group.bench_with_input(
            BenchmarkId::new("alternating_bindings_one_snapshot", length),
            &length,
            |b, _| {
                let other = input(history.clone(), request("b"));
                let mut engine = warm(&template, &baseline);
                evaluate(&mut engine, &other, false);
                let mut binding_a = false;
                b.iter(|| {
                    binding_a = !binding_a;
                    evaluate(
                        &mut engine,
                        if binding_a { &baseline } else { &other },
                        binding_a,
                    );
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, history_match);
criterion_main!(benches);
