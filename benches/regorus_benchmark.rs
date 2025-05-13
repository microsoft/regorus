use std::hint::black_box;

use regorus::Engine;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use serde_json::json;

fn engine_with_policy(policy: &str) -> Engine {
    let mut engine = Engine::new();
    engine
        .add_policy("policy.rego".to_string(), policy.to_string())
        .unwrap();
    engine
}

fn eval_principal(engine: &mut Engine) {
    engine.set_input(black_box(json!({"principal": "admin"}).into()));
    let result = engine
        .eval_rule(black_box("data.bench.allow".to_string()))
        .unwrap();
    assert_eq!(result, true.into());
}

fn allow_with_simple_equality(c: &mut Criterion) {
    c.bench_function("simple equality check with constant", |b| {
        let mut engine = engine_with_policy(
            r#"
            package bench
            allow if input.principal == "admin"
            "#,
        );

        b.iter(|| eval_principal(&mut engine))
    });

    c.bench_function("simple equality check with data", |b| {
        let mut engine = engine_with_policy(
            r#"
            package bench
            allow if input.principal == data.allowed_principal
            "#,
        );
        engine
            .add_data(json!({"allowed_principal": "admin"}).into())
            .unwrap();

        b.iter(|| eval_principal(&mut engine))
    });
}

fn allow_with_simple_membership(c: &mut Criterion) {
    let generate_principals = |n: usize| {
        (0..n)
            .into_iter()
            .map(|i| i.to_string())
            .chain(std::iter::once("admin".to_string()))
            .collect::<Vec<_>>()
    };

    let mut group = c.benchmark_group("allow with simple membership");
    for size in [32, 64, 128, 512, 1024, 2048].iter() {
        group.bench_with_input(BenchmarkId::new("with constant", size), size, |b, &size| {
            let principals = generate_principals(size).join("\",\"");
            let mut engine = engine_with_policy(&format!(
                r#"
                package bench

                allowed_principals := {{
                    "{principals}"
                }}

                allow if input.principal in allowed_principals
                "#
            ));

            b.iter(|| eval_principal(&mut engine))
        });

        group.bench_with_input(BenchmarkId::new("with data", size), size, |b, &size| {
            let principals = generate_principals(size);
            let mut engine = engine_with_policy(&format!(
                r#"
                package bench
                allow if input.principal in data.allowed_principals
                "#
            ));
            engine
                .add_data(json!({"allowed_principals": principals}).into())
                .unwrap();

            b.iter(|| eval_principal(&mut engine))
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    allow_with_simple_equality,
    allow_with_simple_membership
);
criterion_main!(benches);
