use std::hint::black_box;

use regorus::{Engine, Value};

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
            let mut engine = engine_with_policy(
                r#"
                package bench
                allow if input.principal in data.allowed_principals
                "#,
            );
            engine
                .add_data(json!({"allowed_principals": principals}).into())
                .unwrap();

            b.iter(|| eval_principal(&mut engine))
        });
    }
    group.finish();
}

fn clone(c: &mut Criterion) {
    // Use Arc<BtreeMap> as a reference. Clone will only increment
    // the reference count.
    let mut m = std::collections::BTreeMap::default();
    m.insert(1, 2);
    let m = std::sync::Arc::new(m);

    c.bench_function("clone: Arc<BTreeMap>", |b| {
        b.iter(|| {
            let _ = m.clone();
        })
    });

    let mut engine = Engine::new();
    engine.set_rego_v0(true);
    engine
        .add_policy_from_file("tests/aci/framework.rego")
        .unwrap();
    engine.add_policy_from_file("tests/aci/api.rego").unwrap();
    engine
        .add_policy_from_file("tests/aci/policy.rego")
        .unwrap();
    engine
        .add_data(Value::from_json_file("tests/aci/data.json").expect("failed to load data.json"))
        .expect("failed to add data");
    engine.set_input(
        Value::from_json_file("tests/aci/input.json").expect("failed to load input.json"),
    );

    // An engine without preparation will not have processed fields populated.
    c.bench_function("clone: engine with aci policies", |b| {
        b.iter(|| {
            let _ = engine.clone();
        })
    });

    // Trigger engine preparation.
    let _ = engine.eval_query("data.framework.mount_overlay".to_string(), false);

    // Prepared engine will have many more fields populated. But the fields are
    // immutable after preparation and will be shared between clones.
    c.bench_function("clone: prepared engine with aci policies", |b| {
        b.iter(|| {
            let _ = engine.clone();
        })
    });
}

fn aci_policy_eval(c: &mut Criterion) {
    let mut group = c.benchmark_group("ACI Policy Eval");
    let rules = ["data.policy.mount_overlay", "data.policy.mount_device"];
    for rule in rules {
        group.bench_with_input(BenchmarkId::new("rule", rule), &rule, |b, rule| {
            let mut engine = Engine::new();
            engine.set_rego_v0(true);

            engine
                .add_policy_from_file("tests/aci/api.rego")
                .expect("failed to add api.rego");
            engine
                .add_policy_from_file("tests/aci/framework.rego")
                .expect("failed to add framework.rego");
            engine
                .add_policy_from_file("tests/aci/policy.rego")
                .expect("failed to add policy.rego");
            engine
                .add_data(
                    Value::from_json_file("tests/aci/data.json").expect("failed to load data.json"),
                )
                .expect("failed to add data");
            let input =
                Value::from_json_file("tests/aci/input.json").expect("failed to load input.json");
            engine.set_input(input.clone());
            engine.eval_rule(rule.to_string()).unwrap();
            b.iter(|| {
                engine.eval_rule(rule.to_string()).unwrap();
            })
        });
    }
    group.finish();
}

criterion_group!(
    benches,
    allow_with_simple_equality,
    allow_with_simple_membership,
    clone,
    aci_policy_eval
);

criterion_main!(benches);
