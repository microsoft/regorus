// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use regorus::languages::history_table::{HistoryStore, ACTION, PRINCIPAL, RESOURCE};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::RegoVM;
use regorus::{Engine, Value};
use std::hint::black_box;
use std::sync::Arc;

fn history_table_case(c: &mut Criterion, name: &str, language: &str) {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "bench.rego".into(),
            format!(
                "package t\nimport rego.v1\n\
                 r0 := history.require({{\"action\": \"release\", \"principal\": p, \"resource\": r}}, {language})\n"
            ),
        )
        .unwrap();
    let policy = engine.compile_with_entrypoint(&"data.t.r0".into()).unwrap();
    let program = Compiler::compile_from_policy(&policy, &["data.t.r0"]).unwrap();
    let store = Arc::new(HistoryStore::new());
    let principal = store.intern(PRINCIPAL, "alice").unwrap();
    let resource = store.intern(RESOURCE, "document").unwrap();
    let edit = store.intern(ACTION, "edit").unwrap();
    let release = store.intern(ACTION, "release").unwrap();
    let event = store.event(&[principal, edit, resource]).unwrap();
    let request = store.event(&[principal, release, resource]).unwrap();
    let mut group = c.benchmark_group(name);
    for length in [16, 256, 4096] {
        let history = store.new_history().unwrap();
        let events = vec![event; length];
        store.append(&history, &events).unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.attach_history(store.clone()).unwrap();
        vm.set_history_input(history.clone(), request).unwrap();
        assert_eq!(
            vm.execute_entry_point_by_name("data.t.r0").unwrap(),
            Value::Bool(true)
        );
        group.bench_with_input(
            BenchmarkId::new("unchanged_prefix_warm", length),
            &length,
            |b, _| {
                b.iter(|| black_box(vm.execute_entry_point_by_name("data.t.r0").unwrap()));
            },
        );
        // Truncation invalidates the cursor; graph/successor caches remain warm.
        group.bench_with_input(
            BenchmarkId::new("invalidated_prefix_replay", length),
            &length,
            |b, _| {
                b.iter_batched(
                    || {
                        store.truncate(&history, 0).unwrap();
                        store.append(&history, &events).unwrap();
                    },
                    |()| black_box(vm.execute_entry_point_by_name("data.t.r0").unwrap()),
                    BatchSize::PerIteration,
                );
            },
        );
        let mut primer = RegoVM::new();
        primer.load_program(program.clone());
        primer.attach_history(store.clone()).unwrap();
        primer.set_history_input(history.clone(), request).unwrap();
        group.bench_with_input(
            BenchmarkId::new("append_one_warm", length),
            &length,
            |b, _| {
                b.iter_batched(
                    || {
                        store.truncate(&history, length).unwrap();
                        assert_eq!(
                            primer.execute_entry_point_by_name("data.t.r0").unwrap(),
                            Value::Bool(true),
                        );
                        store.append(&history, &[event]).unwrap();
                    },
                    |()| black_box(vm.execute_entry_point_by_name("data.t.r0").unwrap()),
                    BatchSize::PerIteration,
                );
            },
        );
    }
    group.finish();
}

fn history_table(c: &mut Criterion) {
    history_table_case(
        c,
        "history_table_batch_256",
        r#"[any, {principal == p, action == "edit", resource == r}, any]"#,
    );
    history_table_case(
        c,
        "history_table_full_scan_batch_256",
        r#"star({action == "edit"})"#,
    );
}

criterion_group!(benches, history_table);
criterion_main!(benches);
