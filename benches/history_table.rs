// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use criterion::{criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use regorus::languages::history_table::{compile, Event, HistoryStore};
use regorus::rvm::vm::RegoVM;
use regorus::Value;
use std::hint::black_box;
use std::sync::Arc;

fn history_table_case(c: &mut Criterion, name: &str, source: &str) {
    let source = Value::from_json_str(source).unwrap();
    let program = compile(&source, 256).unwrap();
    let store = Arc::new(HistoryStore::new());
    let principal = store.intern_principal("alice").unwrap();
    let resource = store.intern_resource("document").unwrap();
    let edit = store.intern_action("edit").unwrap();
    let release = store.intern_action("release").unwrap();
    let event = Event {
        principal,
        action: edit,
        resource,
    };
    let request = Event {
        principal,
        action: release,
        resource,
    };
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
            vm.execute_entry_point_by_name("decide").unwrap(),
            Value::Null
        );
        group.bench_with_input(
            BenchmarkId::new("unchanged_prefix_warm", length),
            &length,
            |b, _| {
                b.iter(|| black_box(vm.execute_entry_point_by_name("decide").unwrap()));
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
                    |()| black_box(vm.execute_entry_point_by_name("decide").unwrap()),
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
                            primer.execute_entry_point_by_name("decide").unwrap(),
                            Value::Null,
                        );
                        store.append(&history, &[event]).unwrap();
                    },
                    |()| black_box(vm.execute_entry_point_by_name("decide").unwrap()),
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
        r#"{"rules":[{"mode":"require","request":{"object":{"principal":{"var":"p"},"action":{"value":"release"},"resource":{"var":"r"}}},"history":{"concat":[{"all":true},{"test":{"and":[{"eq":{"path":["principal"],"term":{"var":"p"}}},{"eq":{"path":["action"],"term":{"value":"edit"}}},{"eq":{"path":["resource"],"term":{"var":"r"}}}]}},{"all":true}]}}]}"#,
    );
    history_table_case(
        c,
        "history_table_full_scan_batch_256",
        r#"{"rules":[{"mode":"require","request":{"object":{"principal":{"var":"p"},"action":{"value":"release"},"resource":{"var":"r"}}},"history":{"star":{"test":{"eq":{"path":["action"],"term":{"value":"edit"}}}}}}]}"#,
    );
}

criterion_group!(benches, history_table);
criterion_main!(benches);
