// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(all(feature = "rvm", feature = "history"))]

use regorus::languages::history_table::{compile, HistoryTableError};
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, RegoVM, VmError};
use regorus::Value;
use serde_json::json;
use std::sync::Arc;

const ACTIONS: [&str; 4] = ["edit", "read", "release", "remove"];
const OWNED: [&str; 3] = ["edit", "release", "remove"];
const READ: [&str; 2] = ["read", "remove"];

/// (principal, action, resource)
type Event = (usize, &'static str, usize);

fn event(e: Event) -> Value {
    json!({"principal": format!("a{}", e.0), "action": e.1, "resource": format!("f{}", e.2)}).into()
}

fn lock_rule(action: &str, setter: &str, changes: &[&str]) -> serde_json::Value {
    let unchanged: Vec<_> = changes
        .iter()
        .map(|c| json!({"neq": {"path": ["action"], "term": {"value": c}}}))
        .collect();
    json!({
        "mode": "forbid",
        "request": {"object": {
            "principal": {"var": "p"},
            "action": {"value": action},
            "resource": {"var": "r"}
        }},
        "history": {"concat": [
            {"all": true},
            {"test": {"and": [
                {"eq": {"path": ["resource"], "term": {"var": "r"}}},
                {"eq": {"path": ["action"], "term": {"value": setter}}},
                {"neq": {"path": ["principal"], "term": {"var": "p"}}}
            ]}},
            {"star": {"test": {"or": [
                {"neq": {"path": ["resource"], "term": {"var": "r"}}},
                {"and": unchanged}
            ]}}}
        ]}
    })
}

fn lock_table() -> Arc<Program> {
    let table = json!({"rules": [
        lock_rule("edit", "edit", &OWNED),
        lock_rule("edit", "read", &READ),
        lock_rule("release", "edit", &OWNED),
        lock_rule("remove", "edit", &OWNED),
        lock_rule("remove", "read", &READ),
    ]});
    compile(&table.into()).expect("lock table compiles")
}

/// Index of the first violated lock rule, by brute force.
fn oracle(history: &[Event], c: Event) -> Option<usize> {
    let forbidden = |setter: &str, changes: &[&str]| {
        history.iter().enumerate().any(|(i, e)| {
            e.2 == c.2
                && e.1 == setter
                && e.0 != c.0
                && history[i + 1..]
                    .iter()
                    .all(|f| f.2 != c.2 || !changes.contains(&f.1))
        })
    };
    let rules: [(&str, &str, &[&str]); 5] = [
        ("edit", "edit", &OWNED),
        ("edit", "read", &READ),
        ("release", "edit", &OWNED),
        ("remove", "edit", &OWNED),
        ("remove", "read", &READ),
    ];
    rules
        .iter()
        .position(|&(action, setter, changes)| action == c.1 && forbidden(setter, changes))
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn event(&mut self) -> Event {
        (self.below(3), ACTIONS[self.below(4)], self.below(3))
    }
}

fn vm(program: &Arc<Program>) -> (RegoVM, usize) {
    let mut vm = RegoVM::new();
    vm.load_program(program.clone());
    vm.set_strict_builtin_errors(true);
    let hid = vm.history_new();
    (vm, hid)
}

fn decide(vm: &mut RegoVM, hid: usize, c: Event) -> Result<Value, VmError> {
    let mut input = Value::new_object();
    let fields = input.as_object_mut().unwrap();
    fields.insert(Value::from("history"), Value::from(hid));
    fields.insert(Value::from("request"), event(c));
    vm.set_input(input);
    vm.execute_entry_point_by_name("decide")
}

fn expected(v: Option<usize>) -> Value {
    v.map_or(Value::Null, Value::from)
}

fn cases(seed: u64, n: usize) -> Vec<(Vec<Event>, Event)> {
    let mut rng = Rng(seed);
    (0..n)
        .map(|_| {
            let len = rng.below(25);
            ((0..len).map(|_| rng.event()).collect(), rng.event())
        })
        .collect()
}

fn check_cases(
    program: &Arc<Program>,
    mode: ExecutionMode,
    cases: &[(Vec<Event>, Event)],
) -> usize {
    let (mut vm, hid) = vm(program);
    vm.set_execution_mode(mode);
    let mut denials = 0;
    for (history, c) in cases {
        vm.history_truncate(hid, 0).unwrap();
        vm.history_append(hid, history.iter().map(|&e| event(e)))
            .unwrap();
        let want = oracle(history, *c);
        denials += usize::from(want.is_some());
        assert_eq!(
            decide(&mut vm, hid, *c).unwrap(),
            expected(want),
            "{history:?} {c:?}"
        );
    }
    denials
}

#[test]
fn lock_table_matches_oracle() {
    let denials = check_cases(
        &lock_table(),
        ExecutionMode::RunToCompletion,
        &cases(7, 3000),
    );
    assert!(denials >= 50, "only {denials} denials");
}

#[test]
fn incremental_equals_scratch() {
    let program = lock_table();
    let (mut vm, hid) = vm(&program);
    let mut history: Vec<Event> = Vec::new();
    let mut rng = Rng(11);
    for _ in 0..500 {
        match rng.below(3) {
            0 => {
                let batch: Vec<Event> = (0..1 + rng.below(8)).map(|_| rng.event()).collect();
                vm.history_append(hid, batch.iter().map(|&e| event(e)))
                    .unwrap();
                history.extend(batch);
            }
            1 => {
                let len = rng.below(history.len() + 1);
                vm.history_truncate(hid, len).unwrap();
                history.truncate(len);
            }
            _ => {
                let c = rng.event();
                let got = decide(&mut vm, hid, c).unwrap();
                let (mut fresh, fresh_hid) = self::vm(&program);
                fresh
                    .history_append(fresh_hid, history.iter().map(|&e| event(e)))
                    .unwrap();
                assert_eq!(got, decide(&mut fresh, fresh_hid, c).unwrap());
                assert_eq!(got, expected(oracle(&history, c)));
            }
        }
        assert_eq!(vm.history_len(hid).unwrap(), history.len());
    }
}

#[test]
fn truncate_invalidates_cursor() {
    let (mut vm, hid) = vm(&lock_table());
    vm.history_append(hid, [event((1, "edit", 0))]).unwrap();
    assert_eq!(
        decide(&mut vm, hid, (0, "edit", 0)).unwrap(),
        Value::from(0usize)
    );
    vm.history_truncate(hid, 0).unwrap();
    assert_eq!(decide(&mut vm, hid, (0, "edit", 0)).unwrap(), Value::Null);
    vm.history_append(hid, [event((1, "edit", 0)), event((1, "release", 0))])
        .unwrap();
    assert_eq!(decide(&mut vm, hid, (0, "edit", 0)).unwrap(), Value::Null);
}

#[test]
fn require_mode() {
    let table = json!({"rules": [{
        "mode": "require",
        "request": {"object": {"action": {"value": "edit"}, "resource": {"var": "r"}}},
        "history": {"concat": [
            {"all": true},
            {"test": {"and": [
                {"eq": {"path": ["action"], "term": {"value": "read"}}},
                {"eq": {"path": ["resource"], "term": {"var": "r"}}}
            ]}},
            {"all": true}
        ]}
    }]});
    let (mut vm, hid) = vm(&compile(&table.into()).unwrap());
    assert_eq!(
        decide(&mut vm, hid, (0, "edit", 0)).unwrap(),
        Value::from(0usize)
    );
    // Not judged: the request pattern does not match.
    assert_eq!(decide(&mut vm, hid, (0, "read", 0)).unwrap(), Value::Null);
    vm.history_append(hid, [event((2, "read", 0))]).unwrap();
    assert_eq!(decide(&mut vm, hid, (0, "edit", 0)).unwrap(), Value::Null);
    assert_eq!(
        decide(&mut vm, hid, (0, "edit", 1)).unwrap(),
        Value::from(0usize)
    );
}

#[test]
fn undefined_request_propagates() {
    let (mut vm, hid) = vm(&lock_table());
    vm.set_input(json!({"history": hid}).into());
    assert_eq!(
        vm.execute_entry_point_by_name("decide").unwrap(),
        Value::Undefined
    );
}

#[test]
fn invalid_handle_errors() {
    let (mut vm, _) = vm(&lock_table());
    vm.set_input(json!({"history": 99, "request": {"action": "edit"}}).into());
    assert!(matches!(
        vm.execute_entry_point_by_name("decide"),
        Err(VmError::InvalidHistoryHandle { .. })
    ));
    assert!(matches!(
        vm.history_append(99, []),
        Err(VmError::InvalidHistoryHandle { .. })
    ));
    assert!(matches!(
        vm.history_append(0, [Value::Undefined]),
        Err(VmError::InvalidHistoryEvent { .. })
    ));
    assert_eq!(vm.history_len(0).unwrap(), 0);
}

#[test]
fn binary_round_trip() {
    let program = lock_table();
    let bytes = program.serialize_binary().unwrap();
    let DeserializationResult::Complete(mut restored) =
        Program::deserialize_binary(&bytes).unwrap()
    else {
        panic!("partial deserialization");
    };
    restored.initialize_resolved_builtins().unwrap();
    check_cases(
        &Arc::new(restored),
        ExecutionMode::RunToCompletion,
        &cases(13, 100),
    );
    let json = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
    check_cases(
        &Arc::new(json),
        ExecutionMode::RunToCompletion,
        &cases(17, 100),
    );
}

#[test]
fn both_execution_modes_agree() {
    check_cases(&lock_table(), ExecutionMode::Suspendable, &cases(13, 100));
}

#[test]
fn malformed_table_rejected_at_compile() {
    let bad = json!({"rules": [{"mode": "forbid", "request": {"object": {}}, "history": {"bogus": true}}]});
    assert!(matches!(
        compile(&bad.into()),
        Err(HistoryTableError::InvalidPair { index: 0, .. })
    ));
    let mode =
        json!({"rules": [{"mode": "deny", "request": {"any": true}, "history": {"all": true}}]});
    assert!(matches!(
        compile(&mode.into()),
        Err(HistoryTableError::BadMode { index: 0, .. })
    ));
    assert!(matches!(
        compile(&json!({}).into()),
        Err(HistoryTableError::MissingRules)
    ));
}
