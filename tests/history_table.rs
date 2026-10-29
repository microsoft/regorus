// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(all(feature = "rvm", feature = "history"))]

use history_semantics::CompiledRule;
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use regorus::languages::history_table::{
    compile, Event, HistoryError, HistoryHandle, HistoryStore, HistoryTableError,
};
use regorus::rvm::program::{DeserializationResult, Program};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
use regorus::rvm::Instruction;
use regorus::{Engine, Value};
use serde_json::{json, Value as Json};
use std::sync::Arc;

const MODES: [ExecutionMode; 2] = [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable];
const BATCHES: [u32; 5] = [1, 2, 64, 256, 1024];
const ACTIONS: [&str; 4] = ["edit", "read", "release", "remove"];
const OWNED: [&str; 3] = ["edit", "release", "remove"];
const READ: [&str; 2] = ["read", "remove"];
type Sample = (usize, &'static str, usize);

fn event(store: &HistoryStore, principal: &str, action: &str, resource: &str) -> Event {
    Event {
        principal: store.intern_principal(principal).unwrap(),
        action: store.intern_action(action).unwrap(),
        resource: store.intern_resource(resource).unwrap(),
    }
}

struct Fixture {
    store: Arc<HistoryStore>,
    history: HistoryHandle,
    vm: RegoVM,
}

impl Fixture {
    fn sample(&self, e: Sample) -> Event {
        event(&self.store, &format!("a{}", e.0), e.1, &format!("f{}", e.2))
    }

    fn new(program: &Arc<Program>, mode: ExecutionMode) -> Self {
        Self::with_store(program, mode, Arc::new(HistoryStore::new()))
    }

    fn with_store(program: &Arc<Program>, mode: ExecutionMode, store: Arc<HistoryStore>) -> Self {
        let history = store.new_history().unwrap();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.attach_history(store.clone()).unwrap();
        Self { store, history, vm }
    }

    fn replace(&self, events: &[Event]) {
        self.store.truncate(&self.history, 0).unwrap();
        self.store.append(&self.history, events).unwrap();
    }

    fn decide(&mut self, request: Event) -> Result<Value, VmError> {
        self.vm.set_history_input(self.history.clone(), request)?;
        self.vm.execute_entry_point_by_name("decide")
    }
}

fn table(rules: Vec<Json>, batch_size: u32) -> Arc<Program> {
    let rule_count = rules.len();
    let program = compile(&json!({"rules": rules}).into(), batch_size).unwrap();
    assert_eq!(program.instructions.len(), rule_count + 2);
    assert_eq!(program.entry_points.get("decide"), Some(&0));
    for index in 0..rule_count {
        let Instruction::HistoryStep { params_index } = program.instructions[index] else {
            panic!("expected one HISTORY_STEP per ordered rule");
        };
        let params = &program.instruction_data.history_step_params[usize::from(params_index)];
        assert_eq!(params.table, 0);
        assert_eq!(usize::from(params.rule), index);
        assert_eq!(params.batch_size, batch_size);
    }
    program
}

fn rule(mode: &str, request: Json, history: Json) -> Json {
    json!({"mode": mode, "request": request, "history": history})
}

fn comparison(op: &str, field: &str, term: Json) -> Json {
    json!({(op): {"path": [field], "term": term}})
}

fn constant(field: &str, value: &str) -> Json {
    comparison("eq", field, json!({"value": value}))
}

fn expected(index: Option<usize>) -> Value {
    index.map_or(Value::Null, Value::from)
}

fn prior_edit_rule() -> Json {
    rule(
        "require",
        json!({"object": {
            "principal": {"var": "actor"},
            "action": {"value": "release"},
            "resource": {"var": "resource"}
        }}),
        json!({"concat": [
            {"all": true},
            {"test": {"and": [
                comparison("eq", "principal", json!({"var": "actor"})),
                constant("action", "edit"),
                comparison("eq", "resource", json!({"var": "resource"}))
            ]}},
            {"all": true}
        ]}),
    )
}

#[test]
fn prior_edit_requires_same_principal_and_resource_without_appending_candidate() {
    let program = table(vec![prior_edit_rule()], 256);
    for mode in MODES {
        let mut f = Fixture::new(&program, mode);
        let edit = event(&f.store, "alice", "edit", "doc");
        let release = event(&f.store, "alice", "release", "doc");
        let bob = event(&f.store, "bob", "release", "doc");
        let other = event(&f.store, "alice", "release", "other");
        assert_eq!(f.decide(release).unwrap(), Value::from(0usize));
        f.store.append(&f.history, &[edit]).unwrap();
        assert_eq!(f.decide(release).unwrap(), Value::Null);
        assert_eq!(f.decide(bob).unwrap(), Value::from(0usize));
        assert_eq!(f.decide(other).unwrap(), Value::from(0usize));
        assert_eq!(f.decide(edit).unwrap(), Value::Null);
        assert_eq!(f.store.len(&f.history).unwrap(), 1);
        // Ordinary repeated execution keeps the staged typed input.
        assert_eq!(
            f.vm.execute_entry_point_by_name("decide").unwrap(),
            Value::Null
        );
    }
}

#[test]
fn cached_prefixes_preserve_history_revision_and_binding_semantics() {
    let program = table(vec![prior_edit_rule()], 1);
    for mode in MODES {
        let store = Arc::new(HistoryStore::new());
        let mut a = Fixture::with_store(&program, mode, store.clone());
        let mut b = Fixture::with_store(&program, mode, store.clone());
        let alice_edit = event(&store, "alice", "edit", "doc");
        let bob_edit = event(&store, "bob", "edit", "doc");
        let alice_release = event(&store, "alice", "release", "doc");
        let bob_release = event(&store, "bob", "release", "doc");
        store.append(&a.history, &[alice_edit]).unwrap();
        store.append(&b.history, &[bob_edit]).unwrap();

        let assert_verdict = |f: &mut Fixture, request: Event, granted: bool| {
            let len = f.store.len(&f.history).unwrap();
            assert_eq!(
                f.decide(request).unwrap(),
                expected((!granted).then_some(0))
            );
            assert_eq!(f.store.len(&f.history).unwrap(), len);
        };

        for _ in 0..2 {
            assert_verdict(&mut a, alice_release, true);
            assert_verdict(&mut a, bob_release, false);
            assert_verdict(&mut b, alice_release, false);
            assert_verdict(&mut b, bob_release, true);
        }

        store.append(&b.history, &[alice_edit]).unwrap();
        assert_verdict(&mut b, alice_release, true);
        assert_verdict(&mut b, bob_release, true);

        a.replace(&[bob_edit]);
        assert_eq!(store.len(&a.history).unwrap(), 1);
        assert_verdict(&mut a, alice_release, false);
        assert_verdict(&mut a, bob_release, true);
        assert_verdict(&mut b, alice_release, true);
        assert_verdict(&mut b, bob_release, true);

        for _ in 0..17 {
            let mut other = Fixture::with_store(&program, mode, store.clone());
            store.append(&other.history, &[alice_edit]).unwrap();
            assert_verdict(&mut other, alice_release, true);
            assert_verdict(&mut other, bob_release, false);
        }

        assert_verdict(&mut a, alice_release, false);
        assert_verdict(&mut a, bob_release, true);
        assert_verdict(&mut b, alice_release, true);
        assert_verdict(&mut b, bob_release, true);
    }
}

fn approval_rule() -> Json {
    let same_resource = comparison("eq", "resource", json!({"var": "resource"}));
    let no_edit = json!({"star": {"test": {"or": [
        comparison("neq", "resource", json!({"var": "resource"})),
        comparison("neq", "action", json!({"value": "edit"}))
    ]}}});
    rule(
        "require",
        json!({"object": {
            "principal": {"var": "actor"},
            "action": {"value": "release"},
            "resource": {"var": "resource"}
        }}),
        json!({"concat": [
            {"all": true},
            {"test": {"and": [
                same_resource.clone(), constant("action", "edit"),
                comparison("eq", "principal", json!({"var": "actor"}))
            ]}},
            no_edit.clone(),
            {"test": {"and": [
                same_resource, constant("action", "approve"),
                comparison("neq", "principal", json!({"var": "actor"}))
            ]}},
            no_edit
        ]}),
    )
}

#[test]
fn approval_must_follow_edit_be_other_actor_and_not_be_stale() {
    let program = table(vec![approval_rule()], 256);
    for mode in MODES {
        let mut f = Fixture::new(&program, mode);
        let edit = event(&f.store, "alice", "edit", "doc");
        let approve = event(&f.store, "bob", "approve", "doc");
        let self_approve = event(&f.store, "alice", "approve", "doc");
        let wrong = event(&f.store, "bob", "approve", "other");
        let unrelated = event(&f.store, "alice", "edit", "other");
        let request = event(&f.store, "alice", "release", "doc");
        for (history, grant) in [
            (vec![], false),
            (vec![edit], false),
            (vec![approve, edit], false),
            (vec![edit, self_approve], false),
            (vec![edit, wrong], false),
            (vec![edit, approve], true),
            (vec![edit, approve, edit], false),
            (vec![edit, approve, unrelated], true),
            (vec![edit, approve, edit, approve], true),
        ] {
            f.replace(&history);
            assert_eq!(
                f.decide(request).unwrap(),
                expected((!grant).then_some(0)),
                "{history:?}"
            );
        }
        f.replace(&[edit, approve, edit]);
        assert_eq!(f.decide(request).unwrap(), Value::from(0usize));
        f.store.truncate(&f.history, 2).unwrap();
        assert_eq!(f.decide(request).unwrap(), Value::Null);
    }
}

fn lock_rule(action: &str, setter: &str, changes: &[&str]) -> Json {
    let unchanged: Vec<_> = changes
        .iter()
        .map(|c| comparison("neq", "action", json!({"value": c})))
        .collect();
    rule(
        "forbid",
        json!({"object": {
            "principal": {"var": "p"}, "action": {"value": action}, "resource": {"var": "r"}
        }}),
        json!({"concat": [
            {"all": true},
            {"test": {"and": [
                comparison("eq", "resource", json!({"var": "r"})),
                constant("action", setter),
                comparison("neq", "principal", json!({"var": "p"}))
            ]}},
            {"star": {"test": {"or": [
                comparison("neq", "resource", json!({"var": "r"})),
                {"and": unchanged}
            ]}}}
        ]}),
    )
}

fn lock_table() -> Arc<Program> {
    table(
        vec![
            lock_rule("edit", "edit", &OWNED),
            lock_rule("edit", "read", &READ),
            lock_rule("release", "edit", &OWNED),
            lock_rule("remove", "edit", &OWNED),
            lock_rule("remove", "read", &READ),
        ],
        256,
    )
}

// Enumerate setters and inspect their suffixes, independently of regex derivatives.
fn lock_oracle(history: &[Sample], candidate: Sample) -> Option<usize> {
    let rules: [(&str, &str, &[&str]); 5] = [
        ("edit", "edit", &OWNED),
        ("edit", "read", &READ),
        ("release", "edit", &OWNED),
        ("remove", "edit", &OWNED),
        ("remove", "read", &READ),
    ];
    rules.iter().position(|&(action, setter, changes)| {
        action == candidate.1
            && history.iter().enumerate().any(|(i, e)| {
                e.2 == candidate.2
                    && e.1 == setter
                    && e.0 != candidate.0
                    && history[i + 1..]
                        .iter()
                        .all(|f| f.2 != candidate.2 || !changes.contains(&f.1))
            })
    })
}

struct Generator(u64);
impl Generator {
    fn below(&mut self, upper: usize) -> usize {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        usize::try_from(self.0 >> 32).unwrap() % upper
    }
    fn event(&mut self) -> Sample {
        (self.below(3), ACTIONS[self.below(4)], self.below(3))
    }
}

#[test]
fn lock_table_matches_independent_oracle_in_both_runners() {
    for mode in MODES {
        let mut f = Fixture::new(&lock_table(), mode);
        let mut rng = Generator(7);
        let mut denials = 0;
        for _ in 0..3000 {
            let len = rng.below(25);
            let history: Vec<_> = (0..len).map(|_| rng.event()).collect();
            let candidate = rng.event();
            let events: Vec<_> = history.iter().map(|&e| f.sample(e)).collect();
            let request = f.sample(candidate);
            f.replace(&events);
            let want = lock_oracle(&history, candidate);
            denials += usize::from(want.is_some());
            assert_eq!(
                f.decide(request).unwrap(),
                expected(want),
                "{history:?} {candidate:?}"
            );
        }
        assert!(denials > 3000 / 100, "only {denials} denials");
    }
}

#[test]
fn incremental_append_truncate_and_repeated_candidates_match_scratch() {
    let program = lock_table();
    for mode in MODES {
        let mut f = Fixture::new(&program, mode);
        let mut history = Vec::new();
        let mut rng = Generator(11);
        for _ in 0..500 {
            match rng.below(3) {
                0 => {
                    let count = 1 + rng.below(8);
                    let batch: Vec<_> = (0..count).map(|_| rng.event()).collect();
                    let events: Vec<_> = batch.iter().map(|&e| f.sample(e)).collect();
                    f.store.append(&f.history, &events).unwrap();
                    history.extend(batch);
                }
                1 => {
                    let len = rng.below(history.len() + 1);
                    f.store.truncate(&f.history, len).unwrap();
                    history.truncate(len);
                }
                _ => {
                    let candidate = rng.event();
                    let request = f.sample(candidate);
                    let got = f.decide(request).unwrap();
                    let mut fresh = Fixture::new(&program, mode);
                    let events: Vec<_> = history.iter().map(|&e| fresh.sample(e)).collect();
                    let fresh_request = fresh.sample(candidate);
                    fresh.replace(&events);
                    assert_eq!(got, fresh.decide(fresh_request).unwrap());
                    assert_eq!(got, expected(lock_oracle(&history, candidate)));
                    assert_eq!(f.decide(request).unwrap(), got);
                }
            }
            assert_eq!(f.store.len(&f.history).unwrap(), history.len());
        }
    }
}

#[test]
fn require_forbid_order_returns_first_violated_rule() {
    let programs = [
        table(
            vec![
                rule("require", json!({"any": true}), json!({"empty": true})),
                rule("forbid", json!({"any": true}), json!({"all": true})),
            ],
            256,
        ),
        table(
            vec![
                rule(
                    "forbid",
                    json!({"object": {"action": {"value": "skip"}}}),
                    json!({"all": true}),
                ),
                rule("require", json!({"any": true}), json!({"empty": true})),
                rule("forbid", json!({"any": true}), json!({"all": true})),
            ],
            256,
        ),
    ];
    for mode in MODES {
        for (index, program) in programs.iter().enumerate() {
            let mut f = Fixture::new(program, mode);
            let request = event(&f.store, "alice", "read", "doc");
            assert_eq!(f.decide(request).unwrap(), Value::from(index));
        }
    }
}

#[derive(Clone, Debug)]
enum Test {
    Bool(bool),
    Compare {
        field: usize,
        unequal: bool,
        variable: bool,
        literal: usize,
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

type WordEvent = [usize; 3];
const FIELDS: [&str; 3] = ["principal", "action", "resource"];
const VARIABLES: [&str; 3] = ["p", "a", "r"];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TypedWord(WordEvent);

impl history_syntax::Event for TypedWord {
    type Principal = usize;
    type Action = usize;
    type Resource = usize;

    fn principal(self) -> usize {
        self.0[0]
    }
    fn action(self) -> usize {
        self.0[1]
    }
    fn resource(self) -> usize {
        self.0[2]
    }
}

impl Test {
    fn owned(&self) -> TestExpr<TypedWord> {
        match self {
            Self::Bool(true) => TestExpr::True,
            Self::Bool(false) => TestExpr::False,
            Self::Compare {
                field,
                unequal,
                variable,
                literal,
            } => {
                let component = if *variable {
                    ComponentPattern::variable(VARIABLES[*field])
                } else {
                    ComponentPattern::constant(*literal)
                };
                TestExpr::Atom {
                    comparison: if *unequal {
                        Comparison::Neq
                    } else {
                        Comparison::Eq
                    },
                    pattern: match field {
                        0 => AtomPattern::Principal(component),
                        1 => AtomPattern::Action(component),
                        2 => AtomPattern::Resource(component),
                        _ => unreachable!("oracle has three coordinates"),
                    },
                }
            }
            Self::And(children) => TestExpr::And(children.iter().map(Self::owned).collect()),
            Self::Or(children) => TestExpr::Or(children.iter().map(Self::owned).collect()),
        }
    }

    fn matches(&self, event: &WordEvent, binding: &WordEvent) -> bool {
        match self {
            Test::Bool(value) => *value,
            Test::Compare {
                field,
                unequal,
                variable,
                literal,
            } => (event[*field] == if *variable { binding[*field] } else { *literal }) != *unequal,
            Test::And(children) => children.iter().all(|t| t.matches(event, binding)),
            Test::Or(children) => children.iter().any(|t| t.matches(event, binding)),
        }
    }

    fn source(&self) -> Json {
        match self {
            Test::Bool(value) => json!(value),
            Test::Compare {
                field,
                unequal,
                variable,
                literal,
            } => comparison(
                if *unequal { "neq" } else { "eq" },
                FIELDS[*field],
                if *variable {
                    json!({"var": VARIABLES[*field]})
                } else {
                    json!({"value": format!("id{literal}")})
                },
            ),
            Test::And(children) => {
                json!({"and": children.iter().map(Test::source).collect::<Vec<_>>()})
            }
            Test::Or(children) => {
                json!({"or": children.iter().map(Test::source).collect::<Vec<_>>()})
            }
        }
    }
}

impl Regex {
    fn owned(&self) -> RegexExpr<TypedWord> {
        match self {
            Self::Empty => RegexExpr::Empty,
            Self::All => RegexExpr::All,
            Self::Epsilon => RegexExpr::Epsilon,
            Self::Test(test) => RegexExpr::Test(test.owned()),
            Self::Union(children) => RegexExpr::union(children.iter().map(Self::owned)),
            Self::Concat(children) => RegexExpr::concat(children.iter().map(Self::owned)),
            Self::Intersect(children) => RegexExpr::intersect(children.iter().map(Self::owned)),
            Self::Star(inner) => RegexExpr::star(inner.owned()),
            Self::Not(inner) => RegexExpr::complement(inner.owned()),
        }
    }

    // Bounded recursive oracle enumerates word splits; it shares no production
    // normalization, nullable, derivative, graph or cache implementation.
    fn accepts(&self, history: &[WordEvent], binding: &WordEvent) -> bool {
        match self {
            Regex::Empty => false,
            Regex::All => true,
            Regex::Epsilon => history.is_empty(),
            Regex::Test(test) => matches!(history, [e] if test.matches(e, binding)),
            Regex::Union(children) => children.iter().any(|r| r.accepts(history, binding)),
            Regex::Intersect(children) => children.iter().all(|r| r.accepts(history, binding)),
            Regex::Not(inner) => !inner.accepts(history, binding),
            Regex::Concat(factors) => Self::accepts_concat(factors, history, binding),
            Regex::Star(inner) => {
                history.is_empty()
                    || (1..=history.len()).any(|split| {
                        inner.accepts(&history[..split], binding)
                            && self.accepts(&history[split..], binding)
                    })
            }
        }
    }

    fn accepts_concat(factors: &[Self], history: &[WordEvent], binding: &WordEvent) -> bool {
        match factors {
            [] => history.is_empty(),
            [first, rest @ ..] => (0..=history.len()).any(|split| {
                first.accepts(&history[..split], binding)
                    && Self::accepts_concat(rest, &history[split..], binding)
            }),
        }
    }

    fn derivative(&self, event: &WordEvent, binding: &WordEvent) -> Self {
        match self {
            Regex::Empty | Regex::Epsilon => Regex::Empty,
            Regex::All => Regex::All,
            Regex::Test(test) => {
                if test.matches(event, binding) {
                    Regex::Epsilon
                } else {
                    Regex::Empty
                }
            }
            Regex::Union(children) => Regex::Union(
                children
                    .iter()
                    .map(|r| r.derivative(event, binding))
                    .collect(),
            ),
            Regex::Intersect(children) => Regex::Intersect(
                children
                    .iter()
                    .map(|r| r.derivative(event, binding))
                    .collect(),
            ),
            Regex::Not(inner) => Regex::Not(Box::new(inner.derivative(event, binding))),
            Regex::Star(inner) => {
                Regex::Concat(vec![inner.derivative(event, binding), self.clone()])
            }
            Regex::Concat(children) => {
                let mut alternatives = Vec::new();
                for (index, child) in children.iter().enumerate() {
                    let mut factors = vec![child.derivative(event, binding)];
                    factors.extend_from_slice(&children[index + 1..]);
                    alternatives.push(Regex::Concat(factors));
                    if !child.accepts(&[], binding) {
                        break;
                    }
                }
                Regex::Union(alternatives)
            }
        }
    }

    fn source(&self) -> Json {
        match self {
            Regex::Empty => json!({"empty": true}),
            Regex::All => json!({"all": true}),
            Regex::Epsilon => json!({"epsilon": true}),
            Regex::Test(test) => json!({"test": test.source()}),
            Regex::Union(children) => {
                json!({"union": children.iter().map(Regex::source).collect::<Vec<_>>()})
            }
            Regex::Concat(children) => {
                json!({"concat": children.iter().map(Regex::source).collect::<Vec<_>>()})
            }
            Regex::Intersect(children) => {
                json!({"intersect": children.iter().map(Regex::source).collect::<Vec<_>>()})
            }
            Regex::Star(inner) => json!({"star": inner.source()}),
            Regex::Not(inner) => json!({"not": inner.source()}),
        }
    }
}

impl Generator {
    fn test(&mut self, depth: usize) -> Test {
        if depth > 0 {
            match self.below(4) {
                0 => return Test::And(vec![self.test(depth - 1), self.test(depth - 1)]),
                1 => return Test::Or(vec![self.test(depth - 1), self.test(depth - 1)]),
                _ => {}
            }
        }
        match self.below(6) {
            0 => Test::Bool(true),
            1 => Test::Bool(false),
            n => Test::Compare {
                field: self.below(3),
                unequal: n % 2 == 0,
                variable: n >= 4,
                literal: 1,
            },
        }
    }
    fn regex(&mut self, depth: usize) -> Regex {
        if depth == 0 {
            return match self.below(5) {
                0 => Regex::Empty,
                1 => Regex::All,
                2 => Regex::Epsilon,
                _ => Regex::Test(self.test(1)),
            };
        }
        match self.below(9) {
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

fn oracle_corpus_and_words() -> (Vec<Regex>, [WordEvent; 3], Vec<Vec<WordEvent>>) {
    let leaf = Regex::Test(Test::Compare {
        field: 0,
        unequal: false,
        variable: true,
        literal: 1,
    });
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
        Regex::Intersect(vec![leaf, Regex::All]),
        Regex::Test(Test::And(vec![])),
        Regex::Test(Test::Or(vec![])),
        Regex::Concat(vec![
            Regex::Union(vec![]),
            Regex::Intersect(vec![]),
            Regex::Test(Test::And(vec![])),
            Regex::Test(Test::Or(vec![])),
        ]),
    ];
    let mut generator = Generator(0x5eed_cafe_f00d_beef);
    corpus.extend((0..500).map(|_| generator.regex(2)));
    let alphabet = [[1, 1, 1], [2, 2, 2], [1, 2, 1]];
    let mut words = vec![vec![]];
    let mut layer = vec![vec![]];
    for _ in 0..3 {
        layer = layer
            .iter()
            .flat_map(|prefix| {
                alphabet.iter().map(move |e| {
                    let mut word = prefix.clone();
                    word.push(*e);
                    word
                })
            })
            .collect();
        words.extend(layer.iter().cloned());
    }
    (corpus, alphabet, words)
}

#[test]
fn exhaustive_typed_words_match_split_oracle_and_concrete_derivatives() {
    let (corpus, alphabet, words) = oracle_corpus_and_words();
    for regex in corpus {
        for batch_size in BATCHES {
            let program = table(
                vec![rule(
                    "require",
                    json!({"object": {
                        "principal": {"var": "p"}, "action": {"var": "a"}, "resource": {"var": "r"}
                    }}),
                    regex.source(),
                )],
                batch_size,
            );
            for mode in MODES {
                let mut f = Fixture::new(&program, mode);
                let ids = [
                    event(&f.store, "id1", "id1", "id1"),
                    event(&f.store, "id2", "id2", "id2"),
                    event(&f.store, "id1", "id2", "id1"),
                ];
                for binding in [[1, 1, 1], [2, 2, 2]] {
                    let request = ids[binding[0] - 1];
                    for word in &words {
                        let events: Vec<_> = word
                            .iter()
                            .map(|e| ids[alphabet.iter().position(|a| a == e).unwrap()])
                            .collect();
                        f.replace(&events);
                        let want = regex.accepts(word, &binding);
                        assert_eq!(
                            f.decide(request).unwrap(),
                            expected((!want).then_some(0)),
                            "{regex:?} {word:?} {binding:?} batch={batch_size} mode={mode:?}"
                        );
                        assert_eq!(
                            f.decide(request).unwrap(),
                            expected((!want).then_some(0)),
                            "warm repeat"
                        );
                        if let Some((first, tail)) = word.split_first() {
                            assert_eq!(
                                regex.derivative(first, &binding).accepts(tail, &binding),
                                want
                            );
                        }
                    }
                }
            }
        }
    }
}

fn assert_shared_decision(
    regex: &Regex,
    mode: RuleMode,
    fixture: &mut Fixture,
    compiled: &mut CompiledRule<TypedWord>,
    history: &History<TypedWord>,
    word: &[WordEvent],
    binding: WordEvent,
) {
    let inside = regex.accepts(word, &binding);
    let violation = match mode {
        RuleMode::Require => !inside,
        RuleMode::Forbid => inside,
    };
    let request = event(
        &fixture.store,
        &format!("id{}", binding[0]),
        &format!("id{}", binding[1]),
        &format!("id{}", binding[2]),
    );
    for _ in 0..2 {
        assert_eq!(
            compiled
                .accepts_history(history, &TypedWord(binding))
                .unwrap(),
            Some(inside),
            "owned DSL: {regex:?} {word:?} {binding:?} {mode:?}"
        );
        assert_eq!(
            fixture.decide(request).unwrap(),
            expected(violation.then_some(0)),
            "JSON frontend: {regex:?} {word:?} {binding:?} {mode:?}"
        );
        assert_eq!(fixture.store.len(&fixture.history).unwrap(), word.len());
        assert_eq!(history.len(), word.len());
    }
}

#[test]
fn junco_dsl_and_history_table_frontends_agree() {
    let (corpus, alphabet, words) = oracle_corpus_and_words();
    for regex in corpus {
        for rule_mode in [RuleMode::Require, RuleMode::Forbid] {
            for batch_size in BATCHES {
                let program = table(
                    vec![rule(
                        match rule_mode {
                            RuleMode::Require => "require",
                            RuleMode::Forbid => "forbid",
                        },
                        json!({"object": {
                            "principal": {"var": "p"}, "action": {"var": "a"}, "resource": {"var": "r"}
                        }}),
                        regex.source(),
                    )],
                    batch_size,
                );
                for execution_mode in MODES {
                    let mut fixture = Fixture::new(&program, execution_mode);
                    let store = Arc::new(Store::new().unwrap());
                    let mut compiled = CompiledRule::new(
                        store.clone(),
                        Rule::new(
                            rule_mode,
                            Head::new(
                                ComponentPattern::variable("p"),
                                ComponentPattern::variable("a"),
                                ComponentPattern::variable("r"),
                            ),
                            regex.owned(),
                        ),
                    )
                    .unwrap();
                    let mut history = History::new(store).unwrap();
                    let ids: Vec<_> = alphabet
                        .iter()
                        .map(|e| {
                            event(
                                &fixture.store,
                                &format!("id{}", e[0]),
                                &format!("id{}", e[1]),
                                &format!("id{}", e[2]),
                            )
                        })
                        .collect();
                    for binding in [[1, 1, 1], [2, 2, 2]] {
                        for word in &words {
                            history.truncate(0).unwrap();
                            fixture.replace(&[]);
                            assert_shared_decision(
                                &regex,
                                rule_mode,
                                &mut fixture,
                                &mut compiled,
                                &history,
                                &[],
                                binding,
                            );
                            for e in word {
                                history.push(TypedWord(*e)).unwrap();
                                fixture
                                    .store
                                    .append(
                                        &fixture.history,
                                        &[ids[alphabet.iter().position(|a| a == e).unwrap()]],
                                    )
                                    .unwrap();
                            }
                            assert_shared_decision(
                                &regex,
                                rule_mode,
                                &mut fixture,
                                &mut compiled,
                                &history,
                                word,
                                binding,
                            );
                            if let Some((last, prefix)) = word.split_last() {
                                history.truncate(prefix.len()).unwrap();
                                fixture
                                    .store
                                    .truncate(&fixture.history, prefix.len())
                                    .unwrap();
                                assert_shared_decision(
                                    &regex,
                                    rule_mode,
                                    &mut fixture,
                                    &mut compiled,
                                    &history,
                                    prefix,
                                    binding,
                                );
                                let replacement = alphabet.iter().position(|e| e != last).unwrap();
                                history.push(TypedWord(alphabet[replacement])).unwrap();
                                fixture
                                    .store
                                    .append(&fixture.history, &[ids[replacement]])
                                    .unwrap();
                                let mut replaced = prefix.to_vec();
                                replaced.push(alphabet[replacement]);
                                assert_shared_decision(
                                    &regex,
                                    rule_mode,
                                    &mut fixture,
                                    &mut compiled,
                                    &history,
                                    &replaced,
                                    binding,
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    // A constant action head does not fire, independently of the tail's answer or mode.
    let regex = Regex::Test(Test::Compare {
        field: 0,
        unequal: false,
        variable: true,
        literal: 1,
    });
    for rule_mode in [RuleMode::Require, RuleMode::Forbid] {
        for batch_size in BATCHES {
            let program = table(
                vec![rule(
                    match rule_mode {
                        RuleMode::Require => "require",
                        RuleMode::Forbid => "forbid",
                    },
                    json!({"object": {"principal": {"var": "p"}, "action": {"value": "id1"},
                    "resource": {"var": "r"}}}),
                    regex.source(),
                )],
                batch_size,
            );
            for execution_mode in MODES {
                let mut fixture = Fixture::new(&program, execution_mode);
                let store = Arc::new(Store::new().unwrap());
                let mut compiled = CompiledRule::new(
                    store.clone(),
                    Rule::new(
                        rule_mode,
                        Head::new(
                            ComponentPattern::variable("p"),
                            ComponentPattern::constant(1usize),
                            ComponentPattern::variable("r"),
                        ),
                        regex.owned(),
                    ),
                )
                .unwrap();
                let mut history = History::new(store).unwrap();
                for word in [vec![], vec![[1, 1, 1]]] {
                    fixture.replace(&[]);
                    history.truncate(0).unwrap();
                    for e in word {
                        history.push(TypedWord(e)).unwrap();
                        let recorded = event(&fixture.store, "id1", "id1", "id1");
                        fixture.store.append(&fixture.history, &[recorded]).unwrap();
                    }
                    let mismatch = event(&fixture.store, "id1", "id2", "id1");
                    for _ in 0..2 {
                        assert_eq!(
                            compiled
                                .accepts_history(&history, &TypedWord([1, 2, 1]))
                                .unwrap(),
                            None
                        );
                        assert_eq!(fixture.decide(mismatch).unwrap(), Value::Null);
                        assert_eq!(fixture.store.len(&fixture.history).unwrap(), history.len());
                    }
                }
            }
        }
    }
}

fn assert_flat_epsilon_language(source: FlatPair<String>, nodes: usize, edges: usize) {
    source.validate().unwrap();
    let assert_shape = |program: &Program| {
        let stored = &program.history_tables[0].rules[0].source;
        assert_eq!(stored, &source);
        assert_eq!(stored.regexes.len(), nodes);
        assert_eq!(
            stored
                .regexes
                .iter()
                .map(|node| match node {
                    FlatRegex::Concat(children)
                    | FlatRegex::Union(children)
                    | FlatRegex::Intersect(children) => children.len(),
                    FlatRegex::Star(_) | FlatRegex::Complement(_) => 1,
                    _ => 0,
                })
                .sum::<usize>(),
            edges
        );
    };
    for batch_size in BATCHES {
        let mut program = (*table(
            vec![rule(
                "require",
                json!({"any": true}),
                json!({"epsilon": true}),
            )],
            batch_size,
        ))
        .clone();
        program.history_tables[0].rules[0].source = source.clone();
        assert_shape(&program);
        let json_program = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
        let DeserializationResult::Complete(binary_program) =
            Program::deserialize_binary(&program.serialize_binary().unwrap()).unwrap()
        else {
            panic!("current version must deserialize completely");
        };
        for restored in [program, json_program, binary_program] {
            assert_shape(&restored);
            let restored = Arc::new(restored);
            for mode in MODES {
                let mut fixture = Fixture::new(&restored, mode);
                let probe = event(&fixture.store, "alice", "read", "doc");
                for _ in 0..2 {
                    assert_eq!(fixture.decide(probe).unwrap(), Value::Null);
                }
                fixture.store.append(&fixture.history, &[probe]).unwrap();
                for _ in 0..2 {
                    assert_eq!(fixture.decide(probe).unwrap(), Value::from(0usize));
                    assert_eq!(fixture.store.len(&fixture.history).unwrap(), 1);
                }
                assert_shape(&restored);
            }
        }
    }
}

#[test]
fn flat_shared_dag_roundtrips_and_executes_without_unfolding() {
    let mut regexes = vec![FlatRegex::Epsilon];
    for index in 1..4096 {
        regexes.push(FlatRegex::Concat(vec![index - 1, index - 1]));
    }
    assert_flat_epsilon_language(
        FlatPair {
            head: [FlatHead::Any, FlatHead::Any, FlatHead::Any],
            tests: vec![],
            regexes,
            root: 4095,
        },
        4096,
        8190,
    );
}

#[test]
fn flat_deep_unary_and_non_last_root_preserve_topology() {
    let mut regexes = vec![FlatRegex::Epsilon];
    for index in 1..4096 {
        regexes.push(FlatRegex::Star(index - 1));
    }
    assert_flat_epsilon_language(
        FlatPair {
            head: [FlatHead::Any, FlatHead::Any, FlatHead::Any],
            tests: vec![],
            regexes,
            root: 4095,
        },
        4096,
        4095,
    );
    assert_flat_epsilon_language(
        FlatPair {
            head: [FlatHead::Any, FlatHead::Any, FlatHead::Any],
            tests: vec![FlatTest::Bool(false)],
            regexes: vec![
                FlatRegex::Epsilon,
                FlatRegex::All,
                FlatRegex::Test(0),
                FlatRegex::Star(1),
            ],
            root: 0,
        },
        4,
        1,
    );
}

#[test]
fn native_value_parser_handles_deep_policy_without_recursive_fixture_drop() {
    fn object(fields: Vec<(&str, Value)>) -> Value {
        fields
            .into_iter()
            .map(|(key, value)| (Value::from(key), value))
            .collect::<std::collections::BTreeMap<_, _>>()
            .into()
    }

    let mut history = object(vec![("epsilon", Value::from(true))]);
    // Keep every level alive until its parents have dropped, so fixture teardown is iterative.
    let mut keepalive = vec![history.clone()];
    for _ in 1..4096 {
        history = object(vec![("star", history)]);
        keepalive.push(history.clone());
    }
    let document = object(vec![(
        "rules",
        Value::from(vec![object(vec![
            ("mode", Value::from("require")),
            ("request", object(vec![("any", Value::from(true))])),
            ("history", history),
        ])]),
    )]);
    for batch_size in BATCHES {
        let program = compile(&document, batch_size).unwrap();
        let source = &program.history_tables[0].rules[0].source;
        assert_eq!(source.regexes.len(), 4096);
        assert_eq!(source.regexes[0], FlatRegex::Epsilon);
        for (index, node) in source.regexes.iter().enumerate().skip(1) {
            assert_eq!(node, &FlatRegex::Star(u32::try_from(index - 1).unwrap()));
        }
        assert_eq!(source.root, 4095);
        for mode in MODES {
            let mut fixture = Fixture::new(&program, mode);
            let probe = event(&fixture.store, "alice", "read", "doc");
            assert_eq!(fixture.decide(probe).unwrap(), Value::Null);
            fixture.store.append(&fixture.history, &[probe]).unwrap();
            assert_eq!(fixture.decide(probe).unwrap(), Value::from(0usize));
        }
    }
    drop(document);
    while let Some(level) = keepalive.pop() {
        drop(level);
    }
}

fn read_star(batch_size: u32) -> Arc<Program> {
    table(
        vec![rule(
            "require",
            json!({"any": true}),
            json!({"star": {
                "test": constant("action", "read")
            }}),
        )],
        batch_size,
    )
}

fn assert_step(vm: &RegoVM, pc: usize) {
    assert!(
        matches!(vm.execution_state(), ExecutionState::Suspended {
        reason: SuspendReason::Step, pc: actual, ..
    } if *actual == pc),
        "{:?}",
        vm.execution_state()
    );
    assert_eq!(vm.get_pc(), pc);
}

fn finish(vm: &mut RegoVM) -> Result<Value, VmError> {
    while matches!(vm.execution_state(), ExecutionState::Suspended { .. }) {
        vm.resume(None)?;
    }
    match vm.execution_state() {
        ExecutionState::Completed { result } => Ok(result.clone()),
        state => panic!("expected completion, got {state:?}"),
    }
}

#[test]
fn batch_edges_repeat_pc_zero_and_charge_every_dispatch() {
    for len in [0usize, 1, 2, 3, 4, 6, 7] {
        let program = read_star(3);
        assert_eq!(program.instructions.len(), 3);
        assert!(matches!(
            program.instructions[0],
            Instruction::HistoryStep { .. }
        ));
        assert!(matches!(
            program.instructions[1],
            Instruction::LoadNull { dest: 0 }
        ));
        assert!(matches!(
            program.instructions[2],
            Instruction::Return { value: 0 }
        ));
        let batches = len.div_ceil(3).max(1);
        let mut f = Fixture::new(&program, ExecutionMode::Suspendable);
        let read = event(&f.store, "alice", "read", "doc");
        f.replace(&vec![read; len]);
        f.vm.set_step_mode(true);
        f.decide(read).unwrap();
        for index in 0..batches {
            assert_step(&f.vm, 0);
            if index + 1 < batches {
                f.vm.resume(None).unwrap();
            }
        }
        f.vm.resume(None).unwrap();
        assert_step(&f.vm, 1);
        assert_eq!(finish(&mut f.vm).unwrap(), Value::Null);
        for mode in MODES {
            let mut limited = Fixture::new(&program, mode);
            let read = event(&limited.store, "alice", "read", "doc");
            limited.replace(&vec![read; len]);
            limited.vm.set_max_instructions(batches + 1);
            assert!(matches!(
                limited.decide(read),
                Err(VmError::InstructionLimitExceeded { .. })
            ));
            limited.vm.set_max_instructions(batches + 2);
            assert_eq!(limited.decide(read).unwrap(), Value::Null);
        }
    }
}

#[test]
fn nullable_intermediate_prefix_cannot_grant_before_rejecting_suffix() {
    for mode in MODES {
        let mut f = Fixture::new(&read_star(1), mode);
        let read = event(&f.store, "alice", "read", "doc");
        let edit = event(&f.store, "alice", "edit", "doc");
        f.replace(&[read, edit]);
        if mode == ExecutionMode::Suspendable {
            f.vm.set_step_mode(true);
            f.decide(read).unwrap();
            assert_step(&f.vm, 0);
            assert_eq!(finish(&mut f.vm).unwrap(), Value::from(0usize));
        } else {
            assert_eq!(f.decide(read).unwrap(), Value::from(0usize));
        }
    }
}

#[test]
fn append_after_snapshot_is_excluded_but_fresh_decision_includes_it() {
    let mut f = Fixture::new(&read_star(3), ExecutionMode::Suspendable);
    let read = event(&f.store, "alice", "read", "doc");
    let edit = event(&f.store, "alice", "edit", "doc");
    f.replace(&[read; 4]);
    f.vm.set_step_mode(true);
    f.decide(read).unwrap();
    assert_step(&f.vm, 0);
    f.store.append(&f.history, &[edit]).unwrap();
    assert_eq!(finish(&mut f.vm).unwrap(), Value::Null);
    f.vm.set_step_mode(false);
    assert_eq!(f.decide(read).unwrap(), Value::from(0usize));
}

#[test]
fn newer_shared_cache_prefix_cannot_seed_an_older_decision_target() {
    let program = table(
        vec![
            rule("require", json!({"any": true}), json!({"all": true})),
            rule(
                "require",
                json!({"any": true}),
                json!({"star": {"test": constant("action", "read")}}),
            ),
        ],
        1,
    );
    let mut old = Fixture::new(&program, ExecutionMode::Suspendable);
    let read = event(&old.store, "alice", "read", "doc");
    let edit = event(&old.store, "alice", "edit", "doc");
    old.replace(&[read; 3]);
    old.vm.set_step_mode(true);
    old.decide(read).unwrap();
    assert_step(&old.vm, 0);
    old.store.append(&old.history, &[edit]).unwrap();
    let mut newer = RegoVM::new();
    newer.load_program(program);
    newer.attach_history(old.store.clone()).unwrap();
    newer.set_history_input(old.history.clone(), read).unwrap();
    assert_eq!(
        newer.execute_entry_point_by_name("decide").unwrap(),
        Value::from(1usize)
    );
    assert_eq!(finish(&mut old.vm).unwrap(), Value::Null);
    old.vm.set_step_mode(false);
    assert_eq!(old.decide(read).unwrap(), Value::from(1usize));
}

#[test]
fn truncate_reappend_invalidates_batch_and_both_terminal_boundaries() {
    for resumes in 0..3 {
        let mut f = Fixture::new(&read_star(3), ExecutionMode::Suspendable);
        let read = event(&f.store, "alice", "read", "doc");
        f.replace(&[read; 4]);
        f.vm.set_step_mode(true);
        f.decide(read).unwrap();
        for _ in 0..resumes {
            f.vm.resume(None).unwrap();
        }
        assert_step(&f.vm, usize::from(resumes == 2));
        // Preserve length and bytes: only the revision can detect this rewrite.
        f.store.truncate(&f.history, 0).unwrap();
        f.store.append(&f.history, &[read; 4]).unwrap();
        assert!(matches!(
            finish(&mut f.vm),
            Err(VmError::History {
                source: HistoryError::HistoryChanged {
                    expected: 0,
                    actual: 1
                },
                ..
            })
        ));
        assert!(!matches!(
            f.vm.execution_state(),
            ExecutionState::Completed { .. }
        ));
        f.vm.set_step_mode(false);
        assert_eq!(f.decide(read).unwrap(), Value::Null);
    }
}

#[test]
fn suspended_execution_rejects_restaging_and_reattachment() {
    let mut f = Fixture::new(&read_star(1), ExecutionMode::Suspendable);
    let read = event(&f.store, "alice", "read", "doc");
    f.replace(&[read; 3]);
    f.vm.set_step_mode(true);
    f.decide(read).unwrap();
    assert!(matches!(
        f.vm.set_history_input(f.history.clone(), read),
        Err(VmError::HistoryExecutionActive { .. })
    ));
    assert!(matches!(
        f.vm.attach_history(f.store.clone()),
        Err(VmError::HistoryExecutionActive { .. })
    ));
    assert!(matches!(
        f.vm.attach_history(Arc::new(HistoryStore::new())),
        Err(VmError::HistoryExecutionActive { .. })
    ));
    assert_eq!(finish(&mut f.vm).unwrap(), Value::Null);
}

#[test]
fn load_program_cancels_suspension_and_drops_typed_context_not_shared_history() {
    let program = read_star(1);
    let mut f = Fixture::new(&program, ExecutionMode::Suspendable);
    let read = event(&f.store, "alice", "read", "doc");
    f.replace(&[read; 3]);
    let mut peer = RegoVM::new();
    peer.load_program(program);
    peer.attach_history(f.store.clone()).unwrap();
    peer.set_history_input(f.history.clone(), read).unwrap();
    f.vm.set_step_mode(true);
    f.decide(read).unwrap();
    f.vm.load_program(table(vec![], 256));
    assert!(matches!(f.vm.execution_state(), ExecutionState::Ready));
    assert!(matches!(
        f.vm.resume(None),
        Err(VmError::InvalidResumeState { .. })
    ));
    f.vm.set_step_mode(false);
    assert!(matches!(
        f.vm.execute_entry_point_by_name("decide"),
        Err(VmError::HistoryContextMissing { .. })
    ));
    f.vm.attach_history(f.store.clone()).unwrap();
    assert!(matches!(
        f.vm.execute_entry_point_by_name("decide"),
        Err(VmError::HistoryContextMissing { .. })
    ));
    f.vm.set_history_input(f.history.clone(), read).unwrap();
    assert_eq!(
        f.vm.execute_entry_point_by_name("decide").unwrap(),
        Value::Null
    );
    assert_eq!(f.store.len(&f.history).unwrap(), 3);
    assert_eq!(
        peer.execute_entry_point_by_name("decide").unwrap(),
        Value::Null
    );
}

#[test]
fn staging_requires_attachment_owner_and_each_domain_membership() {
    let program = read_star(256);
    let store = Arc::new(HistoryStore::new());
    let foreign = Arc::new(HistoryStore::new());
    let history = store.new_history().unwrap();
    let own = event(&store, "alice", "read", "doc");
    let other = event(&foreign, "alice", "read", "doc");
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert!(matches!(
        vm.set_history_input(history.clone(), own),
        Err(VmError::HistoryContextMissing { .. })
    ));
    vm.attach_history(store.clone()).unwrap();
    assert!(matches!(
        vm.set_history_input(foreign.new_history().unwrap(), own),
        Err(VmError::History {
            source: HistoryError::WrongHistoryOwner,
            ..
        })
    ));
    for (request, domain) in [
        (
            Event {
                principal: other.principal,
                ..own
            },
            "principal",
        ),
        (
            Event {
                action: other.action,
                ..own
            },
            "action",
        ),
        (
            Event {
                resource: other.resource,
                ..own
            },
            "resource",
        ),
    ] {
        assert!(matches!(vm.set_history_input(history.clone(), request),
            Err(VmError::History { source: HistoryError::UnknownId { domain: actual, .. }, .. }) if actual == domain));
    }
    vm.set_history_input(history, own).unwrap();
    assert_eq!(
        vm.execute_entry_point_by_name("decide").unwrap(),
        Value::Null
    );
}

#[test]
fn empty_table_preflights_context_in_both_runners() {
    let program = table(vec![], 256);
    assert_eq!(program.instructions.len(), 2);
    for mode in MODES {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        assert!(matches!(
            vm.execute_entry_point_by_name("decide"),
            Err(VmError::HistoryContextMissing { .. })
        ));
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let request = event(&store, "alice", "read", "doc");
        vm.attach_history(store).unwrap();
        assert!(matches!(
            vm.execute_entry_point_by_name("decide"),
            Err(VmError::HistoryContextMissing { .. })
        ));
        vm.set_history_input(history, request).unwrap();
        assert_eq!(
            vm.execute_entry_point_by_name("decide").unwrap(),
            Value::Null
        );
    }
}

#[test]
fn empty_table_still_checks_revision_before_terminal_return() {
    let mut f = Fixture::new(&table(vec![], 256), ExecutionMode::Suspendable);
    let request = event(&f.store, "alice", "read", "doc");
    f.replace(&[request]);
    f.vm.set_step_mode(true);
    f.decide(request).unwrap();
    assert_step(&f.vm, 0);
    f.store.truncate(&f.history, 0).unwrap();
    assert!(matches!(
        finish(&mut f.vm),
        Err(VmError::History {
            source: HistoryError::HistoryChanged { .. },
            ..
        })
    ));
}

#[test]
fn zero_batch_is_rejected_before_empty_or_head_mismatch_shortcuts() {
    assert!(matches!(
        compile(&json!({"rules": []}).into(), 0),
        Err(HistoryTableError::InvalidBatchSize)
    ));
    for mode in MODES {
        for matching in [false, true] {
            let mut program = (*table(vec![rule("require",
                json!({"object": {"action": {"value": if matching { "read" } else { "release" }}}}),
                json!({"all": true}))], 256)).clone();
            program.instruction_data.history_step_params[0].batch_size = 0;
            assert!(program.validate_limits().is_err());
            let mut f = Fixture::new(&Arc::new(program), mode);
            let request = event(&f.store, "alice", "read", "doc");
            assert!(matches!(
                f.decide(request),
                Err(VmError::InvalidHistoryBatchSize { batch_size: 0, .. })
            ));
        }
    }
}

#[test]
fn current_binary_and_json_reintern_constants_in_fresh_store() {
    let program = table(vec![prior_edit_rule()], 256);
    let mut original = Fixture::new(&program, ExecutionMode::RunToCompletion);
    let old_edit = event(&original.store, "alice", "edit", "doc");
    let old_request = event(&original.store, "alice", "release", "doc");
    original.replace(&[old_edit]);
    assert_eq!(original.decide(old_request).unwrap(), Value::Null);
    let bytes = program.serialize_binary().unwrap();
    assert_eq!(Program::SERIALIZATION_VERSION, 8);
    assert_eq!(&bytes[4..8], &8u32.to_le_bytes());
    let DeserializationResult::Complete(binary) = Program::deserialize_binary(&bytes).unwrap()
    else {
        panic!("current version must deserialize completely");
    };
    let json_program = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
    for restored in [binary, json_program] {
        let store = Arc::new(HistoryStore::new());
        let _ = event(&store, "bob", "release", "other");
        let edit = event(&store, "alice", "edit", "doc");
        let request = event(&store, "alice", "release", "doc");
        assert_ne!(edit.principal, old_edit.principal);
        assert_ne!(edit.action, old_edit.action);
        assert_ne!(edit.resource, old_edit.resource);
        let mut f = Fixture::with_store(&Arc::new(restored), ExecutionMode::RunToCompletion, store);
        assert_eq!(f.decide(request).unwrap(), Value::from(0usize));
        f.replace(&[edit]);
        assert_eq!(f.decide(request).unwrap(), Value::Null);
        let other = event(&f.store, "bob", "release", "doc");
        assert_eq!(f.decide(other).unwrap(), Value::from(0usize));
    }
    let mut obsolete = bytes;
    obsolete[4..8].copy_from_slice(&7u32.to_le_bytes());
    obsolete.truncate(8); // Version rejection must precede payload decoding.
    let error = Program::deserialize_binary(&obsolete).unwrap_err();
    assert!(error.to_lowercase().contains("recompil"), "{error}");
    assert_eq!(std::mem::size_of::<Instruction>(), 6);
}

fn unchecked_binary(program: &Program) -> Vec<u8> {
    let mut bytes = read_star(256).serialize_binary().unwrap();
    let section_bytes: usize = (8..24)
        .step_by(4)
        .map(|offset| u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap()) as usize)
        .sum();
    bytes.truncate(25 + section_bytes);
    let payload = postcard::to_allocvec(program).unwrap();
    bytes.extend_from_slice(&u32::try_from(payload.len()).unwrap().to_le_bytes());
    bytes.extend_from_slice(&payload);
    bytes
}

#[test]
fn malformed_source_nodes_variables_and_indexes_are_rejected() {
    let base = (*table(vec![prior_edit_rule()], 256)).clone();
    let mut invalid = Vec::new();
    let mut p = base.clone();
    p.history_tables[0].rules[0].source.regexes = vec![FlatRegex::Star(0)];
    p.history_tables[0].rules[0].source.root = 0;
    invalid.push(p);
    let mut p = base.clone();
    p.history_tables[0].rules[0].source.regexes = vec![FlatRegex::Test(u32::MAX)];
    p.history_tables[0].rules[0].source.root = 0;
    invalid.push(p);
    let mut p = base.clone();
    p.history_tables[0].rules[0].source.root = u32::MAX;
    invalid.push(p);
    let mut p = base.clone();
    p.history_tables[0].rules[0].source.tests = vec![FlatTest::And(vec![0])];
    invalid.push(p);
    let mut p = base.clone();
    p.history_tables[0].rules[0].source.tests = vec![FlatTest::Atom {
        field: Component::Principal,
        term: FlatTerm::Variable(Component::Resource),
        positive: true,
    }];
    invalid.push(p);
    let mut p = base.clone();
    p.history_tables[0].rules[0].source.tests = vec![FlatTest::Atom {
        field: Component::Action,
        term: FlatTerm::Variable(Component::Action),
        positive: true,
    }];
    invalid.push(p); // Action is Constant in the head, not Bind.
    let mut p = base.clone();
    p.instruction_data.history_step_params[0].table = u16::MAX;
    invalid.push(p);
    let mut p = base.clone();
    p.instruction_data.history_step_params[0].rule = u16::MAX;
    invalid.push(p);
    let mut p = base.clone();
    p.instructions[0] = Instruction::HistoryStep {
        params_index: u16::MAX,
    };
    invalid.push(p);
    let mut p = base;
    p.instruction_data.history_step_params[0].batch_size = 0;
    invalid.push(p);
    for program in invalid {
        assert!(program.validate_limits().is_err());
        assert!(program.serialize_binary().is_err());
        let mut serialized: Json =
            serde_json::from_str(&read_star(256).serialize_json().unwrap()).unwrap();
        serialized["history_tables"] = serde_json::to_value(&program.history_tables).unwrap();
        serialized["instructions"] = serde_json::to_value(&program.instructions).unwrap();
        serialized["instruction_data"] = serde_json::to_value(&program.instruction_data).unwrap();
        assert!(Program::deserialize_json(&serialized.to_string()).is_err());
        assert!(!matches!(
            Program::deserialize_binary(&unchecked_binary(&program)),
            Ok(DeserializationResult::Complete(_))
        ));
        let invalid_source = program.history_tables[0].rules[0]
            .source
            .validate()
            .is_err();
        let store = Arc::new(HistoryStore::new());
        let history = store.new_history().unwrap();
        let request = event(&store, "alice", "release", "doc");
        let mut vm = RegoVM::new();
        vm.load_program(Arc::new(program));
        if invalid_source {
            assert!(vm.attach_history(store).is_err());
        } else {
            vm.attach_history(store).unwrap();
            vm.set_history_input(history, request).unwrap();
            assert!(matches!(
                vm.execute_entry_point_by_name("decide"),
                Err(VmError::InvalidHistoryStepParams { .. }
                    | VmError::InvalidHistoryTableIndex { .. }
                    | VmError::InvalidHistoryRuleIndex { .. }
                    | VmError::InvalidHistoryBatchSize { .. })
            ));
        }
    }
}

#[test]
fn source_rejects_removed_generic_language_and_invalid_shapes() {
    let bad_heads = [
        json!({"object": {"metadata": {"any": true}}}),
        json!({"object": {"principal": {"object": {"name": {"any": true}}}}}),
        json!({"object": {"principal": {"value": 1}}}),
        json!({"object": {"principal": {"value": null}}}),
        json!({"object": {"principal": {"type": "string"}}}),
        json!({"object": {"principal": {"var": "x"}, "resource": {"var": "x"}}}),
        json!({"object": {"principal": {"var": "x"}, "action": {"var": "x"}}}),
        json!({"array": []}),
        json!({"set": []}),
        json!({"var": "x"}),
        json!({"value": "alice"}),
    ];
    for request in bad_heads {
        let source = json!({"rules": [rule("require", request, json!({"all": true}))]});
        assert!(matches!(
            compile(&source.into(), 256),
            Err(HistoryTableError::InvalidPair { index: 0, .. })
        ));
    }
    let bad_tests = [
        json!({"eq": {"path": ["principal", "name"], "term": {"value": "alice"}}}),
        json!({"eq": {"path": [], "term": {"value": "alice"}}}),
        constant("unknown", "alice"),
        comparison("eq", "action", json!({"value": 1})),
        comparison("eq", "action", json!({"var": "missing"})),
        comparison("eq", "resource", json!({"var": "actor"})),
        comparison("eq", "action", json!({"var": "actor"})),
        comparison("eq", "principal", json!({"var": "unknown"})),
        json!({"eq": {"path": ["action"]}}),
        json!({"eq": {"path": ["action"], "term": {"value": "read"}, "extra": true}}),
        json!({"and": true}),
        json!({"not": true}),
    ];
    for test in bad_tests {
        let source = json!({"rules": [rule("require",
            json!({"object": {"principal": {"var": "actor"}}}), json!({"test": test}))]});
        assert!(matches!(
            compile(&source.into(), 256),
            Err(HistoryTableError::InvalidPair { index: 0, .. })
        ));
    }
    for regex in [
        json!({"bogus": true}),
        json!({"star": []}),
        json!({"concat": true}),
        json!({"empty": false}),
    ] {
        assert!(compile(
            &json!({"rules": [rule("require", json!({"any": true}), regex)]}).into(),
            256
        )
        .is_err());
    }
    assert!(matches!(
        compile(&json!({}).into(), 256),
        Err(HistoryTableError::MissingRules)
    ));
    assert!(matches!(
        compile(
            &json!({"rules": [rule("deny", json!({"any": true}), json!({"all": true}))]}).into(),
            256
        ),
        Err(HistoryTableError::BadMode { index: 0, .. })
    ));
    for (pair, missing) in [
        (
            json!({"mode": "require", "history": {"star": []}}),
            "request",
        ),
        (
            json!({"mode": "require", "request": {"value": 3}}),
            "history",
        ),
    ] {
        assert!(matches!(
            compile(&json!({"rules": [pair]}).into(), 256),
            Err(HistoryTableError::MissingMember { index: 0, member }) if member == missing
        ));
    }
    assert!(matches!(
        compile(
            &json!({"rules": [{"mode": "deny", "history": {"star": []}}]}).into(),
            256
        ),
        Err(HistoryTableError::BadMode { index: 0, .. })
    ));
    assert!(matches!(
        compile(
            &json!({"rules": [{"mode": "require", "unknown": true}]}).into(),
            256
        ),
        Err(HistoryTableError::InvalidPair { index: 0, .. })
    ));
    assert!(matches!(
        compile(
            &json!({"rules": [{"mode": "deny", "unknown": true}]}).into(),
            0
        ),
        Err(HistoryTableError::InvalidBatchSize)
    ));
}

#[test]
fn removed_history_builtin_is_unknown_in_interpreter_and_rvm_compilation() {
    const SOURCE: &str = "package removed\nimport rego.v1\nresult := history.match({}, [], {})";
    let mut engine = Engine::new();
    engine
        .add_policy("removed.rego".into(), SOURCE.into())
        .unwrap();
    assert!(engine.eval_rule("data.removed.result".into()).is_err());
    let mut engine = Engine::new();
    engine
        .add_policy("removed.rego".into(), SOURCE.into())
        .unwrap();
    let policy = engine
        .compile_with_entrypoint(&"data.removed.result".into())
        .unwrap();
    let error = regorus::languages::rego::compiler::Compiler::compile_from_policy(
        &policy,
        &["data.removed.result"],
    )
    .unwrap_err();
    assert!(matches!(error.error,
        regorus::languages::rego::compiler::CompilerError::UnknownFunction { ref name }
        if name == "history.match"));
}

#[cfg(feature = "std")]
#[test]
fn concurrent_vms_share_identities_and_fixed_prefix_without_sharing_candidates() {
    use std::sync::Barrier;
    let program = table(
        vec![rule(
            "require",
            json!({"object": {"principal": {"var": "p"}}}),
            json!({"star": {"test": comparison("eq", "principal", json!({"var": "p"}))}}),
        )],
        1,
    );
    let store = Arc::new(HistoryStore::new());
    let history = store.new_history().unwrap();
    let alice = event(&store, "alice", "read", "doc");
    let bob = event(&store, "bob", "read", "doc");
    store.append(&history, &[alice; 3]).unwrap();
    let ready = Arc::new(Barrier::new(3));
    let appended = Arc::new(Barrier::new(3));
    let threads: Vec<_> = [alice, bob]
        .into_iter()
        .map(|request| {
            let store = store.clone();
            let history = history.clone();
            let program = program.clone();
            let ready = ready.clone();
            let appended = appended.clone();
            std::thread::spawn(move || {
                assert_eq!(event(&store, "alice", "read", "doc"), alice);
                let mut vm = RegoVM::new();
                vm.load_program(program);
                vm.set_execution_mode(ExecutionMode::Suspendable);
                vm.set_step_mode(true);
                vm.attach_history(store.clone()).unwrap();
                vm.set_history_input(history, request).unwrap();
                vm.execute_entry_point_by_name("decide").unwrap();
                assert_step(&vm, 0);
                ready.wait();
                appended.wait();
                let first = finish(&mut vm).unwrap();
                vm.set_step_mode(false);
                let fresh = vm.execute_entry_point_by_name("decide").unwrap();
                (request, first, fresh)
            })
        })
        .collect();
    ready.wait();
    store.append(&history, &[bob]).unwrap();
    appended.wait();
    for worker in threads {
        let (request, first, fresh) = worker.join().unwrap();
        assert_eq!(first, expected((request == bob).then_some(0)));
        assert_eq!(fresh, Value::from(0usize));
    }
    assert_eq!(store.len(&history).unwrap(), 4);
}

#[test]
fn mixed_program_captures_history_on_first_history_instruction() {
    let mut program = (*read_star(1)).clone();
    program.metadata.language = "mixed".into();
    program
        .instructions
        .insert(0, Instruction::LoadTrue { dest: 0 });
    program.instruction_spans.insert(0, None);
    let mut f = Fixture::new(&Arc::new(program), ExecutionMode::Suspendable);
    let read = event(&f.store, "alice", "read", "doc");
    let edit = event(&f.store, "alice", "edit", "doc");
    f.replace(&[read]);
    f.vm.set_step_mode(true);
    f.decide(read).unwrap();
    assert_step(&f.vm, 0);
    // No HISTORY_STEP has executed, so this append belongs to the captured prefix.
    f.store.append(&f.history, &[edit]).unwrap();
    assert_eq!(finish(&mut f.vm).unwrap(), Value::from(0usize));
}

#[cfg(feature = "std")]
#[test]
fn concurrent_rewrite_invalidates_both_pinned_decisions() {
    use std::sync::Barrier;
    let program = read_star(1);
    let store = Arc::new(HistoryStore::new());
    let history = store.new_history().unwrap();
    let read = event(&store, "alice", "read", "doc");
    store.append(&history, &[read; 3]).unwrap();
    let paused = Arc::new(Barrier::new(3));
    let rewritten = Arc::new(Barrier::new(3));
    let workers: Vec<_> = (0..2)
        .map(|_| {
            let store = store.clone();
            let history = history.clone();
            let program = program.clone();
            let paused = paused.clone();
            let rewritten = rewritten.clone();
            std::thread::spawn(move || {
                let mut vm = RegoVM::new();
                vm.load_program(program);
                vm.set_execution_mode(ExecutionMode::Suspendable);
                vm.set_step_mode(true);
                vm.attach_history(store).unwrap();
                vm.set_history_input(history, read).unwrap();
                vm.execute_entry_point_by_name("decide").unwrap();
                assert_step(&vm, 0);
                paused.wait();
                rewritten.wait();
                assert!(matches!(
                    finish(&mut vm),
                    Err(VmError::History {
                        source: HistoryError::HistoryChanged {
                            expected: 0,
                            actual: 1
                        },
                        ..
                    })
                ));
            })
        })
        .collect();
    paused.wait();
    store.truncate(&history, 0).unwrap();
    store.append(&history, &[read; 3]).unwrap();
    rewritten.wait();
    for worker in workers {
        worker.join().unwrap();
    }
}

#[test]
fn fixed_head_compares_all_three_exact_byte_identities() {
    let program = table(
        vec![rule(
            "require",
            json!({"object": {
                "principal": {"value": "alice/\0é"},
                "action": {"value": "edit"},
                "resource": {"value": "doc/é"}
            }}),
            json!({"empty": true}),
        )],
        256,
    );
    for mode in MODES {
        let mut f = Fixture::new(&program, mode);
        let exact = event(&f.store, "alice/\0é", "edit", "doc/é");
        let other_principal = event(&f.store, "alice/\0e\u{301}", "edit", "doc/é");
        let other_action = event(&f.store, "alice/\0é", "Edit", "doc/é");
        let other_resource = event(&f.store, "alice/\0é", "edit", "doc//é");
        assert_eq!(f.decide(exact).unwrap(), Value::from(0usize));
        for request in [other_principal, other_action, other_resource] {
            assert_eq!(f.decide(request).unwrap(), Value::Null);
        }
    }
}
