// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(all(feature = "rvm", feature = "history"))]

use history_semantics::CompiledRule;
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Event as _, Head, RegexExpr, Rule,
    RuleMode, TestExpr,
};
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use junco_core::limits::Unmetered;
use junco_core::observation::{fail_reservations_after, ObservationWorld};
use junco_core::reference::{head_matches, Lang};
use junco_core::{lower_flat, FlatEncoder};
use regorus::languages::history_table::{
    Event, HistoryError, HistoryHandle, HistoryStore, ACTION, PRINCIPAL, RESOURCE,
};
use regorus::languages::rego::compiler::{Compiler, CompilerError, HISTORY_BATCH_SIZE};
use regorus::rvm::program::{
    generate_assembly_listing, AssemblyListingConfig, DeserializationResult, Program,
};
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, SuspendReason, VmError};
use regorus::rvm::Instruction;
use regorus::{Engine, Value};
use serde_json::Value as Json;
use std::fmt::Write as _;
use std::sync::Arc;

const MODES: [ExecutionMode; 2] = [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable];
const BATCHES: [u32; 5] = [1, 2, 64, 256, 1024];
const ACTIONS: [&str; 4] = ["edit", "read", "release", "remove"];
const OWNED: [&str; 3] = ["edit", "release", "remove"];
const READ: [&str; 2] = ["read", "remove"];
type Sample = (usize, &'static str, usize);
/// History rule as Rego source: (`require` | `forbid`, request pattern, language).
type RuleSource = (&'static str, String, String);

fn event(store: &HistoryStore, principal: &str, action: &str, resource: &str) -> Event {
    store
        .event(&[
            store.intern(PRINCIPAL, principal).unwrap(),
            store.intern(ACTION, action).unwrap(),
            store.intern(RESOURCE, resource).unwrap(),
        ])
        .unwrap()
}

struct Fixture {
    store: Arc<HistoryStore>,
    history: HistoryHandle,
    vm: RegoVM,
    program: Arc<Program>,
    entry: &'static str,
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
        Self {
            store,
            history,
            vm,
            program: program.clone(),
            entry: "data.t.first",
        }
    }

    fn with_entry(mut self, entry: &'static str) -> Self {
        self.entry = entry;
        self
    }

    fn replace(&self, events: &[Event]) {
        self.store.truncate(&self.history, 0).unwrap();
        self.store.append(&self.history, events).unwrap();
    }

    fn decide(&mut self, request: Event) -> Result<Value, VmError> {
        self.vm.set_history_input(self.history.clone(), request)?;
        self.vm.execute_entry_point_by_name(self.entry)
    }

    fn run_to_history(&mut self) -> usize {
        run_to_history(&mut self.vm, &self.program)
    }
}

/// Compile a Rego module through the engine and the RVM compiler.
fn program(source: &str, entry_points: &[&str]) -> Arc<Program> {
    let mut engine = Engine::new();
    engine.add_policy("t.rego".into(), source.into()).unwrap();
    let policy = engine
        .compile_with_entrypoint(&entry_points[0].into())
        .unwrap();
    Compiler::compile_from_policy(&policy, entry_points).unwrap()
}

fn rule(mode: &'static str, request: &str, language: &str) -> RuleSource {
    (mode, request.into(), language.into())
}

/// Rules `r<i>`, `first` = least violated index (undefined when all hold), `allow` = all hold.
fn module(rules: &[RuleSource]) -> String {
    let mut source = String::from("package t\nimport rego.v1\n");
    for (index, (mode, request, language)) in rules.iter().enumerate() {
        writeln!(source, "r{index} := history.{mode}({request}, {language})").unwrap();
        writeln!(source, "violated contains {index} if not r{index}").unwrap();
    }
    source.push_str("first := min(violated)\nallow if {\n");
    for index in 0..rules.len() {
        writeln!(source, "    r{index}").unwrap();
    }
    source.push_str("}\n");
    source
}

fn table(rules: &[RuleSource], batch: u32) -> Arc<Program> {
    let rule_entries: Vec<String> = (0..rules.len()).map(|i| format!("data.t.r{i}")).collect();
    let mut entry_points = vec!["data.t.first", "data.t.allow"];
    entry_points.extend(rule_entries.iter().map(String::as_str));
    with_batch(&program(&module(rules), &entry_points), batch)
}

fn with_batch(program: &Arc<Program>, batch: u32) -> Arc<Program> {
    let mut program = (**program).clone();
    for params in &mut program.instruction_data.history_step_params {
        params.batch_size = batch;
    }
    Arc::new(program)
}

fn step_pc(program: &Program) -> usize {
    program
        .instructions
        .iter()
        .position(|instruction| matches!(instruction, Instruction::HistoryStep { .. }))
        .unwrap()
}

fn expected(index: Option<usize>) -> Value {
    index.map_or(Value::Undefined, Value::from)
}

fn prior_edit_rule(release: &str, edit: &str) -> RuleSource {
    rule(
        "require",
        &format!(r#"{{"action": "{release}", "principal": actor, "resource": doc}}"#),
        &format!(r#"[any, {{principal == actor, action == "{edit}", resource == doc}}, any]"#),
    )
}

#[test]
fn prior_edit_requires_same_principal_and_resource_without_appending_candidate() {
    let program = table(&[prior_edit_rule("release", "edit")], 256);
    for mode in MODES {
        let mut f = Fixture::new(&program, mode);
        let edit = event(&f.store, "alice", "edit", "doc");
        let release = event(&f.store, "alice", "release", "doc");
        let bob = event(&f.store, "bob", "release", "doc");
        let other = event(&f.store, "alice", "release", "other");
        assert_eq!(f.decide(release).unwrap(), Value::from(0usize));
        f.store.append(&f.history, &[edit]).unwrap();
        assert_eq!(f.decide(release).unwrap(), Value::Undefined);
        assert_eq!(f.decide(bob).unwrap(), Value::from(0usize));
        assert_eq!(f.decide(other).unwrap(), Value::from(0usize));
        assert_eq!(f.decide(edit).unwrap(), Value::Undefined);
        assert_eq!(f.store.len(&f.history).unwrap(), 1);
        // Ordinary repeated execution keeps the staged typed input.
        assert_eq!(
            f.vm.execute_entry_point_by_name("data.t.first").unwrap(),
            Value::Undefined
        );
    }
}

#[test]
fn cached_prefixes_preserve_history_revision_and_binding_semantics() {
    let program = table(&[prior_edit_rule("release", "edit")], 1);
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

#[test]
fn wrappers_share_histories_without_sharing_residuals() {
    let program = table(&[prior_edit_rule("release", "edit")], 1);
    for mode in MODES {
        let peer = Arc::new(HistoryStore::new());
        // The VM caches tables in its own wrapper; histories and requests come from `peer`.
        let mut f = Fixture::new(&program, mode);
        let alice_edit = event(&peer, "alice", "edit", "doc");
        let bob_edit = event(&peer, "bob", "edit", "doc");
        let alice_release = event(&peer, "alice", "release", "doc");
        let bob_release = event(&peer, "bob", "release", "doc");
        let other_release = event(&peer, "alice", "release", "other");
        let history = peer.new_history().unwrap();
        let interleaved = peer.new_history().unwrap();
        let mut decide = |history: &HistoryHandle, request: Event| {
            f.vm.set_history_input(history.clone(), request).unwrap();
            f.vm.execute_entry_point_by_name(f.entry).unwrap()
        };
        let deny = Value::from(0usize);
        assert_eq!(decide(&history, alice_release), deny);
        // Equal lengths, revisions and bindings: only the record key separates residuals.
        peer.append(&history, &[alice_edit]).unwrap();
        peer.append(&interleaved, &[bob_edit]).unwrap();
        for _ in 0..2 {
            assert_eq!(decide(&history, alice_release), Value::Undefined);
            assert_eq!(decide(&interleaved, alice_release), deny);
            assert_eq!(decide(&history, bob_release), deny);
            assert_eq!(decide(&interleaved, bob_release), Value::Undefined);
            assert_eq!(decide(&history, other_release), deny);
        }
        peer.truncate(&history, 0).unwrap();
        peer.append(&history, &[bob_edit]).unwrap();
        assert_eq!(decide(&history, alice_release), deny);
        assert_eq!(decide(&history, bob_release), Value::Undefined);
        assert_eq!(peer.len(&history).unwrap(), 1);
        assert_eq!(peer.len(&interleaved).unwrap(), 1);
    }
}

fn approval_rule() -> RuleSource {
    let no_edit = r#"star({resource != doc} | {action != "edit"})"#;
    rule(
        "require",
        r#"{"action": "release", "principal": actor, "resource": doc}"#,
        &format!(
            r#"[any, {{resource == doc, action == "edit", principal == actor}}, {no_edit}, {{resource == doc, action == "approve", principal != actor}}, {no_edit}]"#
        ),
    )
}

#[test]
fn approval_must_follow_edit_be_other_actor_and_not_be_stale() {
    let program = table(&[approval_rule()], 256);
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
        assert_eq!(f.decide(request).unwrap(), Value::Undefined);
    }
}

fn lock_rule(action: &str, setter: &str, changes: &[&str]) -> RuleSource {
    let unchanged = changes
        .iter()
        .map(|change| format!(r#"action != "{change}""#))
        .collect::<Vec<_>>()
        .join(", ");
    rule(
        "forbid",
        &format!(r#"{{"action": "{action}", "principal": p, "resource": r}}"#),
        &format!(
            r#"[any, {{resource == r, action == "{setter}", principal != p}}, star({{resource != r}} | {{{unchanged}}})]"#
        ),
    )
}

fn lock_table() -> Arc<Program> {
    table(
        &[
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
            &[rule("require", "{}", "false"), rule("forbid", "{}", "any")],
            256,
        ),
        table(
            &[
                rule("forbid", r#"{"action": "skip"}"#, "any"),
                rule("require", "{}", "false"),
                rule("forbid", "{}", "any"),
            ],
            256,
        ),
    ];
    for mode in MODES {
        for (index, program) in programs.iter().enumerate() {
            let mut f = Fixture::new(program, mode);
            let request = event(&f.store, "alice", "read", "doc");
            assert_eq!(f.decide(request).unwrap(), Value::from(index));
            f.entry = "data.t.allow";
            assert_eq!(f.decide(request).unwrap(), Value::Undefined);
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
const IDS: [&str; 3] = ["id0", "id1", "id2"];
const VARIABLES: [&str; 3] = ["p", "a", "r"];
const COORDINATES: [&str; 3] = ["principal", "action", "resource"];
const ORACLE_REQUEST: &str = r#"{"principal": p, "action": a, "resource": r}"#;

/// Borrowed-string event for the typed-semantics side of the oracle comparison.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct TestEvent<'a> {
    principal: &'a str,
    action: &'a str,
    resource: &'a str,
}

/// Tagged coordinate of a [`TestEvent`]; constants in rules carry their coordinate.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum TestComponent<'a> {
    Principal(&'a str),
    Action(&'a str),
    Resource(&'a str),
}

impl history_syntax::KeyHash for TestComponent<'_> {
    fn key_hash(&self) -> u64 {
        history_syntax::key_hash::hash_via_std(self)
    }
}

impl<'a> history_syntax::Event for TestEvent<'a> {
    type Component = TestComponent<'a>;
    type Arity = history_syntax::N3;

    fn component(self, index: usize) -> TestComponent<'a> {
        match index {
            0 => TestComponent::Principal(self.principal),
            1 => TestComponent::Action(self.action),
            _ => TestComponent::Resource(self.resource),
        }
    }

    fn coordinate(component: TestComponent<'a>) -> usize {
        match component {
            TestComponent::Principal(_) => 0,
            TestComponent::Action(_) => 1,
            TestComponent::Resource(_) => 2,
        }
    }
}

fn source_event(word: WordEvent) -> TestEvent<'static> {
    TestEvent {
        principal: IDS[word[0]],
        action: IDS[word[1]],
        resource: IDS[word[2]],
    }
}

fn join<T>(children: &[T], separator: &str, render: impl Fn(&T) -> String) -> String {
    children
        .iter()
        .map(render)
        .collect::<Vec<_>>()
        .join(separator)
}

impl Test {
    fn owned(&self) -> TestExpr<TestEvent<'static>> {
        match self {
            Self::Bool(true) => TestExpr::True,
            Self::Bool(false) => TestExpr::False,
            Self::Compare {
                field,
                unequal,
                variable,
                literal,
            } => {
                let pattern = if *variable {
                    ComponentPattern::variable(VARIABLES[*field])
                } else {
                    // Tag the constant with this coordinate through the authoring event.
                    ComponentPattern::constant(source_event([*literal; 3]).component(*field))
                };
                TestExpr::Atom {
                    comparison: if *unequal {
                        Comparison::Neq
                    } else {
                        Comparison::Eq
                    },
                    pattern: AtomPattern::new(Component(u8::try_from(*field).unwrap()), pattern),
                }
            }
            Self::And(children) => TestExpr::And(children.iter().map(Self::owned).collect()),
            Self::Or(children) => TestExpr::Or(children.iter().map(Self::owned).collect()),
        }
    }

    /// One-event tests become one-event languages: `∧` is `&`, `∨` is `|`.
    fn rego(&self) -> String {
        match self {
            Self::Bool(value) => value.to_string(),
            Self::Compare {
                field,
                unequal,
                variable,
                literal,
            } => {
                let term = if *variable {
                    VARIABLES[*field].to_string()
                } else {
                    format!("\"{}\"", IDS[*literal])
                };
                let op = if *unequal { "!=" } else { "==" };
                format!("{{{} {op} {term}}}", COORDINATES[*field])
            }
            Self::And(children) if children.is_empty() => "set()".into(),
            Self::And(children) => format!("({})", join(children, " & ", Self::rego)),
            Self::Or(children) if children.is_empty() => "false".into(),
            Self::Or(children) => format!("({})", join(children, " | ", Self::rego)),
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
}

impl Regex {
    fn owned(&self) -> RegexExpr<TestEvent<'static>> {
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

    /// Rego history expression; binary operators are always parenthesized.
    fn rego(&self) -> String {
        match self {
            Self::Empty => "false".into(),
            Self::All => "any".into(),
            Self::Epsilon => "[]".into(),
            Self::Test(test) => test.rego(),
            Self::Union(children) if children.is_empty() => "false".into(),
            Self::Union(children) => format!("({})", join(children, " | ", Self::rego)),
            Self::Concat(children) => format!("[{}]", join(children, ", ", Self::rego)),
            Self::Intersect(children) if children.is_empty() => "any".into(),
            Self::Intersect(children) => format!("({})", join(children, " & ", Self::rego)),
            Self::Star(inner) => format!("star({})", inner.rego()),
            Self::Not(inner) => format!("(any - {})", inner.rego()),
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

fn mode_name(mode: RuleMode) -> &'static str {
    match mode {
        RuleMode::Require => "require",
        RuleMode::Forbid => "forbid",
    }
}

fn oracle_head(action: Option<&'static str>) -> Head<TestEvent<'static>> {
    Head::new([
        ComponentPattern::variable("p"),
        action.map_or_else(
            || ComponentPattern::variable("a"),
            |action| ComponentPattern::constant(TestComponent::Action(action)),
        ),
        ComponentPattern::variable("r"),
    ])
}

/// Interns portable constants exactly as `RegoVM::attach_history` does.
struct StoreEncoder<'a>(&'a HistoryStore);

impl FlatEncoder<String> for StoreEncoder<'_> {
    fn encode(&mut self, field: Component, value: &String) -> Result<u64, HistoryError> {
        self.0.intern(field, value)
    }
}

/// Whether the rule holds according to the unverified `junco_core::reference` evaluator.
fn reference_holds(
    pair: &FlatPair<u64>,
    mode: RuleMode,
    request: &[u64],
    events: &[[u64; 3]],
) -> bool {
    if !head_matches(&pair.head, request) {
        return true;
    }
    let mut lang = Lang::inflate(pair, &mut Unmetered).unwrap();
    for event in events {
        lang = lang.step(pair, event, request, &mut Unmetered).unwrap();
    }
    lang.nullable() == (mode == RuleMode::Require)
}

#[test]
fn exhaustive_typed_words_match_split_oracle_and_concrete_derivatives() {
    let (corpus, alphabet, words) = oracle_corpus_and_words();
    let store = HistoryStore::new();
    let slots = [["id1"; 3], ["id2"; 3], ["id1", "id2", "id1"]].map(|[p, a, r]| {
        [
            store.intern(PRINCIPAL, p).unwrap(),
            store.intern(ACTION, a).unwrap(),
            store.intern(RESOURCE, r).unwrap(),
        ]
    });
    for regex in corpus {
        let base = table(&[rule("require", ORACLE_REQUEST, &regex.rego())], 256);
        let source = &base.history_tables[0].rules[0];
        let pair = lower_flat(
            &source.source,
            &mut StoreEncoder(&store),
            &mut Unmetered,
            &mut ObservationWorld,
        )
        .unwrap();
        for binding in [[1, 1, 1], [2, 2, 2]] {
            for word in &words {
                let events: Vec<_> = word
                    .iter()
                    .map(|e| slots[alphabet.iter().position(|a| a == e).unwrap()])
                    .collect();
                assert_eq!(
                    reference_holds(&pair, source.mode, &slots[binding[0] - 1], &events),
                    regex.accepts(word, &binding),
                    "reference evaluator: {regex:?} {word:?} {binding:?}"
                );
            }
        }
        for batch_size in BATCHES {
            let program = with_batch(&base, batch_size);
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
    compiled: &mut CompiledRule<TestEvent<'static>>,
    history: &History<TestEvent<'static>>,
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
                .accepts_history(history, &source_event(binding))
                .unwrap(),
            Some(inside),
            "typed semantics: {regex:?} {word:?} {binding:?} {mode:?}"
        );
        assert_eq!(
            fixture.decide(request).unwrap(),
            Value::Bool(!violation),
            "Rego history rule: {regex:?} {word:?} {binding:?} {mode:?}"
        );
        assert_eq!(fixture.store.len(&fixture.history).unwrap(), word.len());
        assert_eq!(history.len(), word.len());
    }
}

#[test]
fn typed_semantics_and_rego_history_rules_agree() {
    let (corpus, alphabet, words) = oracle_corpus_and_words();
    for regex in corpus {
        for rule_mode in [RuleMode::Require, RuleMode::Forbid] {
            let base = table(
                &[rule(mode_name(rule_mode), ORACLE_REQUEST, &regex.rego())],
                256,
            );
            for batch_size in BATCHES {
                let program = with_batch(&base, batch_size);
                for execution_mode in MODES {
                    // The rule's own Boolean: `first`/`allow` composition is covered elsewhere.
                    let mut fixture =
                        Fixture::new(&program, execution_mode).with_entry("data.t.r0");
                    let store = Arc::new(Store::new().unwrap());
                    let mut compiled = CompiledRule::new(
                        store.clone(),
                        Rule::new(rule_mode, oracle_head(None), regex.owned()),
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
                                history.push(source_event(*e)).unwrap();
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
                                history.push(source_event(alphabet[replacement])).unwrap();
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
        let base = table(
            &[rule(
                mode_name(rule_mode),
                &format!(
                    r#"{{"principal": p, "action": "{}", "resource": r}}"#,
                    IDS[1]
                ),
                &regex.rego(),
            )],
            256,
        );
        for batch_size in BATCHES {
            let program = with_batch(&base, batch_size);
            for execution_mode in MODES {
                let mut fixture = Fixture::new(&program, execution_mode);
                let store = Arc::new(Store::new().unwrap());
                let mut compiled = CompiledRule::new(
                    store.clone(),
                    Rule::new(rule_mode, oracle_head(Some(IDS[1])), regex.owned()),
                )
                .unwrap();
                let mut history = History::new(store).unwrap();
                for word in [vec![], vec![[1, 1, 1]]] {
                    fixture.replace(&[]);
                    history.truncate(0).unwrap();
                    for e in word {
                        history.push(source_event(e)).unwrap();
                        let recorded = event(&fixture.store, "id1", "id1", "id1");
                        fixture.store.append(&fixture.history, &[recorded]).unwrap();
                    }
                    let mismatch = event(&fixture.store, "id1", "id2", "id1");
                    for _ in 0..2 {
                        assert_eq!(
                            compiled
                                .accepts_history(&history, &source_event([1, 2, 1]))
                                .unwrap(),
                            None
                        );
                        assert_eq!(fixture.decide(mismatch).unwrap(), Value::Undefined);
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
    let base = table(&[rule("require", "{}", "[]")], 256);
    for batch_size in BATCHES {
        let mut program = (*with_batch(&base, batch_size)).clone();
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
                    assert_eq!(fixture.decide(probe).unwrap(), Value::Undefined);
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
            head: vec![FlatHead::Any, FlatHead::Any, FlatHead::Any],
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
            head: vec![FlatHead::Any, FlatHead::Any, FlatHead::Any],
            tests: vec![],
            regexes,
            root: 4095,
        },
        4096,
        4095,
    );
    assert_flat_epsilon_language(
        FlatPair {
            head: vec![FlatHead::Any, FlatHead::Any, FlatHead::Any],
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

fn read_star(batch_size: u32) -> Arc<Program> {
    table(
        &[rule("require", "{}", r#"star({action == "read"})"#)],
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

/// Step a suspended VM until it is about to dispatch a `HistoryStep`; returns that PC.
fn run_to_history(vm: &mut RegoVM, program: &Program) -> usize {
    loop {
        let pc = vm.get_pc();
        if matches!(
            program.instructions.get(pc),
            Some(Instruction::HistoryStep { .. })
        ) {
            assert_step(vm, pc);
            return pc;
        }
        vm.resume(None).unwrap();
    }
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
fn batch_edges_repeat_one_pc_and_charge_every_dispatch() {
    let program = read_star(3);
    assert_eq!(
        program
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::HistoryStep { .. }))
            .count(),
        1
    );
    let step = step_pc(&program);
    // Smallest instruction budget for a one-dispatch (empty-history) decision.
    let bases = MODES.map(|mode| {
        (1..)
            .find(|&limit| {
                let mut f = Fixture::new(&program, mode).with_entry("data.t.r0");
                let read = event(&f.store, "alice", "read", "doc");
                f.vm.set_max_instructions(limit);
                f.decide(read).is_ok()
            })
            .unwrap()
    });
    for len in [0usize, 1, 2, 3, 4, 6, 7] {
        let batches = len.div_ceil(3).max(1);
        let mut f = Fixture::new(&program, ExecutionMode::Suspendable).with_entry("data.t.r0");
        let read = event(&f.store, "alice", "read", "doc");
        f.replace(&vec![read; len]);
        f.vm.set_step_mode(true);
        f.decide(read).unwrap();
        assert_eq!(f.run_to_history(), step);
        for index in 0..batches {
            assert_step(&f.vm, step);
            if index + 1 < batches {
                f.vm.resume(None).unwrap();
            }
        }
        f.vm.resume(None).unwrap();
        assert_step(&f.vm, step + 1);
        assert_eq!(finish(&mut f.vm).unwrap(), Value::Bool(true));
        for (mode, base) in MODES.into_iter().zip(bases) {
            let mut limited = Fixture::new(&program, mode).with_entry("data.t.r0");
            let read = event(&limited.store, "alice", "read", "doc");
            limited.replace(&vec![read; len]);
            limited.vm.set_max_instructions(base + batches - 2);
            assert!(matches!(
                limited.decide(read),
                Err(VmError::InstructionLimitExceeded { .. })
            ));
            limited.vm.set_max_instructions(base + batches - 1);
            assert_eq!(limited.decide(read).unwrap(), Value::Bool(true));
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
            f.run_to_history();
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
    let step = f.run_to_history();
    // The first dispatch pins the decision's prefix.
    f.vm.resume(None).unwrap();
    assert_step(&f.vm, step);
    f.store.append(&f.history, &[edit]).unwrap();
    assert_eq!(finish(&mut f.vm).unwrap(), Value::Undefined);
    f.vm.set_step_mode(false);
    assert_eq!(f.decide(read).unwrap(), Value::from(0usize));
}

#[test]
fn newer_shared_cache_prefix_cannot_seed_an_older_decision_target() {
    let program = table(
        &[
            rule("require", "{}", "any"),
            rule("require", "{}", r#"star({action == "read"})"#),
        ],
        1,
    );
    let mut old = Fixture::new(&program, ExecutionMode::Suspendable);
    let read = event(&old.store, "alice", "read", "doc");
    let edit = event(&old.store, "alice", "edit", "doc");
    old.replace(&[read; 3]);
    old.vm.set_step_mode(true);
    old.decide(read).unwrap();
    old.run_to_history();
    // The first dispatch pins the decision's prefix.
    old.vm.resume(None).unwrap();
    old.store.append(&old.history, &[edit]).unwrap();
    let mut newer = RegoVM::new();
    newer.load_program(program);
    newer.attach_history(old.store.clone()).unwrap();
    newer.set_history_input(old.history.clone(), read).unwrap();
    assert_eq!(
        newer.execute_entry_point_by_name("data.t.first").unwrap(),
        Value::from(1usize)
    );
    assert_eq!(finish(&mut old.vm).unwrap(), Value::Undefined);
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
        f.run_to_history();
        // The first dispatch pins revision 0; later resumes finish the step and leave it.
        for _ in 0..resumes {
            f.vm.resume(None).unwrap();
        }
        assert_step(&f.vm, step_pc(&f.program) + usize::from(resumes == 2));
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
        assert_eq!(f.decide(read).unwrap(), Value::Undefined);
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
    assert_eq!(finish(&mut f.vm).unwrap(), Value::Undefined);
}

#[test]
fn load_program_cancels_suspension_and_drops_typed_context_not_shared_history() {
    let program = read_star(1);
    let mut f = Fixture::new(&program, ExecutionMode::Suspendable);
    let read = event(&f.store, "alice", "read", "doc");
    f.replace(&[read; 3]);
    let mut peer = RegoVM::new();
    peer.load_program(program.clone());
    peer.attach_history(f.store.clone()).unwrap();
    peer.set_history_input(f.history.clone(), read).unwrap();
    f.vm.set_step_mode(true);
    f.decide(read).unwrap();
    f.run_to_history();
    f.vm.resume(None).unwrap();
    f.vm.load_program(program);
    assert!(matches!(f.vm.execution_state(), ExecutionState::Ready));
    assert!(matches!(
        f.vm.resume(None),
        Err(VmError::InvalidResumeState { .. })
    ));
    f.vm.set_step_mode(false);
    assert!(matches!(
        f.vm.execute_entry_point_by_name("data.t.first"),
        Err(VmError::HistoryContextMissing { .. })
    ));
    f.vm.attach_history(f.store.clone()).unwrap();
    assert!(matches!(
        f.vm.execute_entry_point_by_name("data.t.first"),
        Err(VmError::HistoryContextMissing { .. })
    ));
    f.vm.set_history_input(f.history.clone(), read).unwrap();
    assert_eq!(
        f.vm.execute_entry_point_by_name("data.t.first").unwrap(),
        Value::Undefined
    );
    assert_eq!(f.store.len(&f.history).unwrap(), 3);
    assert_eq!(
        peer.execute_entry_point_by_name("data.t.first").unwrap(),
        Value::Undefined
    );
}

#[test]
fn staging_requires_attachment_and_each_domain_membership() {
    let program = read_star(256);
    let store = Arc::new(HistoryStore::new());
    let peer = Arc::new(HistoryStore::new());
    let history = peer.new_history().unwrap();
    let own = event(&peer, "alice", "read", "doc");
    // Typed views encode through dictionaries the byte domains never contain.
    let typed =
        History::from_events(Arc::new(Store::new().unwrap()), [source_event([0; 3])]).unwrap();
    let other = typed.numeric().as_slice()[0];
    let mut vm = RegoVM::new();
    vm.load_program(program);
    assert!(matches!(
        vm.set_history_input(history.clone(), own),
        Err(VmError::HistoryContextMissing { .. })
    ));
    vm.attach_history(store.clone()).unwrap();
    // Wrappers share one process-wide store, so a peer's handle and identities stage.
    vm.set_history_input(history.clone(), own).unwrap();
    // Event fields are private: each typed-only coordinate is rejected while building.
    for index in 0..3 {
        let mut slots = [own.component(0), own.component(1), own.component(2)];
        slots[index] = other.component(index);
        assert!(matches!(
            peer.event(&slots),
            Err(HistoryError::UnknownId {
                domain: "component",
                ..
            })
        ));
    }
    assert!(matches!(
        vm.set_history_input(history.clone(), other),
        Err(VmError::History {
            source: HistoryError::UnknownId {
                domain: "component",
                ..
            },
            ..
        })
    ));
    // Failed requests leave the previously staged input intact.
    assert_eq!(
        vm.execute_entry_point_by_name("data.t.first").unwrap(),
        Value::Undefined
    );
}

#[test]
fn zero_batch_is_rejected_before_head_mismatch_shortcut() {
    for mode in MODES {
        for matching in [false, true] {
            let request = if matching {
                r#"{"action": "read"}"#
            } else {
                r#"{"action": "release"}"#
            };
            let program = with_batch(&table(&[rule("require", request, "any")], 256), 0);
            assert!(program
                .validate_limits()
                .unwrap_err()
                .contains("zero batch_size"));
            let mut f = Fixture::new(&program, mode);
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
    // Compiled constants own their bytes after the policy source is gone.
    let program = {
        let (release, edit) = (String::from("release"), String::from("edit"));
        table(&[prior_edit_rule(&release, &edit)], 256)
    };
    let mut original = Fixture::new(&program, ExecutionMode::RunToCompletion);
    let old_edit = event(&original.store, "alice", "edit", "doc");
    let old_request = event(&original.store, "alice", "release", "doc");
    original.replace(&[old_edit]);
    assert_eq!(original.decide(old_request).unwrap(), Value::Undefined);
    let bytes = program.serialize_binary().unwrap();
    assert_eq!(Program::SERIALIZATION_VERSION, 7);
    assert_eq!(&bytes[4..8], &7u32.to_le_bytes());
    let DeserializationResult::Complete(binary) = Program::deserialize_binary(&bytes).unwrap()
    else {
        panic!("current version must deserialize completely");
    };
    let json_program = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
    for restored in [binary, json_program] {
        let store = Arc::new(HistoryStore::new());
        let edit = event(&store, "alice", "edit", "doc");
        let request = event(&store, "alice", "release", "doc");
        // Wrappers share process-wide identities: restored byte constants reintern to them.
        assert_eq!(edit, old_edit);
        assert_eq!(request, old_request);
        let mut f = Fixture::with_store(&Arc::new(restored), ExecutionMode::RunToCompletion, store);
        assert_eq!(f.decide(request).unwrap(), Value::from(0usize));
        f.replace(&[edit]);
        assert_eq!(f.decide(request).unwrap(), Value::Undefined);
        let other = event(&f.store, "bob", "release", "doc");
        assert_eq!(f.decide(other).unwrap(), Value::from(0usize));
    }
    assert_eq!(std::mem::size_of::<Instruction>(), 6);
}

/// `header`'s binary header and sections followed by `program`'s unchecked payload.
fn unchecked_binary(header: &Program, program: &Program) -> Vec<u8> {
    let mut bytes = header.serialize_binary().unwrap();
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
    let base = (*table(&[prior_edit_rule("release", "edit")], 256)).clone();
    let base_json: Json = serde_json::from_str(&base.serialize_json().unwrap()).unwrap();
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
        field: PRINCIPAL,
        term: FlatTerm::Variable(RESOURCE),
        positive: true,
    }];
    invalid.push(p);
    let mut p = base.clone();
    p.history_tables[0].rules[0].source.tests = vec![FlatTest::Atom {
        field: ACTION,
        term: FlatTerm::Variable(ACTION),
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
    let step = step_pc(&p);
    p.instructions[step] = Instruction::HistoryStep {
        params_index: u16::MAX,
    };
    invalid.push(p);
    let mut p = base.clone();
    p.instruction_data.history_step_params[0].batch_size = 0;
    invalid.push(p);
    for program in invalid {
        assert!(program.validate_limits().is_err());
        assert!(program.serialize_binary().is_err());
        let mut serialized = base_json.clone();
        serialized["history_tables"] = serde_json::to_value(&program.history_tables).unwrap();
        serialized["instructions"] = serde_json::to_value(&program.instructions).unwrap();
        serialized["instruction_data"] = serde_json::to_value(&program.instruction_data).unwrap();
        assert!(Program::deserialize_json(&serialized.to_string()).is_err());
        assert!(!matches!(
            Program::deserialize_binary(&unchecked_binary(&base, &program)),
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
                vm.execute_entry_point_by_name("data.t.first"),
                Err(VmError::InvalidHistoryStepParams { .. }
                    | VmError::InvalidHistoryTableIndex { .. }
                    | VmError::InvalidHistoryRuleIndex { .. }
                    | VmError::InvalidHistoryBatchSize { .. })
            ));
        }
    }
}

/// Compile `r0 := history.<call>` and return the RVM compiler's error message.
fn history_rule_error(call: &str) -> String {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "t.rego".into(),
            format!("package t\nimport rego.v1\nr0 := history.{call}\n"),
        )
        .unwrap();
    let policy = engine.compile_with_entrypoint(&"data.t.r0".into()).unwrap();
    Compiler::compile_from_policy(&policy, &["data.t.r0"])
        .unwrap_err()
        .to_string()
}

#[test]
fn malformed_history_rules_report_compile_errors() {
    for (call, message) in [
        (
            r#"require({"actor": a}, any)"#,
            "request pattern must be an object",
        ),
        (r#"require([], any)"#, "request pattern must be an object"),
        (
            r#"require({"action": "a", "action": "b"}, any)"#,
            "duplicate request coordinate",
        ),
        (
            r#"require({"principal": action}, any)"#,
            "shadows the coordinate name",
        ),
        (
            r#"require({"principal": 1}, any)"#,
            "must be a string constant or a variable",
        ),
        (
            r#"require({}, [any, {action < "x"}])"#,
            "comparison must be",
        ),
        (
            r#"require({}, [any, {"edit" == action}])"#,
            "comparison must be",
        ),
        (
            r#"require({}, [any, {"action": "edit"}, any])"#,
            "unsupported history expression",
        ),
        (r#"require({}, everything)"#, "unknown name `everything`"),
        (r#"require({}, star())"#, "star takes one argument"),
        (r#"require({})"#, "take two arguments"),
        (r#"forbid({}, any, any)"#, "take two arguments"),
        (
            r#"require({}, {principal == any})"#,
            "comparison term must be",
        ),
        (
            r#"require({}, {principal == action})"#,
            "comparison term must be",
        ),
        (
            r#"require({"action": "release", "principal": x}, {resource == x})"#,
            "invalid history rule",
        ),
        (
            r#"require({}, {principal == missing})"#,
            "invalid history rule",
        ),
    ] {
        let error = history_rule_error(call);
        assert!(error.contains(message), "{call}: {error}");
    }

    // A failed reservation leaves nothing behind: the same source then compiles and decides.
    let rule = prior_edit_rule("release", "edit");
    let call = format!("require({}, {})", rule.1, rule.2);
    let failing = fail_reservations_after(0);
    let error = history_rule_error(&call);
    assert!(error.contains("invalid history rule"), "{error}");
    drop(failing);
    let mut f = Fixture::new(&table(&[rule], 256), ExecutionMode::RunToCompletion);
    let edit = event(&f.store, "alice", "edit", "doc");
    let release = event(&f.store, "alice", "release", "doc");
    assert_eq!(f.decide(release).unwrap(), Value::from(0usize));
    f.replace(&[edit]);
    assert_eq!(f.decide(release).unwrap(), Value::Undefined);
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
    let error = Compiler::compile_from_policy(&policy, &["data.removed.result"]).unwrap_err();
    assert!(matches!(error.error,
        CompilerError::UnknownFunction { ref name }
        if name == "history.match"));
}

#[cfg(feature = "std")]
#[test]
fn concurrent_vms_share_identities_and_fixed_prefix_without_sharing_candidates() {
    use std::sync::Barrier;
    let program = table(
        &[rule(
            "require",
            r#"{"principal": p}"#,
            "star({principal == p})",
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
                vm.load_program(program.clone());
                vm.set_execution_mode(ExecutionMode::Suspendable);
                vm.set_step_mode(true);
                vm.attach_history(store.clone()).unwrap();
                vm.set_history_input(history, request).unwrap();
                vm.execute_entry_point_by_name("data.t.first").unwrap();
                run_to_history(&mut vm, &program);
                // The first dispatch pins the decision's prefix.
                vm.resume(None).unwrap();
                ready.wait();
                appended.wait();
                let first = finish(&mut vm).unwrap();
                vm.set_step_mode(false);
                let fresh = vm.execute_entry_point_by_name("data.t.first").unwrap();
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
fn decision_captures_history_at_its_first_history_step() {
    let mut f = Fixture::new(&read_star(1), ExecutionMode::Suspendable);
    let read = event(&f.store, "alice", "read", "doc");
    let edit = event(&f.store, "alice", "edit", "doc");
    f.replace(&[read]);
    f.vm.set_step_mode(true);
    f.decide(read).unwrap();
    // Stop on the RuleInit just before the first HistoryStep: ordinary Rego
    // instructions ran, no history dispatch has, so this append is captured.
    while !matches!(
        f.program.instructions.get(f.vm.get_pc() + 1),
        Some(Instruction::HistoryStep { .. })
    ) {
        f.vm.resume(None).unwrap();
    }
    assert!(matches!(
        f.program.instructions.get(f.vm.get_pc()),
        Some(Instruction::RuleInit { .. })
    ));
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
                vm.load_program(program.clone());
                vm.set_execution_mode(ExecutionMode::Suspendable);
                vm.set_step_mode(true);
                vm.attach_history(store).unwrap();
                vm.set_history_input(history, read).unwrap();
                vm.execute_entry_point_by_name("data.t.first").unwrap();
                run_to_history(&mut vm, &program);
                // The first dispatch pins revision 0.
                vm.resume(None).unwrap();
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
        &[rule(
            "require",
            r#"{"principal": "alice/\u0000é", "action": "edit", "resource": "doc/é"}"#,
            "false",
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
            assert_eq!(f.decide(request).unwrap(), Value::Undefined);
        }
    }
}

/// The policy shown in `docs/builtins.md`.
const APPROVALS: &str = r#"package approvals
import rego.v1

# require: deny when the committed history is outside the language.
edit_before_release := history.require(
    {"action": "release", "principal": actor, "resource": doc},
    [any, {action == "edit", principal == actor, resource == doc}, any],
)
# forbid: deny when the committed history is inside the language.
never_remove_locked := history.forbid({"action": "remove", "resource": doc}, [any, {action == "lock", resource == doc}, any])
approve_by_other := history.require(
    {"action": "approve", "principal": approver, "resource": doc},
    [any, {action == "submit", resource == doc, principal != approver}, any],
)
first_action_is_create := history.require({"action": "create"}, [])          # history must be empty
only_reads_so_far := history.require({"action": "audit"}, star({action == "read"}))

allow if {
    edit_before_release
    never_remove_locked
    approve_by_other
}
deny contains "release requires a prior edit by the same actor" if not edit_before_release
deny contains "locked resources cannot be removed" if not never_remove_locked
"#;

fn approvals_program() -> Arc<Program> {
    let mut engine = Engine::new();
    engine
        .add_policy("approvals.rego".into(), APPROVALS.into())
        .unwrap();
    let entries = [
        "data.approvals.allow",
        "data.approvals.deny",
        "data.approvals.approve_by_other",
        "data.approvals.first_action_is_create",
        "data.approvals.only_reads_so_far",
    ];
    let policy = engine.compile_with_entrypoint(&entries[0].into()).unwrap();
    Compiler::compile_from_policy(&policy, &entries).unwrap()
}

fn assert_approvals(program: &Arc<Program>, mode: ExecutionMode) {
    let store = Arc::new(HistoryStore::new());
    let history = store.new_history().unwrap();
    let e = |principal, action| event(&store, principal, action, "doc");
    let mut vm = RegoVM::new();
    vm.load_program(program.clone());
    vm.set_execution_mode(mode);
    vm.attach_history(store.clone()).unwrap();
    let mut eval = |events: &[Event], request: Event, rule: &str| {
        store.truncate(&history, 0).unwrap();
        store.append(&history, events).unwrap();
        vm.set_history_input(history.clone(), request).unwrap();
        vm.execute_entry_point_by_name(&format!("data.approvals.{rule}"))
            .unwrap()
    };
    let messages = |value: Value| -> Vec<String> {
        value
            .as_set()
            .unwrap()
            .iter()
            .map(|message| message.as_string().unwrap().to_string())
            .collect()
    };
    let (alice_release, alice_edit) = (e("alice", "release"), e("alice", "edit"));
    assert_eq!(
        eval(&[alice_edit], alice_release, "allow"),
        Value::Bool(true)
    );
    assert!(messages(eval(&[alice_edit], alice_release, "deny")).is_empty());
    let bob_edit = e("bob", "edit");
    assert_eq!(eval(&[bob_edit], alice_release, "allow"), Value::Undefined);
    assert_eq!(
        messages(eval(&[bob_edit], alice_release, "deny")),
        ["release requires a prior edit by the same actor"]
    );
    let (lock, remove) = (e("alice", "lock"), e("alice", "remove"));
    assert_eq!(eval(&[lock], remove, "allow"), Value::Undefined);
    assert_eq!(
        messages(eval(&[lock], remove, "deny")),
        ["locked resources cannot be removed"]
    );
    let submit = e("alice", "submit");
    assert_eq!(
        eval(&[submit], e("bob", "approve"), "approve_by_other"),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&[submit], e("alice", "approve"), "approve_by_other"),
        Value::Bool(false)
    );
    let (create, read) = (e("alice", "create"), e("alice", "read"));
    assert_eq!(
        eval(&[], create, "first_action_is_create"),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&[read], create, "first_action_is_create"),
        Value::Bool(false)
    );
    let audit = e("alice", "audit");
    assert_eq!(
        eval(&[read, read], audit, "only_reads_so_far"),
        Value::Bool(true)
    );
    assert_eq!(
        eval(&[read, alice_edit], audit, "only_reads_so_far"),
        Value::Bool(false)
    );
    // Longer than one batch: the step repeats inside the rule frame.
    let long = vec![alice_edit; 600];
    assert_eq!(eval(&long, alice_release, "allow"), Value::Bool(true));
}

#[test]
fn rego_history_rules_compose_with_ordinary_rules_in_both_modes() {
    let program = approvals_program();
    assert_eq!(program.history_tables.len(), 1);
    assert_eq!(program.history_tables[0].rules.len(), 5);
    let steps = &program.instruction_data.history_step_params;
    assert_eq!(steps.len(), 5);
    assert!(steps
        .iter()
        .all(|step| step.batch_size == HISTORY_BATCH_SIZE));
    let listing = generate_assembly_listing(&program, &AssemblyListingConfig::default());
    assert!(
        listing.contains("HistoryStep table[0].rule[0] batch_size=256 dest=r1"),
        "{listing}"
    );
    let DeserializationResult::Complete(restored) =
        Program::deserialize_binary(&program.serialize_binary().unwrap()).unwrap()
    else {
        panic!("current version must deserialize completely");
    };
    let restored = Arc::new(restored);
    for mode in MODES {
        assert_approvals(&program, mode);
        assert_approvals(&restored, mode);
        // Without a staged request the first history rule fails.
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.attach_history(Arc::new(HistoryStore::new())).unwrap();
        assert!(matches!(
            vm.execute_entry_point_by_name("data.approvals.allow"),
            Err(VmError::HistoryContextMissing { .. })
        ));
    }
    // History rules are RVM-only.
    let mut engine = Engine::new();
    engine
        .add_policy("approvals.rego".into(), APPROVALS.into())
        .unwrap();
    assert!(engine.eval_rule("data.approvals.allow".into()).is_err());
}

const PRIOR_EDIT_REQUEST: &str = r#"{"action": "release", "principal": actor, "resource": doc}"#;
const PRIOR_EDIT_LANGUAGE: &str =
    r#"[any, {principal == actor, action == "edit", resource == doc}, any]"#;

fn rego_module(body: &str) -> String {
    format!("package t\nimport rego.v1\n{body}")
}

fn prior_edit_source() -> FlatPair<String> {
    FlatPair {
        head: vec![
            FlatHead::Bind,
            FlatHead::Constant("release".to_owned()),
            FlatHead::Bind,
        ],
        tests: vec![
            FlatTest::Atom {
                field: Component(0),
                term: FlatTerm::Variable(Component(0)),
                positive: true,
            },
            FlatTest::Atom {
                field: Component(1),
                term: FlatTerm::Constant("edit".to_owned()),
                positive: true,
            },
            FlatTest::Atom {
                field: Component(2),
                term: FlatTerm::Variable(Component(2)),
                positive: true,
            },
            FlatTest::And(vec![0, 1, 2]),
        ],
        regexes: vec![
            FlatRegex::All,
            FlatRegex::Test(3),
            FlatRegex::All,
            FlatRegex::Concat(vec![0, 1, 2]),
        ],
        root: 3,
    }
}

fn history_steps(program: &Program) -> usize {
    program
        .instructions
        .iter()
        .filter(|instruction| matches!(instruction, Instruction::HistoryStep { .. }))
        .count()
}

/// A `require` row followed by a `forbid` row.
fn two_rules() -> Arc<Program> {
    program(
        &rego_module(&format!(
            "r0 := history.require({PRIOR_EDIT_REQUEST}, {PRIOR_EDIT_LANGUAGE})\n\
             r1 := history.forbid({{\"principal\": p}}, star({{principal == p}}))\n"
        )),
        &["data.t.r0", "data.t.r1"],
    )
}

#[test]
fn rego_history_rules_lower_to_one_table_and_history_step() {
    let program = program(
        &rego_module(&format!(
            "r0 := history.require({PRIOR_EDIT_REQUEST}, {PRIOR_EDIT_LANGUAGE})\n"
        )),
        &["data.t.r0"],
    );
    assert_eq!(program.history_tables.len(), 1);
    let rules = &program.history_tables[0].rules;
    assert_eq!(rules.len(), 1);
    assert_eq!(rules[0].mode, RuleMode::Require);
    assert_eq!(rules[0].source, prior_edit_source());
    let steps = &program.instruction_data.history_step_params;
    assert_eq!(steps.len(), 1);
    assert_eq!(
        (steps[0].table, steps[0].rule, steps[0].batch_size),
        (0, 0, HISTORY_BATCH_SIZE)
    );
    assert_eq!(history_steps(&program), 1);
    let listing = generate_assembly_listing(&program, &AssemblyListingConfig::default());
    assert!(
        listing.contains(&format!(
            "HistoryStep table[0].rule[0] batch_size={HISTORY_BATCH_SIZE} dest=r{}",
            steps[0].dest
        )),
        "{listing}"
    );

    // Each call adds one ordered row to the same table and one step instruction.
    let program = two_rules();
    assert_eq!(program.history_tables.len(), 1);
    let modes: Vec<_> = program.history_tables[0]
        .rules
        .iter()
        .map(|rule| rule.mode)
        .collect();
    assert_eq!(modes, [RuleMode::Require, RuleMode::Forbid]);
    let rows: Vec<_> = program
        .instruction_data
        .history_step_params
        .iter()
        .map(|step| (step.table, step.rule))
        .collect();
    assert_eq!(rows, [(0, 0), (0, 1)]);
    assert_eq!(history_steps(&program), 2);
}

#[test]
fn compiled_programs_roundtrip_history_tables() {
    let program = two_rules();
    let DeserializationResult::Complete(binary) =
        Program::deserialize_binary(&program.serialize_binary().unwrap()).unwrap()
    else {
        panic!("current version must deserialize completely");
    };
    let json = Program::deserialize_json(&program.serialize_json().unwrap()).unwrap();
    for restored in [binary, json] {
        assert_eq!(restored.history_tables.len(), 1);
        for (restored, original) in restored.history_tables[0]
            .rules
            .iter()
            .zip(&program.history_tables[0].rules)
        {
            assert_eq!(restored.mode, original.mode);
            assert_eq!(restored.source, original.source);
        }
        let steps = |program: &Program| -> Vec<_> {
            program
                .instruction_data
                .history_step_params
                .iter()
                .map(|step| (step.table, step.rule, step.batch_size, step.dest))
                .collect()
        };
        assert_eq!(steps(&restored), steps(&program));
        assert_eq!(restored.instructions.len(), program.instructions.len());
        assert_eq!(history_steps(&restored), 2);
    }
}
