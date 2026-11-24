// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Events delivered to an `ExplanationRecorder` by the RVM, in both
//! execution modes.

#![cfg(feature = "explanations")]

use anyhow::{bail, Result};
use regorus::explain::{
    BodyEndEvent, BuiltinErrorEvent, CallEndEvent, CallResultSource, CallReusedEvent,
    CallStartEvent, CheckEvent, CheckSite, ComprehensionElement, ComprehensionEmissionEvent,
    ConditionKind, EmissionEvent, ExplanationRecorder, HookContext, NotCapturedEvent, Operator,
    Outcome, Provenance, UncapturedConstruct,
};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::instructions::FunctionCallParams;
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::rvm::Instruction;
use regorus::{Engine, Rc, Value};
use std::sync::{Arc, Mutex};

const MODES: [ExecutionMode; 2] = [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable];

#[derive(Debug, Clone, PartialEq)]
enum Event {
    Reset,
    Check {
        kind: ConditionKind,
        operator: Option<Operator>,
        left: Value,
        right: Option<Value>,
        outcome: Outcome,
    },
    BodyEnd {
        outcome: Outcome,
        result: Option<Value>,
    },
    Emission {
        key: Option<Value>,
        value: Value,
    },
    ComprehensionEmission {
        begin_pc: usize,
        kind: &'static str,
        key: Option<Value>,
        value: Value,
    },
    BuiltinError {
        name: String,
        message: String,
        raised: bool,
    },
    NotCaptured(UncapturedConstruct),
}

#[derive(Debug, Clone)]
struct Recorded {
    context: Option<HookContext>,
    event: Event,
}

#[derive(Clone, Default)]
struct Fixture(Arc<Mutex<Vec<Recorded>>>, Arc<Mutex<Vec<CallRecord>>>);

#[derive(Debug, Clone, PartialEq)]
enum CallRecord {
    Start(HookContext, CallStartEvent),
    End(HookContext, Option<CallResultSource>, Option<Value>),
    Reused(HookContext, CallReusedEvent),
}

impl Fixture {
    fn push(&self, context: Option<&HookContext>, event: Event) {
        self.0.lock().unwrap().push(Recorded {
            context: context.copied(),
            event,
        });
    }

    fn take(&self) -> Vec<Recorded> {
        std::mem::take(&mut *self.0.lock().unwrap())
    }

    fn calls(&self) -> Vec<CallRecord> {
        std::mem::take(&mut *self.1.lock().unwrap())
    }
}

impl ExplanationRecorder for Fixture {
    fn reset(&mut self) {
        self.push(None, Event::Reset);
    }

    fn call_start(&mut self, context: &HookContext, event: &CallStartEvent) {
        self.1
            .lock()
            .unwrap()
            .push(CallRecord::Start(*context, *event));
    }

    fn call_end(&mut self, context: &HookContext, event: &CallEndEvent<'_>) {
        self.1.lock().unwrap().push(CallRecord::End(
            *context,
            event.source,
            event.result.cloned(),
        ));
    }

    fn call_reused(&mut self, context: &HookContext, event: &CallReusedEvent) {
        self.1
            .lock()
            .unwrap()
            .push(CallRecord::Reused(*context, *event));
    }

    fn check(&mut self, context: &HookContext, event: &CheckEvent<'_>) {
        self.push(
            Some(context),
            Event::Check {
                kind: event.kind,
                operator: event.operator,
                left: event.left.clone(),
                right: event.right.cloned(),
                outcome: event.outcome,
            },
        );
    }

    fn body_end(&mut self, context: &HookContext, event: &BodyEndEvent<'_>) {
        self.push(
            Some(context),
            Event::BodyEnd {
                outcome: event.outcome,
                result: event.result.cloned(),
            },
        );
    }

    fn emission(&mut self, context: &HookContext, event: &EmissionEvent<'_>) {
        self.push(
            Some(context),
            Event::Emission {
                key: event.key.cloned(),
                value: event.value.clone(),
            },
        );
    }

    fn builtin_error(&mut self, context: &HookContext, event: &BuiltinErrorEvent<'_>) {
        self.push(
            Some(context),
            Event::BuiltinError {
                name: event.name.to_string(),
                message: event.message.to_string(),
                raised: event.raised,
            },
        );
    }

    fn comprehension_emission(
        &mut self,
        context: &HookContext,
        event: &ComprehensionEmissionEvent<'_>,
    ) {
        let (kind, key, value) = match event.element {
            ComprehensionElement::Array(value) => ("array", None, value),
            ComprehensionElement::Set(value) => ("set", None, value),
            ComprehensionElement::Object { key, value } => ("object", Some(key.clone()), value),
            _ => panic!("unexpected comprehension element: {:?}", event.element),
        };
        self.push(
            Some(context),
            Event::ComprehensionEmission {
                begin_pc: event.begin_pc,
                kind,
                key,
                value: value.clone(),
            },
        );
    }

    fn not_captured(&mut self, context: &HookContext, event: &NotCapturedEvent) {
        self.push(Some(context), Event::NotCaptured(event.construct));
    }
}

struct Run {
    result: Result<Value>,
    events: Vec<Recorded>,
    program: Arc<Program>,
    calls: Vec<CallRecord>,
}

fn compile(policy: &str, query: &str) -> Result<Arc<Program>> {
    let mut engine = Engine::new();
    engine.add_policy("test.rego".to_string(), policy.to_string())?;
    let entrypoint: Rc<str> = query.into();
    let compiled = engine.compile_with_entrypoint(&entrypoint)?;
    Ok(Compiler::compile_from_policy(&compiled, &[query])?)
}

fn execute(vm: &mut RegoVM, mode: ExecutionMode) -> Result<Value> {
    let result = vm.execute();
    if mode == ExecutionMode::RunToCompletion {
        return Ok(result?);
    }
    result?;
    match vm.execution_state() {
        ExecutionState::Completed { result } => Ok(result.clone()),
        ExecutionState::Error { error } => bail!("{error}"),
        other => bail!("suspendable execution did not complete: {other:?}"),
    }
}

fn run_program(program: &Arc<Program>, input: &str, mode: ExecutionMode, strict: bool) -> Run {
    let fixture = Fixture::default();
    let mut vm = RegoVM::new();
    vm.load_program(program.clone());
    vm.set_strict_builtin_errors(strict);
    vm.set_input(Value::from_json_str(input).unwrap());
    vm.set_execution_mode(mode);
    vm.set_explanation_recorder(Box::new(fixture.clone()));
    let result = execute(&mut vm, mode);
    Run {
        result,
        events: fixture.take(),
        program: program.clone(),
        calls: fixture.calls(),
    }
}

/// Runs `query` in both modes, checks that both deliver the same events and
/// result, and returns the run-to-completion run.
fn run_with(policy: &str, query: &str, input: &str, strict: bool) -> Run {
    let program = compile(policy, query).unwrap();
    let [first, second] = MODES.map(|mode| run_program(&program, input, mode, strict));
    let strip = |run: &Run| -> Vec<(Option<HookContext>, Event)> {
        run.events
            .iter()
            .map(|r| (r.context, r.event.clone()))
            .collect()
    };
    assert_eq!(strip(&first), strip(&second), "modes disagree");
    assert_eq!(first.calls, second.calls, "invocation events disagree");
    assert_eq!(
        format!("{:?}", first.result),
        format!("{:?}", second.result),
        "modes disagree on the result"
    );
    first
}

fn run(policy: &str, query: &str, input: &str) -> Run {
    run_with(policy, query, input, false)
}

impl Run {
    fn call_ids(&self, name: &str) -> Vec<u64> {
        self.calls
            .iter()
            .filter_map(|record| match record {
                CallRecord::Start(_, event)
                    if self.program.rule_infos[usize::from(event.rule_index)].name == name =>
                {
                    Some(event.call_instance)
                }
                _ => None,
            })
            .collect()
    }

    fn call_end(&self, id: u64) -> (Option<CallResultSource>, Option<Value>) {
        self.calls
            .iter()
            .find_map(|record| match record {
                CallRecord::End(context, source, value) if context.call_instance == Some(id) => {
                    Some((*source, value.clone()))
                }
                _ => None,
            })
            .unwrap()
    }

    fn events(&self) -> Vec<Event> {
        self.events.iter().map(|r| r.event.clone()).collect()
    }

    fn contexts(&self) -> Vec<HookContext> {
        self.events.iter().filter_map(|r| r.context).collect()
    }

    fn instruction(&self, context: &HookContext) -> Instruction {
        self.program.instructions[context.pc]
    }
}

fn v(json: &str) -> Value {
    Value::from_json_str(json).unwrap()
}

fn check(
    kind: ConditionKind,
    operator: Option<Operator>,
    left: &str,
    right: Option<&str>,
    outcome: Outcome,
) -> Event {
    Event::Check {
        kind,
        operator,
        left: v(left),
        right: right.map(v),
        outcome,
    }
}

fn compare(operator: Operator, left: &str, right: &str, outcome: Outcome) -> Event {
    check(
        ConditionKind::Comparison,
        Some(operator),
        left,
        Some(right),
        outcome,
    )
}

fn unary(kind: ConditionKind, value: Value, outcome: Outcome) -> Event {
    Event::Check {
        kind,
        operator: None,
        left: value,
        right: None,
        outcome,
    }
}

fn body_end(outcome: Outcome, result: Option<&str>) -> Event {
    Event::BodyEnd {
        outcome,
        result: result.map(v),
    }
}

use ConditionKind::{Iteration, Membership, Negation, Truthiness};
use Outcome::{Failure, Success, Undefined};

#[test]
fn comparisons_report_operator_and_operands() {
    let policy = "package t\nallow if { input.role == \"admin\"; input.level > 3 }\n";
    let r = run(policy, "data.t.allow", r#"{"role":"admin","level":5}"#);
    assert_eq!(r.result.as_ref().unwrap(), &Value::from(true));
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Eq, r#""admin""#, r#""admin""#, Success),
            compare(Operator::Gt, "5", "3", Success),
            body_end(Success, Some("true")),
        ]
    );
    for context in r.contexts() {
        assert_eq!(context.rule_index, Some(0));
        assert_eq!(context.call_depth, 1);
        assert!(!context.in_comprehension);
    }
    let guard = r.contexts()[0];
    assert!(matches!(r.instruction(&guard), Instruction::Guard { .. }));

    let r = run(policy, "data.t.allow", r#"{"role":"admin","level":2}"#);
    assert_eq!(r.result.as_ref().unwrap(), &Value::Undefined);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Eq, r#""admin""#, r#""admin""#, Success),
            compare(Operator::Gt, "2", "3", Failure),
            body_end(Failure, None),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"level":5}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            Event::Check {
                kind: ConditionKind::Comparison,
                operator: Some(Operator::Eq),
                left: Value::Undefined,
                right: Some(v(r#""admin""#)),
                outcome: Undefined,
            },
            body_end(Failure, None),
        ]
    );
}

#[test]
fn every_comparison_operator_is_decoded() {
    let policy = "package t\nallow if { input.a != 1; input.a < 3; input.a <= 2; input.a >= 2 }\n";
    let r = run(policy, "data.t.allow", r#"{"a":2}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Ne, "2", "1", Success),
            compare(Operator::Lt, "2", "3", Success),
            compare(Operator::Le, "2", "2", Success),
            compare(Operator::Ge, "2", "2", Success),
            body_end(Success, Some("true")),
        ]
    );
}

#[test]
fn membership_and_truthiness() {
    let policy = "package t\nallow if { \"x\" in input.tags; input.flag }\n";
    let r = run(policy, "data.t.allow", r#"{"tags":["x"],"flag":true}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            check(
                Membership,
                Some(Operator::In),
                r#""x""#,
                Some(r#"["x"]"#),
                Success
            ),
            unary(Truthiness, Value::from(true), Success),
            body_end(Success, Some("true")),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"tags":["y"],"flag":true}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            check(
                Membership,
                Some(Operator::In),
                r#""x""#,
                Some(r#"["y"]"#),
                Failure
            ),
            body_end(Failure, None),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"tags":["x"],"flag":false}"#);
    assert_eq!(
        r.events()[2],
        unary(Truthiness, Value::from(false), Failure)
    );
    let r = run(policy, "data.t.allow", r#"{"tags":["x"]}"#);
    assert_eq!(
        r.events()[2],
        unary(Truthiness, Value::Undefined, Undefined)
    );
}

#[test]
fn negation_reports_the_negated_expression() {
    let policy = "package t\nallow if { not input.blocked; not input.n == 1 }\n";
    let r = run(policy, "data.t.allow", r#"{"n":2}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Negation, Value::Undefined, Success),
            check(Negation, Some(Operator::Eq), "2", Some("1"), Success),
            body_end(Success, Some("true")),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"blocked":false,"n":1}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Negation, Value::from(false), Success),
            check(Negation, Some(Operator::Eq), "1", Some("1"), Failure),
            body_end(Failure, None),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"blocked":true}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Negation, Value::from(true), Failure),
            body_end(Failure, None),
        ]
    );
}

#[test]
fn every_reports_iterations_then_the_quantifier() {
    let policy = "package t\nallow if { every x in input.xs { x > 0 } }\n";
    let r = run(policy, "data.t.allow", r#"{"xs":[1,2]}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Gt, "1", "0", Success),
            compare(Operator::Gt, "2", "0", Success),
            unary(Iteration, v("[1,2]"), Success),
            body_end(Success, Some("true")),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"xs":[1,-2,3]}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Gt, "1", "0", Success),
            compare(Operator::Gt, "-2", "0", Failure),
            unary(Iteration, v("[1,-2,3]"), Failure),
            body_end(Failure, None),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"xs":[]}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Iteration, v("[]"), Success),
            body_end(Success, Some("true")),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Iteration, Value::Undefined, Undefined),
            body_end(Failure, None),
        ]
    );
}

#[test]
fn bindings_are_not_reported_as_checks() {
    let policy = "package t\nallow if { x := input.a; x == 1 }\n";
    let r = run(policy, "data.t.allow", r#"{"a":1}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Eq, "1", "1", Success),
            body_end(Success, Some("true")),
        ]
    );
}

#[test]
fn partial_rules_report_emissions() {
    let policy = "package t\ns contains x if { some x in input.xs; x > 1 }\no[k] := x if { some k, x in input.o }\n";
    let r = run(policy, "data.t.s", r#"{"xs":[1,2]}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Gt, "1", "1", Failure),
            compare(Operator::Gt, "2", "1", Success),
            Event::Emission {
                key: None,
                value: v("2"),
            },
            body_end(Success, None),
        ]
    );
    let emission = r.contexts()[2];
    assert!(matches!(
        r.instruction(&emission),
        Instruction::SetAdd { .. }
    ));

    let r = run(policy, "data.t.o", r#"{"o":{"a":1}}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            Event::Emission {
                key: Some(v(r#""a""#)),
                value: v("1"),
            },
            body_end(Success, None),
        ]
    );

    let r = run(policy, "data.t.o", r#"{"o":{}}"#);
    assert_eq!(r.events(), [Event::Reset, body_end(Success, None)]);
}

#[test]
fn bodies_definitions_and_helpers_are_identified() {
    let policy = "package t\nr := 1 if { input.a } else := 2 if { input.b }\nr := 3 if { input.c; h(input.c) }\nh(x) := y if { y := x }\n";
    let r = run(policy, "data.t.r", r#"{"b":true}"#);
    assert_eq!(r.result.as_ref().unwrap(), &v("2"));
    let ends: Vec<_> = r
        .events
        .iter()
        .filter(|e| matches!(e.event, Event::BodyEnd { .. }))
        .map(|e| {
            let c = e.context.unwrap();
            (c.definition_index, c.body_index, e.event.clone())
        })
        .collect();
    assert_eq!(
        ends,
        [
            (0, 0, body_end(Failure, None)),
            (0, 1, body_end(Success, Some("2"))),
            (1, 0, body_end(Failure, None)),
        ]
    );

    let r = run(policy, "data.t.r", r#"{"c":3}"#);
    assert_eq!(r.result.as_ref().unwrap(), &v("3"));
    let helper = r
        .events
        .iter()
        .find(|e| e.context.is_some_and(|c| c.call_depth == 2))
        .unwrap();
    assert_eq!(helper.event, body_end(Success, Some("3")));
    let caller = r.events.last().unwrap().context.unwrap();
    assert_eq!(caller.call_depth, 1);
    assert_ne!(helper.context.unwrap().rule_index, caller.rule_index);
}

#[test]
fn builtin_errors_are_reported() {
    let policy = "package t\nallow if { json.unmarshal(input.s) }\n";
    let r = run(policy, "data.t.allow", r#"{"s":"{"}"#);
    let events = r.events();
    assert!(
        matches!(&events[1], Event::BuiltinError { name, message, raised: false }
            if name == "json.unmarshal" && !message.is_empty()),
        "{events:?}"
    );
    assert_eq!(events[2], unary(Truthiness, Value::Undefined, Undefined));
    assert!(matches!(
        r.instruction(&r.contexts()[0]),
        Instruction::BuiltinCall { .. }
    ));

    let r = run_with(policy, "data.t.allow", r#"{"s":"{"}"#, true);
    assert!(
        matches!(&r.events()[1], Event::BuiltinError { name, raised: true, .. }
            if name == "json.unmarshal"),
        "{:?}",
        r.events()
    );

    let r = run(policy, "data.t.allow", r#"{"s":"true"}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Truthiness, Value::from(true), Success),
            body_end(Success, Some("true")),
        ]
    );
}

#[test]
fn comprehensions_are_not_captured() {
    let policy = "package t\nc := [y | some y in input.xs; h(y)]\nh(y) if { g(y) }\ng(y) if { y > 1 }\nafter if { count(c) > 0; h(5) }\n";
    let r = run(policy, "data.t.after", r#"{"xs":[2]}"#);
    assert_eq!(r.result.as_ref().unwrap(), &Value::from(true));
    let begin = r.contexts()[0];
    assert!(matches!(
        r.instruction(&begin),
        Instruction::ComprehensionBegin { .. }
    ));
    let truthy = || unary(Truthiness, Value::from(true), Success);
    let succeeded = || body_end(Success, Some("true"));
    let observed: Vec<_> = r
        .events
        .iter()
        .skip(1)
        .map(|e| {
            let c = e.context.unwrap();
            (
                c.rule_index.unwrap(),
                c.call_depth,
                c.in_comprehension,
                e.event.clone(),
            )
        })
        .collect();
    // Rules: 0 = after, 1 = c, 2 = h, 3 = g. Only the comprehension's own
    // checks and those of h and g called for it are flagged, and not c's
    // body end or the later h(5) call.
    assert_eq!(
        observed,
        [
            (
                1,
                2,
                false,
                Event::NotCaptured(UncapturedConstruct::Comprehension)
            ),
            (3, 4, true, compare(Operator::Gt, "2", "1", Success)),
            (3, 4, true, succeeded()),
            (2, 3, true, truthy()),
            (2, 3, true, succeeded()),
            (1, 2, true, truthy()),
            (
                1,
                2,
                true,
                Event::ComprehensionEmission {
                    begin_pc: begin.pc,
                    kind: "array",
                    key: None,
                    value: v("2"),
                },
            ),
            (1, 2, false, body_end(Success, Some("[2]"))),
            (0, 1, false, compare(Operator::Gt, "1", "0", Success)),
            (3, 3, false, compare(Operator::Gt, "5", "1", Success)),
            (3, 3, false, succeeded()),
            (2, 2, false, truthy()),
            (2, 2, false, succeeded()),
            (0, 1, false, truthy()),
            (0, 1, false, succeeded()),
        ]
    );
}

#[test]
fn comprehension_yields_report_typed_payloads_and_static_begin_sites() {
    let cases = [
        ("[y | some y in input.xs; y > 1]", "array", v("[2,2,3]")),
        (
            "{y | some y in input.xs; y > 1}",
            "set",
            Value::from(std::collections::BTreeSet::from([v("2"), v("3")])),
        ),
        (
            r#"{"k": y | some y in input.xs; y > 1}"#,
            "object",
            v(r#"{"k":3}"#),
        ),
    ];
    for (expression, kind, expected) in cases {
        let policy = format!("package t\nc := {expression}\n");
        let r = run(&policy, "data.t.c", r#"{"xs":[0,2,2,3]}"#);
        assert_eq!(r.result.unwrap(), expected);
        let emissions: Vec<_> = r
            .events
            .iter()
            .filter_map(|recorded| match &recorded.event {
                Event::ComprehensionEmission {
                    begin_pc,
                    kind,
                    key,
                    value,
                } => Some((
                    *begin_pc,
                    *kind,
                    key.clone(),
                    value.clone(),
                    recorded.context.unwrap(),
                )),
                _ => None,
            })
            .collect();
        assert_eq!(emissions.len(), 3, "{expression}: {:?}", r.events);
        let begin_pc = emissions[0].0;
        assert!(matches!(
            r.program.instructions[begin_pc],
            Instruction::ComprehensionBegin { .. }
        ));
        for ((site, observed_kind, key, value, context), expected_value) in
            emissions.into_iter().zip([2, 2, 3])
        {
            assert_eq!(site, begin_pc);
            assert_eq!(observed_kind, kind);
            assert_eq!(key, (kind == "object").then(|| v(r#""k""#)));
            assert_eq!(value, Value::from(expected_value));
            assert!(context.in_comprehension);
            assert!(matches!(
                r.program.instructions[context.pc],
                Instruction::ComprehensionYield { .. }
            ));
        }
        assert_eq!(
            r.events
                .iter()
                .filter(|e| matches!(
                    e.event,
                    Event::NotCaptured(UncapturedConstruct::Comprehension)
                ))
                .count(),
            1,
        );
    }
}

#[test]
fn comprehension_yields_skip_empty_failed_and_undefined_values() {
    for expression in [
        "[input.m[k] | some k in input.ks]",
        "{input.m[k] | some k in input.ks}",
        "{input.m[k]: k | some k in input.ks}",
        "{k: input.m[k] | some k in input.ks}",
    ] {
        let policy = format!("package t\nc := {expression}\n");
        for input in [
            r#"{"ks":[],"m":{}}"#,
            r#"{"ks":["missing"],"m":{}}"#,
            r#"{"ks":["a","missing"],"m":{"a":1}}"#,
        ] {
            let r = run(&policy, "data.t.c", input);
            assert!(r.result.is_ok(), "{:?}", r.result);
            let emissions: Vec<_> = r
                .events
                .iter()
                .filter(|e| matches!(e.event, Event::ComprehensionEmission { .. }))
                .collect();
            assert_eq!(
                emissions.len(),
                usize::from(input.contains("\"a\"")),
                "{expression}: {input}"
            );
        }
    }
    let r = run(
        "package t\nc := [y | some y in input.xs; y > 9]\n",
        "data.t.c",
        r#"{"xs":[1,2]}"#,
    );
    assert_eq!(r.result.unwrap(), v("[]"));
    assert!(!r
        .events
        .iter()
        .any(|e| matches!(e.event, Event::ComprehensionEmission { .. })));
}

#[test]
fn comprehension_yields_keep_nested_and_helper_sites_distinct() {
    let policy = "package t\nh(y) := [z | some z in y; z > 1]\nc := [h(row) | some row in input.rows]\nafter := [c, h([5])]\n";
    let r = run(policy, "data.t.after", r#"{"rows":[[1,2],[3]]}"#);
    assert_eq!(r.result.unwrap(), v("[[[2],[3]],[5]]"));
    let emissions: Vec<_> = r
        .events
        .iter()
        .filter_map(|e| match &e.event {
            Event::ComprehensionEmission {
                begin_pc, value, ..
            } => Some((*begin_pc, value.clone(), e.context.unwrap())),
            _ => None,
        })
        .collect();
    assert_eq!(emissions.len(), 5);
    let inner = emissions[0].0;
    let outer = emissions[1].0;
    assert_ne!(inner, outer);
    assert_eq!(
        emissions
            .iter()
            .map(|(site, value, _)| (*site, value.clone()))
            .collect::<Vec<_>>(),
        [
            (inner, v("2")),
            (outer, v("[2]")),
            (inner, v("3")),
            (outer, v("[3]")),
            (inner, v("5"))
        ]
    );
    assert!(emissions.iter().all(|(_, _, c)| c.in_comprehension));
    assert!(emissions[0].2.call_depth > emissions[1].2.call_depth);
    assert!(r
        .events
        .iter()
        .filter(|e| matches!(e.event, Event::BodyEnd { .. })
            && e.context.unwrap().rule_index == Some(0))
        .all(|e| !e.context.unwrap().in_comprehension));
}

#[test]
fn comprehension_yields_handle_raw_undefined_keys_values_and_result_aliases() {
    use regorus::rvm::instructions::{ComprehensionBeginParams, ComprehensionMode};
    for mode in [
        ComprehensionMode::Array,
        ComprehensionMode::Set,
        ComprehensionMode::Object,
    ] {
        for (key, value, alias, key_override) in [
            (v(r#""k""#), v("7"), false, None),
            (Value::Undefined, v("7"), false, None),
            (v(r#""k""#), Value::Undefined, false, None),
            (v(r#""k""#), v("7"), true, None),
            (v(r#""k""#), v("7"), false, Some(0)),
            (Value::Undefined, v("7"), false, Some(2)),
        ] {
            let mut program = Program::new();
            program.literals = vec![key.clone(), value.clone()];
            let params_index = program.add_comprehension_begin_params(ComprehensionBeginParams {
                mode: mode.clone(),
                collection_reg: 0,
                result_reg: 0,
                key_reg: 1,
                value_reg: 2,
                body_start: 3,
                comprehension_end: 5,
            });
            program.instructions = vec![
                Instruction::Load {
                    dest: 1,
                    literal_idx: 0,
                },
                Instruction::Load {
                    dest: 2,
                    literal_idx: 1,
                },
                Instruction::ComprehensionBegin { params_index },
                Instruction::ComprehensionYield {
                    value_reg: if alias { 0 } else { 2 },
                    key_reg: key_override,
                },
                Instruction::ComprehensionEnd {},
                Instruction::Return { value: 0 },
            ];
            program.max_rule_window_size = 8;
            program.dispatch_window_size = 8;
            let empty = match mode {
                ComprehensionMode::Array => v("[]"),
                ComprehensionMode::Set => Value::new_set(),
                ComprehensionMode::Object => v("{}"),
            };
            let yielded = if alias { empty.clone() } else { value.clone() };
            let key = match key_override {
                Some(0) => empty.clone(),
                Some(2) => value.clone(),
                _ => key,
            };
            let defined = yielded != Value::Undefined
                && (!matches!(mode, ComprehensionMode::Object) || key != Value::Undefined);
            let program = Arc::new(program);
            for execution_mode in MODES {
                let r = run_program(&program, "{}", execution_mode, false);
                let result = r.result.as_ref().unwrap();
                let emissions: Vec<_> = r
                    .events
                    .iter()
                    .filter_map(|e| match &e.event {
                        Event::ComprehensionEmission {
                            begin_pc,
                            key,
                            value,
                            ..
                        } => Some((*begin_pc, key.clone(), value.clone())),
                        _ => None,
                    })
                    .collect();
                assert_eq!(
                    emissions,
                    if defined {
                        vec![(
                            2,
                            matches!(mode, ComprehensionMode::Object).then(|| key.clone()),
                            yielded.clone(),
                        )]
                    } else {
                        vec![]
                    },
                    "{mode:?} key={key:?} value={value:?} alias={alias}",
                );
                let expected = if !defined {
                    empty.clone()
                } else {
                    match mode {
                        ComprehensionMode::Array => Value::from(vec![yielded.clone()]),
                        ComprehensionMode::Set => {
                            Value::from(std::collections::BTreeSet::from([yielded.clone()]))
                        }
                        ComprehensionMode::Object => Value::from(std::collections::BTreeMap::from(
                            [(key.clone(), yielded.clone())],
                        )),
                    }
                };
                assert_eq!(result, &expected);
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(execution_mode);
                assert_eq!(execute(&mut vm, execution_mode).unwrap(), expected);
            }
        }
    }
}

#[test]
fn comprehension_yields_follow_auto_iteration_and_skip_failed_writes() {
    use regorus::rvm::instructions::{ComprehensionBeginParams, ComprehensionMode};
    for mode in [
        ComprehensionMode::Array,
        ComprehensionMode::Set,
        ComprehensionMode::Object,
    ] {
        for invalid_result in [false, true] {
            let mut program = Program::new();
            program.literals = vec![v("[10,20]"), v("7")];
            let params_index = program.add_comprehension_begin_params(ComprehensionBeginParams {
                mode: mode.clone(),
                collection_reg: 3,
                result_reg: 0,
                key_reg: 1,
                value_reg: 2,
                body_start: 2,
                comprehension_end: if invalid_result { 5 } else { 4 },
            });
            program.add_instruction(
                Instruction::Load {
                    dest: 3,
                    literal_idx: 0,
                },
                None,
            );
            program.add_instruction(Instruction::ComprehensionBegin { params_index }, None);
            if invalid_result {
                program.add_instruction(
                    Instruction::Load {
                        dest: 0,
                        literal_idx: 1,
                    },
                    None,
                );
            }
            program.add_instruction(
                Instruction::ComprehensionYield {
                    value_reg: 2,
                    key_reg: None,
                },
                None,
            );
            program.add_instruction(Instruction::ComprehensionEnd {}, None);
            program.add_instruction(Instruction::Return { value: 0 }, None);
            program.max_rule_window_size = 8;
            program.dispatch_window_size = 8;
            let program = Arc::new(program);
            for execution_mode in MODES {
                let r = run_program(&program, "{}", execution_mode, false);
                let emissions: Vec<_> = r
                    .events
                    .iter()
                    .filter_map(|e| match &e.event {
                        Event::ComprehensionEmission {
                            begin_pc,
                            key,
                            value,
                            ..
                        } => {
                            assert!(e.context.unwrap().in_comprehension);
                            Some((*begin_pc, key.clone(), value.clone()))
                        }
                        _ => None,
                    })
                    .collect();
                if invalid_result {
                    assert!(r.result.is_err());
                    assert!(emissions.is_empty());
                } else {
                    let is_object = matches!(mode, ComprehensionMode::Object);
                    assert_eq!(
                        emissions,
                        [
                            (1, is_object.then(|| v("0")), v("10")),
                            (1, is_object.then(|| v("1")), v("20")),
                        ]
                    );
                    let expected = match mode {
                        ComprehensionMode::Array => v("[10,20]"),
                        ComprehensionMode::Set => {
                            Value::from(std::collections::BTreeSet::from([v("10"), v("20")]))
                        }
                        ComprehensionMode::Object => {
                            Value::from(std::collections::BTreeMap::from([
                                (v("0"), v("10")),
                                (v("1"), v("20")),
                            ]))
                        }
                    };
                    assert_eq!(r.result.as_ref().unwrap(), &expected);
                }
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_execution_mode(execution_mode);
                assert_eq!(
                    format!("{:?}", execute(&mut vm, execution_mode)),
                    format!("{:?}", r.result),
                );
            }
        }
    }
}

#[test]
fn comprehension_yields_survive_suspension_without_replaying() {
    let mut engine = Engine::new();
    engine
        .add_policy(
            "test.rego".into(),
            "package t\nh(y) := lookup(y)\nc := [h(y) | some y in input.xs]\nafter := [c, 9]\n"
                .into(),
        )
        .unwrap();
    let compiled = engine
        .compile_with_entrypoint(&Rc::from("data.t.after"))
        .unwrap();
    let program = Compiler::compile_from_policy_with_host_await(
        &compiled,
        &["data.t.after"],
        &[("lookup", 1)],
    )
    .unwrap();
    let fixture = Fixture::default();
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_explanation_recorder(Box::new(fixture.clone()));
    vm.set_input(v(r#"{"xs":[1,2]}"#));
    vm.execute().unwrap();
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended { .. }
    ));
    let mut call_segments = vec![fixture.calls()];
    let mut events = fixture.take();
    assert!(!events
        .iter()
        .any(|e| matches!(e.event, Event::ComprehensionEmission { .. })));
    vm.resume(Some(v("10"))).unwrap();
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended { .. }
    ));
    call_segments.push(fixture.calls());
    events.extend(fixture.take());
    vm.resume(Some(v("20"))).unwrap();
    assert!(
        matches!(vm.execution_state(), ExecutionState::Completed { result } if result == &v("[[10,20],9]"))
    );
    call_segments.push(fixture.calls());
    events.extend(fixture.take());
    let mut last_started = 0;
    let mut active_calls = Vec::new();
    for (segment_index, calls) in call_segments.iter().enumerate() {
        if segment_index == 1 {
            assert!(calls
                .iter()
                .any(|call| matches!(call, CallRecord::Start(_, _))));
        }
        for call in calls {
            match call {
                CallRecord::Start(_, event) => {
                    assert!(event.call_instance > last_started);
                    last_started = event.call_instance;
                    active_calls.push((Some(event.call_instance), Some(event.rule_index)));
                }
                CallRecord::End(context, source, result) => {
                    assert_eq!(
                        active_calls.pop(),
                        Some((context.call_instance, context.rule_index))
                    );
                    assert!(source.is_some());
                    assert!(result.is_some());
                }
                CallRecord::Reused(_, _) => {}
            }
        }
        assert_eq!(active_calls.is_empty(), segment_index == 2);
    }
    let yields: Vec<_> = events
        .iter()
        .filter_map(|e| match &e.event {
            Event::ComprehensionEmission {
                begin_pc, value, ..
            } => {
                assert!(e.context.unwrap().in_comprehension);
                Some((*begin_pc, value.clone()))
            }
            _ => None,
        })
        .collect();
    assert_eq!(yields.len(), 2);
    assert_eq!(yields, [(yields[0].0, v("10")), (yields[0].0, v("20"))]);
    assert_eq!(
        events
            .iter()
            .filter(|e| matches!(e.event, Event::Reset))
            .count(),
        1
    );
    assert!(events
        .iter()
        .filter(|e| matches!(e.event, Event::BodyEnd { .. })
            && e.context.unwrap().rule_index == Some(0))
        .all(|e| !e.context.unwrap().in_comprehension));
}

#[test]
fn recorder_is_reset_for_each_evaluation() {
    let program = compile("package t\nallow if input.a\n", "data.t.allow").unwrap();
    for mode in MODES {
        let fixture = Fixture::default();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_explanation_recorder(Box::new(fixture.clone()));
        vm.set_input(v(r#"{"a":true}"#));
        execute(&mut vm, mode).unwrap();
        vm.set_input(v(r#"{"a":false}"#));
        execute(&mut vm, mode).unwrap();
        let starts: Vec<_> = fixture
            .calls()
            .into_iter()
            .filter_map(|record| match record {
                CallRecord::Start(_, event) => Some(event.call_instance),
                _ => None,
            })
            .collect();
        assert_eq!(starts, [1, 1]);
        let events: Vec<_> = fixture.take().into_iter().map(|r| r.event).collect();
        assert_eq!(
            events,
            [
                Event::Reset,
                unary(Truthiness, Value::from(true), Success),
                body_end(Success, Some("true")),
                Event::Reset,
                unary(Truthiness, Value::from(false), Failure),
                body_end(Failure, None),
            ]
        );

        assert!(vm.take_explanation_recorder().is_some());
        assert!(vm.take_explanation_recorder().is_none());
        vm.set_input(v(r#"{"a":true}"#));
        assert_eq!(execute(&mut vm, mode).unwrap(), Value::from(true));
        assert!(fixture.take().is_empty());
    }
}

#[test]
fn invocation_ids_separate_repeated_calls_and_rejected_parameters() {
    let policy = r#"
package t
f(1,y,z) := "ok"
f(x,2,z) := "ok"
f(x,y,3) := "ok"
r := [f(input.a[0],input.a[1],input.a[2]), f(input.b[0],input.b[1],input.b[2])]
"#;
    for input in [
        r#"{"a":[1,0,0],"b":[0,2,3]}"#,
        r#"{"a":[1,2,0],"b":[0,0,3]}"#,
    ] {
        let r = run(policy, "data.t.r", input);
        assert_eq!(r.result.as_ref().unwrap(), &v(r#"["ok","ok"]"#));
        let ids = r.call_ids("data.t.f");
        assert_eq!(ids, [2, 3]);
        for id in ids {
            assert_eq!(
                r.call_end(id),
                (Some(CallResultSource::Body), Some(v(r#""ok""#)))
            );
        }
        for record in &r.calls {
            if let CallRecord::Start(caller, event) = record {
                if event.call_instance != 1 {
                    assert_eq!(caller.call_instance, Some(1));
                    assert_eq!(caller.call_depth, 1);
                }
            }
        }
        for record in &r.events {
            if let Some(context) = record.context {
                assert!(context.call_instance.is_some());
            }
        }
    }
    let r = run(policy, "data.t.r", r#"{"a":[0,0,0],"b":[1,0,0]}"#);
    let id = r.call_ids("data.t.f")[0];
    assert_eq!(
        r.call_end(id),
        (Some(CallResultSource::Undefined), Some(Value::Undefined))
    );
}

#[test]
fn invocation_cache_reuse_preserves_original_identity_and_result_source() {
    for (definition, source, input) in [
        ("default p := false", CallResultSource::Default, "{}"),
        (
            "default p := false\np if input.x",
            CallResultSource::Default,
            r#"{"x":false}"#,
        ),
        ("p := input.x", CallResultSource::Body, r#"{"x":false}"#),
    ] {
        let policy = format!("package t\n{definition}\nr := [p,p]\n");
        let r = run(&policy, "data.t.r", input);
        assert_eq!(r.result.as_ref().unwrap(), &v("[false,false]"));
        let ids = r.call_ids("data.t.p");
        assert_eq!(ids.len(), 1);
        assert_eq!(r.call_end(ids[0]), (Some(source), Some(Value::Bool(false))));
        let uses: Vec<_> = r
            .calls
            .iter()
            .filter_map(|record| match record {
                CallRecord::Reused(caller, event) => {
                    Some((caller.call_instance, event.call_instance))
                }
                _ => None,
            })
            .collect();
        assert_eq!(uses, [(Some(1), Some(ids[0]))]);
    }
    let r = run(
        "package t\np := input.missing\nr if { not p; not p }\n",
        "data.t.r",
        "{}",
    );
    let id = r.call_ids("data.t.p")[0];
    assert_eq!(r.result.as_ref().unwrap(), &Value::Bool(true));
    assert_eq!(
        r.call_end(id),
        (Some(CallResultSource::Undefined), Some(Value::Undefined))
    );
    assert!(r.calls.iter().any(|record| matches!(
        record, CallRecord::Reused(_, event) if event.call_instance == Some(id)
    )));
    let r = run(
        "package t\np contains x if { some x in input.xs }\nr := [count(p),count(p)]\n",
        "data.t.r",
        r#"{"xs":[]}"#,
    );
    assert_eq!(r.result.as_ref().unwrap(), &v("[0,0]"));
    let id = r.call_ids("data.t.p")[0];
    assert_eq!(
        r.call_end(id),
        (Some(CallResultSource::Body), Some(Value::new_set()))
    );
    assert!(r.calls.iter().any(|record| matches!(
        record, CallRecord::Reused(_, event) if event.call_instance == Some(id)
    )));
}

#[test]
fn invocation_with_undefined_arguments_still_has_start_and_end() {
    for (input, expected) in [
        ("{}", Value::Undefined),
        (r#"{"x":false}"#, Value::Bool(false)),
    ] {
        let r = run("package t\nf(x) := x\nr := f(input.x)\n", "data.t.r", input);
        let id = r.call_ids("data.t.f")[0];
        let source = if expected == Value::Undefined {
            CallResultSource::Undefined
        } else {
            CallResultSource::Body
        };
        assert_eq!(r.call_end(id), (Some(source), Some(expected)));
    }
}

fn assert_invocation_subtree_cache_reuse(mode: ExecutionMode) {
    let mut engine = Engine::new();
    for (name, policy) in [
        ("target.rego", "package target.dept\np := input.x\n"),
        ("other.rego", "package target.other\np := input.x\n"),
        (
            "framework.rego",
            "package framework\nr := [data.target[input.a],data.target[input.b]]\n",
        ),
    ] {
        engine
            .add_policy(name.to_string(), policy.to_string())
            .unwrap();
    }
    let entrypoint: Rc<str> = "data.framework.r".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program = Compiler::compile_from_policy(&compiled, &["data.framework.r"]).unwrap();
    let expected = v(r#"[{"p":1},{"p":1}]"#);

    let distinct = run_program(&program, r#"{"a":"dept","b":"other","x":1}"#, mode, false);
    assert_eq!(distinct.result.as_ref().unwrap(), &expected);
    let first = distinct.call_ids("data.target.dept.p");
    let second = distinct.call_ids("data.target.other.p");
    assert_eq!(first.len(), 1);
    assert_eq!(second.len(), 1);
    assert_ne!(first[0], second[0]);
    assert!(!distinct
        .calls
        .iter()
        .any(|record| matches!(record, CallRecord::Reused(_, _))));

    let repeated = run_program(&program, r#"{"a":"dept","b":"dept","x":1}"#, mode, false);
    assert_eq!(repeated.result.as_ref().unwrap(), &expected);
    let target = repeated.call_ids("data.target.dept.p");
    assert_eq!(target.len(), 1, "{mode:?}: {:?}", repeated.calls);
    assert!(repeated.call_ids("data.target.other.p").is_empty());
    let root = repeated.call_ids("data.framework.r")[0];
    let uses: Vec<_> = repeated
        .calls
        .iter()
        .filter_map(|record| match record {
            CallRecord::Reused(caller, event)
                if program.rule_infos[usize::from(event.rule_index)].name
                    == "data.target.dept.p" =>
            {
                Some((caller.call_instance, event.call_instance))
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        uses,
        [(Some(root), Some(target[0]))],
        "{mode:?}: second subtree materialization lost its cached invocation use: {:?}",
        repeated.calls
    );
}

#[test]
fn invocation_subtree_cache_reuse_run_to_completion() {
    assert_invocation_subtree_cache_reuse(ExecutionMode::RunToCompletion);
}

#[test]
fn invocation_subtree_cache_reuse_suspendable() {
    assert_invocation_subtree_cache_reuse(ExecutionMode::Suspendable);
}

#[test]
fn invocation_subtree_cache_reuse_late_recorder_preserves_unknown_identity() {
    let mut engine = Engine::new();
    for (name, policy) in [
        ("target.rego", "package target.dept\np := input.x\n"),
        (
            "framework.rego",
            "package framework\nr := [data.target[input.a], __builtin_host_await(input.x,\"host\"), data.target[input.b]]\n",
        ),
    ] {
        engine.add_policy(name.to_string(), policy.to_string()).unwrap();
    }
    let entrypoint: Rc<str> = "data.framework.r".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program = Compiler::compile_from_policy(&compiled, &["data.framework.r"]).unwrap();
    let mut vm = RegoVM::new();
    vm.load_program(program.clone());
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_input(v(r#"{"a":"dept","b":"dept","x":1}"#));
    vm.execute().unwrap();
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Suspended { .. }
    ));
    let fixture = Fixture::default();
    vm.set_explanation_recorder(Box::new(fixture.clone()));
    vm.resume(Some(Value::Bool(true))).unwrap();
    assert!(matches!(
        vm.execution_state(),
        ExecutionState::Completed { result } if result == &v(r#"[{"p":1},true,{"p":1}]"#)
    ));
    let calls = fixture.calls();
    let uses: Vec<_> = calls
        .iter()
        .filter_map(|record| match record {
            CallRecord::Reused(caller, event)
                if program.rule_infos[usize::from(event.rule_index)].name
                    == "data.target.dept.p" =>
            {
                Some((caller.call_instance, event.call_instance))
            }
            _ => None,
        })
        .collect();
    assert_eq!(uses, [(None, None)], "{calls:?}");
    assert!(!calls
        .iter()
        .any(|record| matches!(record, CallRecord::Start(_, _))));
}

#[test]
fn invocation_mixed_mode_error_keeps_terminal_events_for_every_started_call() {
    let mut engine = Engine::new();
    for (name, policy) in [
        (
            "helpers.rego",
            "package helpers\nf(x) := x\np := f(input.x)\n",
        ),
        ("t.rego", "package t\nr := data[input.ns].p\n"),
    ] {
        engine
            .add_policy(name.to_string(), policy.to_string())
            .unwrap();
    }
    let entrypoint: Rc<str> = "data.t.r".into();
    let compiled = engine.compile_with_entrypoint(&entrypoint).unwrap();
    let program = Compiler::compile_from_policy(&compiled, &["data.t.r"]).unwrap();
    for mode in MODES {
        let mut unrecorded = RegoVM::new();
        unrecorded.load_program(program.clone());
        unrecorded.set_execution_mode(mode);
        unrecorded.set_input(v(r#"{"ns":"helpers","x":1}"#));
        let baseline = execute(&mut unrecorded, mode);
        let fixture = Fixture::default();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(v(r#"{"ns":"helpers","x":1}"#));
        vm.set_explanation_recorder(Box::new(fixture.clone()));
        let result = execute(&mut vm, mode);
        assert_eq!(
            format!("{result:?}"),
            format!("{baseline:?}"),
            "{mode:?}: invocation bookkeeping changed evaluation behavior"
        );
        if mode == ExecutionMode::RunToCompletion {
            assert_eq!(result.as_ref().unwrap(), &v("1"));
        }
        // Mixed-mode evaluation can already fail. Replacing the program must
        // terminate any remaining captured invocations without losing one.
        vm.load_program(program.clone());
        let calls = fixture.calls();
        assert!(
            calls.iter().any(|record| matches!(
                record,
                CallRecord::Start(_, event)
                    if program.rule_infos[usize::from(event.rule_index)].name == "data.helpers.f"
            )),
            "{mode:?}: helper invocation was not reached: {calls:?}"
        );
        let mut started: Vec<_> = calls
            .iter()
            .filter_map(|record| match record {
                CallRecord::Start(_, event) => Some(event.call_instance),
                _ => None,
            })
            .collect();
        let mut ended: Vec<_> = calls
            .iter()
            .filter_map(|record| match record {
                CallRecord::End(context, _, _) => context.call_instance,
                _ => None,
            })
            .collect();
        started.sort_unstable();
        ended.sort_unstable();
        assert_eq!(
            ended, started,
            "{mode:?}: invocation events were lost before error/reset cleanup; result={result:?}, calls={calls:?}"
        );
        if mode == ExecutionMode::Suspendable {
            let child = calls
                .iter()
                .find_map(|record| match record {
                    CallRecord::Start(_, event)
                        if program.rule_infos[usize::from(event.rule_index)].name
                            == "data.helpers.f" =>
                    {
                        Some(event.call_instance)
                    }
                    _ => None,
                })
                .unwrap();
            assert!(
                calls.iter().any(|record| matches!(
                    record, CallRecord::End(context, None, None)
                        if context.call_instance == Some(child)
                )),
                "pending helper must abort, not fabricate completion: {calls:?}"
            );
        }
    }
}

#[test]
fn invocation_abort_is_not_undefined_and_fresh_evaluation_restarts_ids() {
    let program = compile(
        "package t\nf(x) := sum([x,x])\nr := f(input.x)\n",
        "data.t.r",
    )
    .unwrap();
    for mode in MODES {
        let fixture = Fixture::default();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_strict_builtin_errors(true);
        vm.set_explanation_recorder(Box::new(fixture.clone()));
        vm.set_input(v(r#"{"x":1e308}"#));
        assert!(execute(&mut vm, mode).is_err());
        let calls = fixture.calls();
        let ends: Vec<_> = calls
            .iter()
            .filter_map(|record| match record {
                CallRecord::End(context, source, value) => {
                    Some((context.call_instance, *source, value.clone()))
                }
                _ => None,
            })
            .collect();
        assert_eq!(ends, [(Some(2), None, None), (Some(1), None, None)]);
        vm.set_input(v(r#"{"x":1}"#));
        assert_eq!(execute(&mut vm, mode).unwrap(), v("2"));
        let calls = fixture.calls();
        let starts: Vec<_> = calls
            .iter()
            .filter_map(|record| match record {
                CallRecord::Start(_, event) => Some(event.call_instance),
                _ => None,
            })
            .collect();
        assert_eq!(starts, [1, 2]);
        assert_eq!(
            calls
                .iter()
                .filter(|record| matches!(
                    record,
                    CallRecord::End(_, Some(CallResultSource::Body), Some(_))
                ))
                .count(),
            2
        );
    }
    let r = run(
        "package t\nf(x) := x + 1\nr := f(input.x)\n",
        "data.t.r",
        r#"{"x":"bad"}"#,
    );
    assert_eq!(
        r.call_end(r.call_ids("data.t.f")[0]),
        (Some(CallResultSource::Undefined), Some(Value::Undefined))
    );
}

#[test]
fn invocation_identity_survives_host_await_and_late_installation_is_explicit() {
    let policy = "package t\np := input.x\nf(x) := __builtin_host_await(x,\"host\")\nr := [p,f(input.x),p]\n";
    let program = compile(policy, "data.t.r").unwrap();
    for late in [false, true] {
        let fixture = Fixture::default();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_input(v(r#"{"x":1}"#));
        vm.set_execution_mode(ExecutionMode::Suspendable);
        if !late {
            vm.set_explanation_recorder(Box::new(fixture.clone()));
        }
        vm.execute().unwrap();
        assert!(matches!(
            vm.execution_state(),
            ExecutionState::Suspended { .. }
        ));
        let before = fixture.calls();
        assert_eq!(
            before
                .iter()
                .filter(|record| matches!(record, CallRecord::Start(_, _)))
                .count(),
            if late { 0 } else { 3 }
        );
        if late {
            vm.set_explanation_recorder(Box::new(fixture.clone()));
        }
        assert!(vm.resume(None).is_err());
        assert!(fixture.calls().is_empty());
        vm.resume(Some(v("7"))).unwrap();
        assert!(
            matches!(vm.execution_state(), ExecutionState::Completed { result } if result == &v("[1,7,1]"))
        );
        let after = fixture.calls();
        let reused: Vec<_> = after
            .iter()
            .filter_map(|record| match record {
                CallRecord::Reused(_, event) => Some(event.call_instance),
                _ => None,
            })
            .collect();
        assert_eq!(reused, [if late { None } else { Some(2) }]);
        if !late {
            let ended: Vec<_> = after
                .iter()
                .filter_map(|record| match record {
                    CallRecord::End(context, _, _) => context.call_instance,
                    _ => None,
                })
                .collect();
            assert_eq!(ended, [3, 1]);
        }
        assert!(!after
            .iter()
            .any(|record| matches!(record, CallRecord::Start(_, _))));
        assert_eq!(
            fixture
                .take()
                .iter()
                .filter(|record| record.event == Event::Reset)
                .count(),
            usize::from(!late)
        );
    }
}

#[test]
fn invocation_late_recorder_does_not_assign_uncaptured_default_to_caller() {
    let program = compile(
        "package t\ndefault p := false\np if __builtin_host_await(input.x,\"child\")\nr := [__builtin_host_await(input.x,\"outer\"),p]\n",
        "data.t.r",
    ).unwrap();
    let fixture = Fixture::default();
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_execution_mode(ExecutionMode::Suspendable);
    vm.set_input(v(r#"{"x":true}"#));
    vm.set_explanation_recorder(Box::new(fixture.clone()));
    vm.execute().unwrap();
    assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""outer""#)));
    let recorder = vm.take_explanation_recorder().unwrap();
    vm.resume(Some(Value::Bool(true))).unwrap();
    assert_eq!(vm.get_host_await_identifier(), Some(&v(r#""child""#)));
    vm.set_explanation_recorder(recorder);
    vm.resume(Some(Value::Bool(false))).unwrap();
    assert!(
        matches!(vm.execution_state(), ExecutionState::Completed { result } if result == &v("[true,false]"))
    );
    let ends: Vec<_> = fixture
        .calls()
        .into_iter()
        .filter_map(|record| match record {
            CallRecord::End(context, source, value) => Some((context.call_instance, source, value)),
            _ => None,
        })
        .collect();
    assert_eq!(
        ends,
        [(
            Some(1),
            Some(CallResultSource::Body),
            Some(v("[true,false]"))
        )]
    );
}

#[test]
fn invocation_malformed_rule_index_preserves_recorder_off_error() {
    let mut program = Program::new();
    program.dispatch_window_size = 2;
    program.max_rule_window_size = 2;
    program.instructions = vec![
        Instruction::CallRule {
            dest: 0,
            rule_index: 0,
        },
        Instruction::Return { value: 0 },
    ];
    let program = Arc::new(program);
    let outcomes = MODES.map(|mode| {
        [false, true].map(|recording| {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            if recording {
                vm.set_explanation_recorder(Box::new(Fixture::default()));
            }
            vm.execute()
        })
    });
    for (mode, [baseline, recorded]) in MODES.into_iter().zip(outcomes) {
        let expected = Err(VmError::RuleIndexOutOfBounds {
            index: 0,
            pc: 0,
            available: 0,
        });
        assert_eq!(baseline, expected, "{mode:?}: recorder-off baseline");
        assert_eq!(
            recorded, expected,
            "{mode:?}: recording changed the typed error"
        );
    }
}

#[test]
fn invocation_malformed_undefined_argument_preserves_recorder_off_result() {
    let mut program = Program::new();
    program.dispatch_window_size = 2;
    program.max_rule_window_size = 2;
    let params_index = program.add_function_call_params(FunctionCallParams {
        dest: 0,
        func_rule_index: 0,
        num_args: 1,
        args: [1, 0, 0, 0, 0, 0, 0, 0],
    });
    program.instructions = vec![
        Instruction::FunctionCall { params_index },
        Instruction::Return { value: 0 },
    ];
    let program = Arc::new(program);
    let outcomes = MODES.map(|mode| {
        [false, true].map(|recording| {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            if recording {
                vm.set_explanation_recorder(Box::new(Fixture::default()));
            }
            vm.execute()
        })
    });
    for (mode, [baseline, recorded]) in MODES.into_iter().zip(outcomes) {
        assert_eq!(
            baseline,
            Ok(Value::Undefined),
            "{mode:?}: recorder-off baseline"
        );
        assert_eq!(
            recorded,
            Ok(Value::Undefined),
            "{mode:?}: recording changed undefined-argument short-circuit semantics"
        );
    }
}

#[test]
fn assert_eq_is_reported_as_an_equality() {
    let mut program = Program::new();
    program.literals = vec![Value::from(1), Value::from(2)];
    program.instructions = vec![
        Instruction::Load {
            dest: 0,
            literal_idx: 0,
        },
        Instruction::Load {
            dest: 1,
            literal_idx: 0,
        },
        Instruction::AssertEq { left: 0, right: 1 },
        Instruction::Load {
            dest: 1,
            literal_idx: 1,
        },
        Instruction::AssertEq { left: 0, right: 1 },
        Instruction::Return { value: 0 },
    ];
    program.main_entry_point = 0;
    program.max_rule_window_size = 8;
    program.dispatch_window_size = 8;
    let program = Arc::new(program);
    for mode in MODES {
        let r = run_program(&program, "{}", mode, false);
        assert!(r.result.is_err());
        assert_eq!(
            r.events(),
            [
                Event::Reset,
                compare(Operator::Eq, "1", "1", Success),
                compare(Operator::Eq, "1", "2", Failure),
            ]
        );
        let context = r.contexts()[1];
        assert_eq!(
            (context.pc, context.rule_index, context.call_depth),
            (4, None, 0)
        );
    }
}

#[test]
fn every_reports_inner_loop_results_then_its_own_quantifier() {
    let policy = "package t\nallow if { every x in input.xs { some y in input.ys; y == x } }\n";
    let r = run(policy, "data.t.allow", r#"{"xs":[1],"ys":[1,2]}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Eq, "1", "1", Success),
            compare(Operator::Eq, "2", "1", Failure),
            unary(Iteration, v("[1,2]"), Success),
            unary(Iteration, v("[1]"), Success),
            body_end(Success, Some("true")),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"xs":[1],"ys":[2]}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Eq, "2", "1", Failure),
            unary(Iteration, v("[2]"), Failure),
            unary(Iteration, v("[1]"), Failure),
            body_end(Failure, None),
        ]
    );
}

fn check_every_inner_loop(body: &str) {
    let quantifier = format!("every x in input.xs {{ {body} }}");
    let policy = format!("package t\nallow if {{ every x in input.xs {{ {body} }} }}\n");
    for (collection, outcome, expected) in [
        ("[]", Failure, Value::Undefined),
        ("{}", Failure, Value::Undefined),
        ("42", Failure, Value::Undefined),
        (r#""text""#, Failure, Value::Undefined),
        ("null", Failure, Value::Undefined),
        ("[false]", Failure, Value::Undefined),
        ("[true]", Success, Value::Bool(true)),
    ] {
        let input = format!(r#"{{"xs":[{collection}]}}"#);
        let r = run(&policy, "data.t.allow", &input);
        assert_eq!(r.result.as_ref().unwrap(), &expected, "{body} {input}");
        let provenance = Provenance::new(&r.program);
        let iterations: Vec<_> = r
            .events
            .iter()
            .filter_map(|recorded| match &recorded.event {
                Event::Check {
                    kind: Iteration,
                    left,
                    outcome,
                    ..
                } => {
                    let context = recorded.context.as_ref().unwrap();
                    assert!(matches!(
                        r.instruction(context),
                        Instruction::LoopStart { .. }
                    ));
                    let site = provenance.site_at(context.pc).unwrap();
                    assert_eq!(site.kind, Iteration);
                    assert_eq!(site.operator, None);
                    assert!(site.location.is_some());
                    Some((left.clone(), *outcome, site.text.as_str()))
                }
                _ => None,
            })
            .collect();
        assert_eq!(
            iterations,
            [
                (v(collection), outcome, "x"),
                (v(&format!("[{collection}]")), outcome, quantifier.as_str()),
            ],
            "{body} {input}"
        );
    }
}

#[test]
fn every_inner_some_reports_at_the_collection_site() {
    check_every_inner_loop("some y in x; y");
}

#[test]
fn every_inner_index_reports_at_the_collection_site() {
    check_every_inner_loop("y := x[_]; y");
}

#[test]
fn undefined_inner_collections_are_reported_only_once() {
    for body in ["some y in x.ys; y", "y := x.ys[_]; y"] {
        let policy = format!("package t\nallow if {{ every x in input.xs {{ {body} }} }}\n");
        let r = run(&policy, "data.t.allow", r#"{"xs":[{}]}"#);
        assert_eq!(r.result.as_ref().unwrap(), &Value::Undefined);
        assert_eq!(
            r.events(),
            [
                Event::Reset,
                unary(Iteration, Value::Undefined, Undefined),
                unary(Iteration, v("[{}]"), Failure),
                body_end(Failure, None),
            ],
            "{body}"
        );
        let context = r.events[1].context.as_ref().unwrap();
        let provenance = Provenance::new(&r.program);
        let site = provenance.site_at(context.pc).unwrap();
        assert_eq!((site.kind, site.text.as_str()), (Iteration, "x.ys"));
    }
}

#[test]
fn loops_outside_every_do_not_report_a_result_check() {
    for body in ["some y in input.xs; y", "y := input.xs[_]; y"] {
        let policy = format!("package t\nallow if {{ {body} }}\n");
        for (input, expected) in [
            (r#"{"xs":[]}"#, Value::Undefined),
            (r#"{"xs":42}"#, Value::Undefined),
            (r#"{"xs":"text"}"#, Value::Undefined),
            (r#"{"xs":null}"#, Value::Undefined),
            (r#"{"xs":[true]}"#, Value::Bool(true)),
        ] {
            let r = run(&policy, "data.t.allow", input);
            assert_eq!(r.result.as_ref().unwrap(), &expected);
            assert!(
                !r.events().iter().any(|event| matches!(
                    event,
                    Event::Check {
                        kind: Iteration,
                        ..
                    }
                )),
                "{body} {input}: {:?}",
                r.events()
            );
        }
    }
}

#[test]
fn undefined_bindings_are_reported() {
    let policies = [
        "package t\nallow if { _ = input.p }\n",
        "package t\nallow if { {\"k\": x} := input.p; x }\n",
    ];
    for policy in policies {
        let r = run(policy, "data.t.allow", "{}");
        assert_eq!(
            r.events(),
            [
                Event::Reset,
                unary(ConditionKind::Existence, Value::Undefined, Undefined),
                body_end(Failure, None),
            ],
            "{policy}"
        );
    }

    let r = run(policies[0], "data.t.allow", r#"{"p":1}"#);
    assert_eq!(r.events(), [Event::Reset, body_end(Success, Some("true"))]);
}

#[test]
fn membership_in_an_undefined_collection_is_undefined() {
    let policy = "package t\nallow if { \"x\" in input.tags }\n";
    let r = run(policy, "data.t.allow", "{}");
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            Event::Check {
                kind: Membership,
                operator: Some(Operator::In),
                left: v(r#""x""#),
                right: Some(Value::Undefined),
                outcome: Undefined,
            },
            body_end(Failure, None),
        ]
    );
}

/// `key, value in collection` is a membership test, although it is compiled
/// to an indexing whose result is negated twice.
#[test]
fn keyed_membership_is_reported_as_membership() {
    let policy = "package t\nallow if { \"k\", 1 in input.m }\n";
    let membership = |container: Value, outcome| Event::Check {
        kind: Membership,
        operator: Some(Operator::In),
        left: v(r#""k""#),
        right: Some(container),
        outcome,
    };
    for (container, outcome, end) in [
        (r#"{"k":1}"#, Success, body_end(Success, Some("true"))),
        (r#"{"k":2}"#, Failure, body_end(Failure, None)),
        (r#"{"j":1}"#, Failure, body_end(Failure, None)),
    ] {
        let input = format!(r#"{{"m":{container}}}"#);
        let r = run(policy, "data.t.allow", &input);
        assert_eq!(
            r.events(),
            [Event::Reset, membership(v(container), outcome), end],
            "{input}"
        );
    }

    // The key is not evaluated unless the value and the collection are
    // defined and the collection is an array or an object.
    let unevaluated = |container: Value, outcome| Event::Check {
        kind: Membership,
        operator: Some(Operator::In),
        left: Value::Undefined,
        right: Some(container),
        outcome,
    };
    let r = run(policy, "data.t.allow", "{}");
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unevaluated(Value::Undefined, Undefined),
            body_end(Failure, None),
        ]
    );
    let r = run(policy, "data.t.allow", r#"{"m":"k"}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unevaluated(v(r#""k""#), Failure),
            body_end(Failure, None),
        ]
    );
    let r = run(
        "package t\nallow if { \"k\", input.v in {\"k\": 1} }\n",
        "data.t.allow",
        "{}",
    );
    assert_eq!(r.events()[1], unevaluated(v(r#"{"k":1}"#), Undefined));

    let r = run(
        "package t\nallow if { input.k, 1 in {\"k\": 1} }\n",
        "data.t.allow",
        "{}",
    );
    assert_eq!(
        r.events()[1],
        Event::Check {
            kind: Membership,
            operator: Some(Operator::In),
            left: Value::Undefined,
            right: Some(v(r#"{"k":1}"#)),
            outcome: Undefined,
        }
    );

    // A negated keyed membership is a negation of the membership.
    let policy = "package t\nallow if { not \"k\", 1 in input.m }\n";
    for (container, outcome) in [(r#"{"j":1}"#, Success), (r#"{"k":1}"#, Failure)] {
        let input = format!(r#"{{"m":{container}}}"#);
        let r = run(policy, "data.t.allow", &input);
        assert_eq!(
            r.events()[1],
            Event::Check {
                kind: Negation,
                operator: Some(Operator::In),
                left: v(r#""k""#),
                right: Some(v(container)),
                outcome,
            },
            "{input}"
        );
    }
}

/// A negated keyed membership whose negation overwrites the key, the
/// collection or the value is reported as a negation of the membership's
/// result, without operands read after the overwrite.
#[test]
fn negated_membership_with_an_aliased_negation_is_not_decoded() {
    use regorus::rvm::instructions::GuardMode;
    let program = compile(
        "package t\nallow if { not \"k\", 1 in input.m }\n",
        "data.t.allow",
    )
    .unwrap();
    let pcs = 0..program.instructions.len();
    let guard = pcs
        .clone()
        .find(|&pc| {
            matches!(
                (pc.checked_sub(1).map(|p| program.instructions[p]), program.instructions[pc]),
                (
                    Some(Instruction::Not { dest, operand }),
                    Instruction::Guard { register, mode: GuardMode::Condition },
                ) if dest == register && operand != dest
            )
        })
        .expect("negated membership guard");
    let Instruction::Not { operand, .. } = program.instructions[guard - 1] else {
        unreachable!()
    };
    let index = pcs
        .take(guard)
        .rfind(|&pc| matches!(program.instructions[pc], Instruction::Index { .. }))
        .expect("membership index");
    let (Instruction::Index { container, key, .. }, Instruction::Eq { right: value, .. }) =
        (program.instructions[index], program.instructions[index + 1])
    else {
        panic!("unexpected keyed membership lowering");
    };
    assert!(
        key != container
            && key != value
            && container != value
            && ![key, container, value].contains(&operand),
        "{key} {container} {value} {operand}"
    );
    let input = r#"{"m":{"k":1}}"#;
    let r = run_program(&program, input, ExecutionMode::RunToCompletion, false);
    assert_eq!(
        r.events()[1].clone(),
        Event::Check {
            kind: Negation,
            operator: Some(Operator::In),
            left: v(r#""k""#),
            right: Some(v(r#"{"k":1}"#)),
            outcome: Failure,
        }
    );
    for clobbered in [key, container, value] {
        let mut altered = (*program).clone();
        altered.instructions[guard - 1] = Instruction::Not {
            dest: clobbered,
            operand,
        };
        altered.instructions[guard] = Instruction::Guard {
            register: clobbered,
            mode: GuardMode::Condition,
        };
        let r = run_program(
            &Arc::new(altered),
            input,
            ExecutionMode::RunToCompletion,
            false,
        );
        assert_eq!(
            r.events()[1],
            unary(Negation, Value::from(true), Failure),
            "{clobbered}"
        );
    }
}

/// Every check event but an existence check is reported at its site, a
/// check of the same kind and operator.
#[test]
fn checks_are_reported_at_their_sites() {
    let cases = [
        (
            "package t\nallow if { input.x > 0; input.flag }\n",
            r#"{"x":1,"flag":true}"#,
            false,
        ),
        (
            "package t\nallow if { \"x\" in input.tags }\n",
            r#"{"tags":["y"]}"#,
            false,
        ),
        (
            "package t\nallow if { not input.x == 1 }\n",
            r#"{"x":1}"#,
            false,
        ),
        (
            "package t\nallow if { \"a\", 1 in input.m }\n",
            r#"{"m":{"a":1}}"#,
            false,
        ),
        (
            "package t\nallow if { not \"a\", 1 in input.m }\n",
            r#"{"m":{"a":2}}"#,
            false,
        ),
        (
            "package t\nallow if { 0, 1 in input.xs }\n",
            r#"{"xs":[1]}"#,
            false,
        ),
        (
            "package t\nallow if { every x in input.xs { x > 0 } }\n",
            r#"{"xs":[1,-1]}"#,
            false,
        ),
        (
            "package t\nallow if { every x in input.xs { x > 0 } }\n",
            "{}",
            false,
        ),
        (
            "package t\nallow if { some r in input.rs; r }\n",
            "{}",
            false,
        ),
        ("package t\nallow if { x := input.a[_]; x }\n", "{}", false),
        ("package t\nallow if input.x > 0\n", r#"{"x":"text"}"#, true),
        (
            "package t\nallow if not input.x > 0\n",
            r#"{"x":"text"}"#,
            true,
        ),
    ];
    for (policy, input, strict) in cases {
        let r = run_with(policy, "data.t.allow", input, strict);
        let provenance = Provenance::new(&r.program);
        let mut checks = 0;
        for recorded in &r.events {
            let Event::Check { kind, operator, .. } = recorded.event else {
                continue;
            };
            let pc = recorded.context.unwrap().pc;
            if kind == ConditionKind::Existence {
                assert_eq!(provenance.site_at(pc), None, "{policy} {input}: pc {pc}");
                continue;
            }
            checks += 1;
            let site = provenance.site_at(pc);
            // A negation's operator is that of the negated expression, which
            // its site doesn't record.
            let operator = operator.filter(|_| kind != ConditionKind::Negation);
            assert_eq!(
                site.map(|site| (site.kind, site.operator)),
                Some((kind, operator)),
                "{policy} {input}: pc {pc}, {:?}",
                r.instruction(&recorded.context.unwrap())
            );
        }
        assert!(checks > 0, "{policy} {input}: {:?}", r.events());
    }
}

/// When every check of a policy runs, each site receives at least one event,
/// except the iteration site of a `some` over a defined collection.
#[test]
fn every_site_is_reported_when_all_checks_run() {
    let cases = [
        (
            "package t\nallow if { input.x > 0; input.flag }\n",
            r#"{"x":1,"flag":true}"#,
        ),
        (
            "package t\nallow if { every x in input.xs { x > 0 } }\n",
            r#"{"xs":[1,2]}"#,
        ),
        (
            "package t\nallow if { every x in input.xs { some y in x; y } }\n",
            r#"{"xs":[[true]]}"#,
        ),
        (
            "package t\nallow if { some y in input.ys; y < 0 }\n",
            r#"{"ys":[-1]}"#,
        ),
        (
            "package t\nallow if { not \"a\", 1 in input.m }\n",
            r#"{"m":{"a":2}}"#,
        ),
        (
            "package t\nallow if { _ = input.p; input.q }\n",
            r#"{"p":1,"q":true}"#,
        ),
    ];
    for (policy, input) in cases {
        let r = run(policy, "data.t.allow", input);
        let reported: Vec<usize> = r
            .events
            .iter()
            .filter(|recorded| matches!(recorded.event, Event::Check { .. }))
            .map(|recorded| recorded.context.unwrap().pc)
            .collect();
        // Outside `every`, a `some` iteration is reported only for an undefined collection.
        let silent = |site: &&CheckSite| {
            site.kind == ConditionKind::Iteration && !site.text.starts_with("every ")
        };
        for site in Provenance::new(&r.program)
            .sites()
            .iter()
            .filter(|s| !silent(s))
        {
            assert!(
                reported.contains(&site.pc),
                "{policy} {input}: site {:?} at pc {} has no event: {:?}",
                site.text,
                site.pc,
                r.events()
            );
        }
    }
}

#[test]
fn undefined_object_entries_are_not_emitted() {
    let policy = "package t\no[k] := input.m[k] if { some k in input.ks }\n";
    let r = run(policy, "data.t.o", r#"{"ks":["a","b"],"m":{"a":1}}"#);
    let emissions: Vec<_> = r
        .events()
        .into_iter()
        .filter(|e| matches!(e, Event::Emission { .. }))
        .collect();
    assert_eq!(
        emissions,
        [Event::Emission {
            key: Some(v(r#""a""#)),
            value: v("1"),
        }],
        "result: {:?}",
        r.result
    );
}

#[test]
fn builtin_error_messages_have_no_source_frame() {
    let policy = "package t\nallow if { json.unmarshal(input.s) }\n";
    let r = run(policy, "data.t.allow", r#"{"s":"{"}"#);
    let Event::BuiltinError { message, .. } = &r.events()[1] else {
        panic!("{:?}", r.events());
    };
    assert!(!message.is_empty());
    assert!(!message.contains("<builtin>"), "{message:?}");
    assert!(!message.starts_with('\n'), "{message:?}");
}

#[test]
fn arithmetic_errors_are_reported() {
    let policy = "package t\nallow if { r := input.a / input.b; r > 1 }\n";
    let r = run(policy, "data.t.allow", r#"{"a":1,"b":0}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            Event::BuiltinError {
                name: "div".into(),
                message: "divide by zero".into(),
                raised: false,
            },
            Event::Check {
                kind: ConditionKind::Comparison,
                operator: Some(Operator::Gt),
                left: Value::Undefined,
                right: Some(v("1")),
                outcome: Undefined,
            },
            body_end(Failure, None),
        ]
    );
    let r = run(policy, "data.t.allow", r#"{"a":4,"b":2}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Gt, "2", "1", Success),
            body_end(Success, Some("true")),
        ]
    );

    let policy = "package t\nallow if { y := input.a % input.b; y == 0 }\n";
    let r = run_with(policy, "data.t.allow", r#"{"a":1,"b":0}"#, true);
    assert!(
        matches!(&r.events()[1], Event::BuiltinError { name, raised: true, .. } if name == "rem"),
        "{:?}",
        r.events()
    );

    let policy = "package t\nallow if { y := input.s + 1 }\n";
    let r = run(policy, "data.t.allow", r#"{"s":"x"}"#);
    assert!(
        matches!(&r.events()[1], Event::BuiltinError { name, raised: true, .. } if name == "plus"),
        "{:?}",
        r.events()
    );
    assert_eq!(r.events()[2], body_end(Failure, None));
}

#[test]
fn errors_in_a_comprehension_do_not_flag_later_bodies() {
    let policy = "package t\nr := 1 if { ys := [y | y := input.s + 1]; count(ys) > 0 } else := 2 if { input.z == 3 }\n";
    let program = compile(policy, "data.t.r").unwrap();
    let r = run_program(
        &program,
        r#"{"s":"a","z":3}"#,
        ExecutionMode::RunToCompletion,
        false,
    );
    assert_eq!(r.result.as_ref().unwrap(), &v("2"));
    let later: Vec<_> = r
        .events
        .iter()
        .filter(|e| e.context.is_some_and(|c| c.body_index == 1))
        .map(|e| (e.context.unwrap().in_comprehension, e.event.clone()))
        .collect();
    assert_eq!(
        later,
        [
            (false, compare(Operator::Eq, "3", "3", Success)),
            (false, body_end(Success, Some("2"))),
        ]
    );
    let first: Vec<_> = r
        .events
        .iter()
        .filter(|e| e.context.is_some_and(|c| c.body_index == 0))
        .filter(|e| matches!(e.event, Event::BodyEnd { .. }))
        .map(|e| (e.context.unwrap().in_comprehension, e.event.clone()))
        .collect();
    assert_eq!(first, [(false, body_end(Failure, None))]);
}

#[test]
fn parameter_patterns_are_not_reported_as_checks() {
    let policy = "package t\nf(1) := \"one\" if { input.x } else := \"fallback\"\nf(y) := \"other\" if { y != 1 }\nr := f(2)\n";
    let r = run(policy, "data.t.r", "{}");
    assert_eq!(r.result.as_ref().unwrap(), &v(r#""other""#));
    let observed: Vec<_> = r
        .events
        .iter()
        .skip(1)
        .map(|e| {
            let c = e.context.unwrap();
            (c.call_depth, c.definition_index, e.event.clone())
        })
        .collect();
    assert_eq!(
        observed,
        [
            (2, 1, compare(Operator::Ne, "2", "1", Success)),
            (2, 1, body_end(Success, Some(r#""other""#))),
            (1, 0, body_end(Success, Some(r#""other""#))),
        ]
    );
}

#[test]
fn nested_parameter_patterns_are_not_reported_as_checks() {
    let policy = "package t\ng(1) := \"one\"\ng(y) := \"other\" if { y != 1 }\nf(x) := r if { r := g(x); x > 0 }\nr := f(2)\n";
    let r = run(policy, "data.t.r", "{}");
    assert_eq!(r.result.as_ref().unwrap(), &v(r#""other""#));
    let observed: Vec<_> = r
        .events
        .iter()
        .skip(1)
        .map(|e| {
            let c = e.context.unwrap();
            (c.call_depth, c.definition_index, e.event.clone())
        })
        .collect();
    assert_eq!(
        observed,
        [
            (3, 1, compare(Operator::Ne, "2", "1", Success)),
            (3, 1, body_end(Success, Some(r#""other""#))),
            (2, 0, compare(Operator::Gt, "2", "0", Success)),
            (2, 0, body_end(Success, Some(r#""other""#))),
            (1, 0, body_end(Success, Some(r#""other""#))),
        ]
    );
}

struct PanicOnReset;

impl ExplanationRecorder for PanicOnReset {
    fn reset(&mut self) {
        panic!("reset failed");
    }
}

#[test]
fn a_panicking_reset_removes_the_recorder() {
    let program = compile("package t\nallow if input.a\n", "data.t.allow").unwrap();
    for mode in MODES {
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(v(r#"{"a":true}"#));
        vm.set_explanation_recorder(Box::new(PanicOnReset));
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| vm.execute()));
        assert!(outcome.is_err(), "{mode:?}");
        assert!(vm.take_explanation_recorder().is_none(), "{mode:?}");
    }
}

fn first_error(expr: &str, input: &str, strict: bool) -> Event {
    let policy = format!("package t\nallow if {{ y := {expr}; y }}\n");
    let r = run_with(&policy, "data.t.allow", input, strict);
    r.events()
        .into_iter()
        .find(|e| matches!(e, Event::BuiltinError { .. }))
        .unwrap_or_else(|| panic!("{expr}: {:?}", r.events()))
}

fn error_event(name: &str, message: &str, raised: bool) -> Event {
    Event::BuiltinError {
        name: name.into(),
        message: message.into(),
        raised,
    }
}

#[test]
fn arithmetic_error_messages_name_operand_types() {
    let cases = [
        (
            "input.a + input.b",
            r#"{"a":"x","b":1}"#,
            "plus",
            "operand 1 must be number but got string",
        ),
        (
            "input.a + input.b",
            r#"{"a":1,"b":[]}"#,
            "plus",
            "operand 2 must be number but got array",
        ),
        (
            "input.a - input.b",
            r#"{"a":"x","b":1}"#,
            "minus",
            "operand 1 must be one of {number, set} but got string",
        ),
        (
            "input.a - input.b",
            r#"{"a":1,"b":"x"}"#,
            "minus",
            "operand 2 must be number but got string",
        ),
        (
            "{1} - input.b",
            r#"{"b":1}"#,
            "minus",
            "operand 2 must be set but got number",
        ),
        (
            "1 - input.b",
            r#"{"b":[]}"#,
            "minus",
            "operand 2 must be number but got array",
        ),
        (
            "input.a * input.b",
            r#"{"a":true,"b":1}"#,
            "mul",
            "operand 1 must be number but got boolean",
        ),
        (
            "input.a / input.b",
            r#"{"a":1,"b":null}"#,
            "div",
            "operand 2 must be number but got null",
        ),
        (
            "input.a % input.b",
            r#"{"a":{},"b":1}"#,
            "rem",
            "operand 1 must be number but got object",
        ),
        (
            "input.a % input.b",
            r#"{"a":1.5,"b":1}"#,
            "rem",
            "modulo on floating-point number",
        ),
    ];
    for strict in [false, true] {
        for (expr, input, name, message) in cases {
            assert_eq!(
                first_error(expr, input, strict),
                error_event(name, message, true),
                "{expr} {input} strict={strict}"
            );
        }
        for (expr, name, message) in [
            ("input.a / input.b", "div", "divide by zero"),
            ("input.a % input.b", "rem", "modulo by zero"),
        ] {
            assert_eq!(
                first_error(expr, r#"{"a":1,"b":0}"#, strict),
                error_event(name, message, strict),
                "{expr} strict={strict}"
            );
        }
    }
}

#[test]
fn set_operator_errors_use_the_operator_names() {
    for strict in [false, true] {
        assert_eq!(
            first_error("input.a | {1}", r#"{"a":1}"#, strict),
            error_event("or", "operand 1 must be set but got number", strict),
        );
        assert_eq!(
            first_error("{1} & input.a", r#"{"a":"x"}"#, strict),
            error_event("and", "operand 2 must be set but got string", strict),
        );
    }
}

#[test]
fn builtin_error_messages_keep_their_cause() {
    let policy = "package t\nallow if { json.unmarshal(input.s) }\n";
    let r = run(policy, "data.t.allow", r#"{"s":"{"}"#);
    assert_eq!(
        r.events()[1],
        error_event(
            "json.unmarshal",
            "could not deserialize json.: EOF while parsing an object at line 1 column 1",
            false
        )
    );
}

#[test]
fn iterating_an_undefined_collection_is_reported() {
    let policy = "package t\nallow if { some r in input.user.roles; r == \"admin\" }\n";
    // The body ends after the loop, without a value.
    let matched_nothing = Event::BodyEnd {
        outcome: Success,
        result: Some(Value::Undefined),
    };
    let r = run(policy, "data.t.allow", "{}");
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Iteration, Value::Undefined, Undefined),
            matched_nothing.clone(),
        ]
    );

    let r = run(policy, "data.t.allow", r#"{"user":{"roles":[]}}"#);
    assert_eq!(r.events(), [Event::Reset, matched_nothing]);

    let policy = "package t\nallow if { every r in input.user.roles { r == \"admin\" } }\n";
    let r = run(policy, "data.t.allow", "{}");
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            unary(Iteration, Value::Undefined, Undefined),
            body_end(Failure, None),
        ]
    );
}

#[test]
fn iterations_over_undefined_collections_are_reported() {
    let undefined = unary(Iteration, Value::Undefined, Undefined);
    let cases = [
        ("package t\nallow if { x := input.a[_]; x }\n", false),
        ("package t\nallow if { some k, x in input.a; x }\n", false),
        (
            "package t\nallow if { ys := [y | y := input.a[_]]; count(ys) == 0 }\n",
            true,
        ),
    ];
    for (policy, in_comprehension) in cases {
        let r = run(policy, "data.t.allow", "{}");
        let undefined_iterations: Vec<_> = r
            .events
            .iter()
            .filter(|e| e.event == undefined)
            .map(|e| {
                let context = e.context.unwrap();
                assert!(
                    matches!(r.instruction(&context), Instruction::LoopStart { .. }),
                    "{policy}"
                );
                context.in_comprehension
            })
            .collect();
        assert_eq!(
            undefined_iterations,
            [in_comprehension],
            "{policy}: {:?}",
            r.events()
        );
    }

    let r = run(
        "package t\nallow if { some x in 5; x }\n",
        "data.t.allow",
        "{}",
    );
    assert!(
        !r.events().iter().any(|e| matches!(e, Event::Check { .. })),
        "{:?}",
        r.events()
    );
}

#[test]
fn builtin_overflow_is_reported_only_when_it_does_not_end_the_evaluation() {
    let policy = "package t\nallow if { y := sum([input.a, input.a]); y }\n";
    let input = r#"{"a":1e308}"#;
    let reported = first_error("sum([input.a, input.a])", input, false);
    assert!(
        matches!(&reported, Event::BuiltinError { name, raised: false, .. } if name == "sum"),
        "{reported:?}"
    );
    let r = run_with(policy, "data.t.allow", input, true);
    assert!(r.result.is_err(), "{:?}", r.result);
    assert!(
        !r.events()
            .iter()
            .any(|e| matches!(e, Event::BuiltinError { .. })),
        "{:?}",
        r.events()
    );
}

#[cfg(feature = "azure_policy")]
#[test]
fn azure_policy_conditions_are_not_reported() {
    use regorus::languages::azure_policy::{compiler as azure, parser};
    let rules = [
        r#"{"if":{"count":{"field":"securityRules[*]"},"greater":0},"then":{"effect":"deny"}}"#,
        r#"{"if":{"count":{"field":"securityRules[*]","where":{"field":"securityRules[*].access","equals":"Allow"}},"equals":0},"then":{"effect":"deny"}}"#,
        r#"{"if":{"value":"[length(field('securityRules[*].name'))]","equals":0},"then":{"effect":"deny"}}"#,
        r#"{"if":{"field":"securityRules[*].access","equals":"Allow"},"then":{"effect":"deny"}}"#,
        r#"{"if":{"not":{"field":"securityRules[*].access","notEquals":"Deny"}},"then":{"effect":"deny"}}"#,
    ];
    let inputs = [
        r#"{"resource":{},"parameters":{}}"#,
        r#"{"resource":{"securityRules":[{"access":"Allow","name":"a"},{"access":"Deny","name":"b"}]},"parameters":{}}"#,
    ];
    for rule in rules {
        let source = regorus::Source::from_contents("rule.json".into(), rule.into()).unwrap();
        let program =
            azure::compile_policy_rule(&parser::parse_policy_rule(&source).unwrap()).unwrap();
        for input in inputs {
            for mode in MODES {
                let fixture = Fixture::default();
                let mut vm = RegoVM::new();
                vm.load_program(program.clone());
                vm.set_input(v(input));
                vm.set_context(v(r#"{"resourceGroup":{"name":"rg"}}"#));
                vm.set_execution_mode(mode);
                vm.set_explanation_recorder(Box::new(fixture.clone()));
                execute(&mut vm, mode).unwrap();
                let events: Vec<_> = fixture.take().into_iter().map(|r| r.event).collect();
                assert!(
                    !events.iter().any(|e| matches!(e, Event::Check { .. })),
                    "{rule} {input} {mode:?}: {events:?}"
                );
            }
        }
    }
}

#[test]
fn undefined_set_elements_and_object_keys_are_not_emitted() {
    let input = r#"{"ks":["a","b"],"m":{"a":"x"}}"#;
    let policy = "package t\np contains input.m[k] if { some k in input.ks }\n";
    let r = run(policy, "data.t.p", input);
    let emissions: Vec<_> = r
        .events()
        .into_iter()
        .filter(|e| matches!(e, Event::Emission { .. }))
        .collect();
    assert_eq!(
        emissions,
        [Event::Emission {
            key: None,
            value: v(r#""x""#),
        }],
        "result: {:?}",
        r.result
    );

    let policy = "package t\no[input.m[k]] := 1 if { some k in input.ks }\n";
    let r = run(policy, "data.t.o", input);
    let emissions: Vec<_> = r
        .events()
        .into_iter()
        .filter(|e| matches!(e, Event::Emission { .. }))
        .collect();
    assert_eq!(
        emissions,
        [Event::Emission {
            key: Some(v(r#""x""#)),
            value: v("1"),
        }],
        "result: {:?}",
        r.result
    );
}

#[test]
fn strict_comparisons_of_different_types_are_undefined_checks() {
    for (op, operator) in [
        (">", Operator::Gt),
        (">=", Operator::Ge),
        ("<", Operator::Lt),
        ("<=", Operator::Le),
    ] {
        let policy = format!("package t\nallow if input.x {op} 0\n");
        let r = run_with(&policy, "data.t.allow", r#"{"x":"text"}"#, true);
        assert_eq!(r.result.as_ref().unwrap(), &Value::Undefined, "{op}");
        assert_eq!(
            r.events(),
            [
                Event::Reset,
                compare(operator, r#""text""#, "0", Undefined),
                body_end(Failure, None),
            ],
            "{op}"
        );

        let policy = format!("package t\nallow if not input.x {op} 0\n");
        let r = run_with(&policy, "data.t.allow", r#"{"x":"text"}"#, true);
        assert_eq!(r.result.as_ref().unwrap(), &Value::Undefined, "not {op}");
        assert_eq!(
            r.events(),
            [
                Event::Reset,
                check(Negation, Some(operator), r#""text""#, Some("0"), Failure),
                body_end(Failure, None),
            ],
            "not {op}"
        );
    }
}

#[test]
fn strict_comparison_aliases_keep_events_aligned_with_provenance() {
    use regorus::rvm::instructions::GuardMode;

    let program = compile("package t\nallow if input.a < input.b\n", "data.t.allow").unwrap();
    let site = Provenance::new(&program)
        .sites()
        .iter()
        .find(|site| site.operator == Some(Operator::Lt))
        .cloned()
        .expect("ordering comparison site");
    let writer = site.pc.checked_sub(1).expect("comparison before guard");
    let Instruction::Lt { dest, left, right } = program.instructions[writer] else {
        panic!("unexpected comparison lowering");
    };
    assert!(dest != left && dest != right && left != right);

    for target in [dest, left, right] {
        let mut altered = (*program).clone();
        altered.instructions[writer] = Instruction::Lt {
            dest: target,
            left,
            right,
        };
        altered.instructions[site.pc] = Instruction::Guard {
            register: target,
            mode: GuardMode::Condition,
        };
        let altered = Arc::new(altered);
        let provenance = Provenance::new(&altered);
        let site = provenance.site_at(site.pc).expect("altered check site");
        for (input, a, b, outcome) in [
            (r#"{"a":1,"b":2}"#, "1", "2", Success),
            (r#"{"a":2,"b":1}"#, "2", "1", Failure),
            (r#"{"a":1,"b":"x"}"#, "1", r#""x""#, Undefined),
        ] {
            // Execute both modes before asserting, including the pre-write error path.
            let runs = MODES.map(|mode| run_program(&altered, input, mode, true));
            for (mode, run) in MODES.into_iter().zip(runs) {
                let expected_result = if outcome == Success {
                    Value::from(true)
                } else {
                    Value::Undefined
                };
                assert_eq!(
                    run.result.as_ref().unwrap(),
                    &expected_result,
                    "{mode:?} target={target} {input}"
                );
                let checks: Vec<_> = run
                    .events
                    .iter()
                    .filter(|recorded| matches!(recorded.event, Event::Check { .. }))
                    .collect();
                assert_eq!(checks.len(), 1, "{mode:?} target={target} {input}");
                let recorded = checks[0];
                assert_eq!(recorded.context.unwrap().pc, site.pc);
                let Event::Check {
                    kind,
                    operator,
                    outcome: actual_outcome,
                    ..
                } = recorded.event
                else {
                    unreachable!()
                };
                assert_eq!(actual_outcome, outcome);
                assert_eq!(
                    (kind, operator),
                    (site.kind, site.operator),
                    "{mode:?} target={target} {input}: {:?}",
                    recorded.event
                );
                if target == dest {
                    assert_eq!(recorded.event, compare(Operator::Lt, a, b, outcome));
                } else {
                    let value = if outcome == Undefined {
                        Value::Undefined
                    } else {
                        Value::from(outcome == Success)
                    };
                    assert_eq!(
                        recorded.event,
                        unary(Truthiness, value, outcome),
                        "{mode:?} target={target} {input}"
                    );
                }
            }
        }
    }
}

/// A comparison whose value is not checked is not reported, even when it
/// raises an error.
#[test]
fn strict_comparisons_that_are_not_checks_are_not_reported() {
    for (policy, query) in [
        ("package t\np := input.x > 0\n", "data.t.p"),
        (
            "package t\nallow if { b := input.x > 0; b }\n",
            "data.t.allow",
        ),
        (
            "package t\nallow if is_boolean(input.x > 0)\n",
            "data.t.allow",
        ),
    ] {
        let r = run_with(policy, query, r#"{"x":"text"}"#, true);
        assert!(
            !r.events().iter().any(|e| matches!(e, Event::Check { .. })),
            "{policy}: {:?}",
            r.events()
        );
        assert!(
            r.events().contains(&body_end(Failure, None)),
            "{policy}: {:?}",
            r.events()
        );
    }
}

fn has_emission(run: &Run) -> bool {
    run.events()
        .iter()
        .any(|e| matches!(e, Event::Emission { .. }))
}

/// Retargets the program's `SetAdd` or `ObjectSet` to `target`, which picks
/// the new register from the program.
fn retarget(program: &Program, target: impl Fn(&Program, &Instruction) -> Option<u8>) -> Program {
    let mut altered = program.clone();
    let writes: Vec<usize> = altered
        .instructions
        .iter()
        .enumerate()
        .filter(|(_, i)| {
            matches!(
                i,
                Instruction::SetAdd { .. } | Instruction::ObjectSet { .. }
            )
        })
        .map(|(pc, _)| pc)
        .collect();
    assert_eq!(writes.len(), 1);
    let register = target(program, &altered.instructions[writes[0]]).unwrap();
    match &mut altered.instructions[writes[0]] {
        Instruction::SetAdd { set, .. } => *set = register,
        Instruction::ObjectSet { obj, .. } => *obj = register,
        _ => unreachable!(),
    }
    altered
}

/// An emitted operand that is the partial rule's result itself is reported
/// as it was before the write. The programs are altered so that `SetAdd`
/// and `ObjectSet` read an operand from the result register.
#[test]
fn emissions_of_the_result_itself_report_its_value_before_the_write() {
    let set = Value::new_set();
    let object = Value::new_object();
    let cases = [
        (
            "package t\np contains input.x if true\n",
            "data.t.p",
            false,
            None,
            set,
        ),
        (
            "package t\no[input.x] := 1 if true\n",
            "data.t.o",
            false,
            Some(v(r#""a""#)),
            object.clone(),
        ),
        (
            "package t\no[input.x] := 1 if true\n",
            "data.t.o",
            true,
            Some(object),
            v("1"),
        ),
    ];
    for (policy, query, alias_key, key, value) in cases {
        let mut altered = compile(policy, query).unwrap().as_ref().clone();
        for instruction in &mut altered.instructions {
            match instruction {
                Instruction::SetAdd { set, value } => *value = *set,
                Instruction::ObjectSet { obj, key, .. } if alias_key => *key = *obj,
                Instruction::ObjectSet { obj, value, .. } => *value = *obj,
                _ => {}
            }
        }
        let altered = Arc::new(altered);
        let expected = Event::Emission {
            key: key.clone(),
            value: value.clone(),
        };
        for mode in MODES {
            let r = run_program(&altered, r#"{"x":"a"}"#, mode, false);
            let emissions: Vec<_> = r
                .events()
                .into_iter()
                .filter(|e| matches!(e, Event::Emission { .. }))
                .collect();
            assert_eq!(
                emissions,
                std::slice::from_ref(&expected),
                "{policy} {mode:?}"
            );
        }
    }
}

/// A successful write to a collection that is not the executing partial
/// rule's result is not an emission. The programs are altered so that
/// `SetAdd` and `ObjectSet` write to the iterated collection instead.
#[test]
fn writes_to_other_collections_are_not_emitted() {
    let cases = [
        (
            "package t\np contains x if some x in {\"a\"}\n",
            "data.t.p",
            Value::new_set(),
        ),
        (
            "package t\no[k] := v if some k, v in {\"a\": 1}\n",
            "data.t.o",
            Value::new_object(),
        ),
    ];
    for (policy, query, empty) in cases {
        let program = compile(policy, query).unwrap();
        let altered = Arc::new(retarget(&program, |program, _| {
            program.instructions.iter().find_map(|i| match *i {
                Instruction::LoopStart { params_index } => program
                    .instruction_data
                    .get_loop_params(params_index)
                    .map(|params| params.collection),
                _ => None,
            })
        }));
        for mode in MODES {
            assert!(has_emission(&run_program(&program, "{}", mode, false)));
            let r = run_program(&altered, "{}", mode, false);
            assert_eq!(r.result.as_ref().unwrap(), &empty, "{policy} {mode:?}");
            assert!(!has_emission(&r), "{policy} {mode:?}: {:?}", r.events());
        }
    }
}

/// A write to the partial rule's result that fails is not an emission. The
/// programs are altered so that the rule accumulates its result in the
/// register that holds the produced value, which is not a collection when
/// the write runs.
#[test]
fn failed_writes_to_a_partial_rule_result_are_not_emitted() {
    let cases = [
        ("package t\np contains input.x if true\n", "data.t.p"),
        ("package t\no[input.x] := 1 if true\n", "data.t.o"),
    ];
    for (policy, query) in cases {
        let program = compile(policy, query).unwrap();
        let mut altered = retarget(&program, |_, write| match *write {
            Instruction::SetAdd { value, .. } | Instruction::ObjectSet { value, .. } => Some(value),
            _ => None,
        });
        let value = altered
            .instructions
            .iter()
            .find_map(|i| match *i {
                Instruction::SetAdd { set, .. } => Some(set),
                Instruction::ObjectSet { obj, .. } => Some(obj),
                _ => None,
            })
            .unwrap();
        let mut inits = 0;
        for instruction in &mut altered.instructions {
            if let Instruction::RuleInit { result_reg, .. } = instruction {
                *result_reg = value;
                inits += 1;
            }
        }
        assert_eq!(inits, 1, "{policy}");
        let altered = Arc::new(altered);
        for mode in MODES {
            assert!(has_emission(&run_program(
                &program,
                r#"{"x":"a"}"#,
                mode,
                false
            )));
            let r = run_program(&altered, r#"{"x":"a"}"#, mode, false);
            assert!(!has_emission(&r), "{policy} {mode:?}: {:?}", r.events());
            assert!(
                r.events().contains(&body_end(Failure, None)),
                "{policy} {mode:?}: {:?}",
                r.events()
            );
        }
    }
}

struct SlowCallStart(Fixture);

impl ExplanationRecorder for SlowCallStart {
    fn reset(&mut self) {
        self.0.reset();
    }

    fn call_start(&mut self, context: &HookContext, event: &CallStartEvent) {
        self.0.call_start(context, event);
        std::thread::sleep(std::time::Duration::from_millis(200));
    }

    fn call_end(&mut self, context: &HookContext, event: &CallEndEvent<'_>) {
        self.0.call_end(context, event);
    }
}

#[test]
fn invocation_deadline_abort_terminates_the_active_call() -> Result<()> {
    use regorus::utils::limits::ExecutionTimerConfig;
    use std::num::NonZeroU32;

    let program = compile("package t\nallow if input.a\n", "data.t.allow")?;
    for mode in MODES {
        let fixture = Fixture::default();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(v(r#"{"a":true}"#));
        vm.set_execution_timer_config(Some(ExecutionTimerConfig {
            limit: std::time::Duration::from_millis(20),
            check_interval: NonZeroU32::MIN,
        }));
        vm.set_explanation_recorder(Box::new(SlowCallStart(fixture.clone())));
        let outcome = vm.execute();
        assert!(
            matches!(&outcome, Err(VmError::TimeLimitExceeded { .. })),
            "{mode:?}: expected a typed deadline error, got {outcome:?}"
        );
        let calls = fixture.calls();
        let [CallRecord::Start(caller, start), CallRecord::End(owner, None, None)] =
            calls.as_slice()
        else {
            bail!("{mode:?}: expected one started invocation and one abort: {calls:?}");
        };
        assert_eq!(caller.call_instance, None);
        assert_eq!(owner.call_instance, Some(start.call_instance));
        assert_eq!(owner.rule_index, Some(start.rule_index));
        assert_eq!(owner.call_depth, caller.call_depth + 1);
    }
    Ok(())
}

struct SlowCallReuse(Fixture);

impl ExplanationRecorder for SlowCallReuse {
    fn call_start(&mut self, context: &HookContext, event: &CallStartEvent) {
        self.0.call_start(context, event);
    }

    fn call_end(&mut self, context: &HookContext, event: &CallEndEvent<'_>) {
        self.0.call_end(context, event);
    }

    fn call_reused(&mut self, context: &HookContext, event: &CallReusedEvent) {
        self.0.call_reused(context, event);
        std::thread::sleep(std::time::Duration::from_millis(200));
    }
}

#[test]
fn invocation_subtree_cache_reuse_checks_deadline_between_providers() -> Result<()> {
    use regorus::utils::limits::ExecutionTimerConfig;
    use std::num::NonZeroU32;

    let mut engine = Engine::new();
    engine.add_policy(
        "target.rego".into(),
        "package target.dept\np0 := 0\np1 := 1\np2 := 2\np3 := 3\n".into(),
    )?;
    engine.add_policy(
        "t.rego".into(),
        "package t\nr := [data.target[input.a],data.target[input.b]]\n".into(),
    )?;
    let compiled = engine.compile_with_entrypoint(&Rc::from("data.t.r"))?;
    let program = Compiler::compile_from_policy(&compiled, &["data.t.r"])?;
    let expected = v(r#"[{"p0":0,"p1":1,"p2":2,"p3":3},{"p0":0,"p1":1,"p2":2,"p3":3}]"#);
    for mode in MODES {
        let control = Fixture::default();
        let mut vm = RegoVM::new();
        vm.load_program(program.clone());
        vm.set_execution_mode(mode);
        vm.set_input(v(r#"{"a":"dept","b":"dept"}"#));
        vm.set_explanation_recorder(Box::new(control.clone()));
        assert_eq!(execute(&mut vm, mode)?, expected);
        assert_eq!(
            control
                .calls()
                .iter()
                .filter(|call| matches!(call, CallRecord::Reused(_, _)))
                .count(),
            4,
            "{mode:?}: the control must reach all cached providers"
        );

        let fixture = Fixture::default();
        vm.set_explanation_recorder(Box::new(SlowCallReuse(fixture.clone())));
        vm.set_execution_timer_config(Some(ExecutionTimerConfig {
            limit: std::time::Duration::from_millis(100),
            check_interval: NonZeroU32::MIN,
        }));
        let outcome = vm.execute();
        assert!(
            matches!(outcome, Err(VmError::TimeLimitExceeded { .. })),
            "{mode:?}: expected deadline error, got {outcome:?}"
        );
        let calls = fixture.calls();
        assert_eq!(
            calls
                .iter()
                .filter(|call| matches!(call, CallRecord::Reused(_, _)))
                .count(),
            1,
            "{mode:?}: callbacks must stop once the first exceeds the deadline: {calls:?}"
        );
        assert!(calls
            .iter()
            .any(|call| matches!(call, CallRecord::End(_, None, None))));
    }
    Ok(())
}

struct SlowReset;

impl ExplanationRecorder for SlowReset {
    fn reset(&mut self) {
        std::thread::sleep(std::time::Duration::from_millis(200));
    }
}

#[test]
fn reset_time_counts_toward_the_time_limit() {
    use regorus::utils::limits::ExecutionTimerConfig;
    use std::num::NonZeroU32;
    let program = compile("package t\nallow if input.a\n", "data.t.allow").unwrap();
    for mode in MODES {
        for entry_point in [None, Some(Ok(0)), Some(Err("data.t.allow"))] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            vm.set_input(v(r#"{"a":true}"#));
            vm.set_execution_timer_config(Some(ExecutionTimerConfig {
                limit: std::time::Duration::from_millis(20),
                check_interval: NonZeroU32::MIN,
            }));
            vm.set_explanation_recorder(Box::new(SlowReset));
            let result = match entry_point {
                None => vm.execute(),
                Some(Ok(index)) => vm.execute_entry_point_by_index(index),
                Some(Err(name)) => vm.execute_entry_point_by_name(name),
            };
            let error = match (result, vm.execution_state()) {
                (Err(error), _) => error.to_string(),
                (Ok(_), ExecutionState::Error { error }) => error.to_string(),
                (Ok(value), state) => panic!("{mode:?} {entry_point:?}: {value} {state:?}"),
            };
            assert!(
                error.contains("exceeded time limit"),
                "{mode:?} {entry_point:?}: {error}"
            );
        }
    }
}

#[cfg(feature = "arc")]
#[test]
fn vm_stays_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<RegoVM>();
}
