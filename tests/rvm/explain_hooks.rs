// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Events delivered to an `ExplanationRecorder` by the RVM, in both
//! execution modes.

#![cfg(feature = "explanations")]

use anyhow::{bail, Result};
use regorus::explain::{
    BodyEndEvent, BuiltinErrorEvent, CheckEvent, ConditionKind, EmissionEvent, ExplanationRecorder,
    HookContext, NotCapturedEvent, Operator, Outcome, UncapturedConstruct,
};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::program::Program;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM};
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
struct Fixture(Arc<Mutex<Vec<Recorded>>>);

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
}

impl ExplanationRecorder for Fixture {
    fn reset(&mut self) {
        self.push(None, Event::Reset);
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

    fn not_captured(&mut self, context: &HookContext, event: &NotCapturedEvent) {
        self.push(Some(context), Event::NotCaptured(event.construct));
    }
}

struct Run {
    result: Result<Value>,
    events: Vec<Recorded>,
    program: Arc<Program>,
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
fn every_reports_only_its_own_quantifier() {
    let policy = "package t\nallow if { every x in input.xs { some y in input.ys; y == x } }\n";
    let r = run(policy, "data.t.allow", r#"{"xs":[1],"ys":[1,2]}"#);
    assert_eq!(
        r.events(),
        [
            Event::Reset,
            compare(Operator::Eq, "1", "1", Success),
            compare(Operator::Eq, "2", "1", Failure),
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
            unary(Iteration, v("[1]"), Failure),
            body_end(Failure, None),
        ]
    );
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
            unary(ConditionKind::Existence, Value::Undefined, Undefined),
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
    let existence = unary(ConditionKind::Existence, Value::Undefined, Undefined);
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
        let existence_checks: Vec<_> = r
            .events
            .iter()
            .filter(|e| e.event == existence)
            .map(|e| e.context.unwrap().in_comprehension)
            .collect();
        assert_eq!(
            existence_checks,
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
fn azure_policy_loops_over_missing_fields_are_not_reported() {
    use regorus::languages::azure_policy::{compiler as azure, parser};
    let rules = [
        r#"{"if":{"count":{"field":"securityRules[*]"},"greater":0},"then":{"effect":"deny"}}"#,
        r#"{"if":{"count":{"field":"securityRules[*]","where":{"field":"securityRules[*].access","equals":"Allow"}},"equals":0},"then":{"effect":"deny"}}"#,
        r#"{"if":{"value":"[length(field('securityRules[*].name'))]","equals":0},"then":{"effect":"deny"}}"#,
    ];
    for rule in rules {
        let source = regorus::Source::from_contents("rule.json".into(), rule.into()).unwrap();
        let program =
            azure::compile_policy_rule(&parser::parse_policy_rule(&source).unwrap()).unwrap();
        for mode in MODES {
            let fixture = Fixture::default();
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_input(v(r#"{"resource":{},"parameters":{}}"#));
            vm.set_context(v(r#"{"resourceGroup":{"name":"rg"}}"#));
            vm.set_execution_mode(mode);
            vm.set_explanation_recorder(Box::new(fixture.clone()));
            execute(&mut vm, mode).unwrap();
            let events: Vec<_> = fixture.take().into_iter().map(|r| r.event).collect();
            assert!(
                !events.iter().any(|e| matches!(e, Event::Check { .. })),
                "{rule} {mode:?}: {events:?}"
            );
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

#[cfg(feature = "arc")]
#[test]
fn vm_stays_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<RegoVM>();
}
