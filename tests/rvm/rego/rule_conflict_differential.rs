// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for conflicting complete-rule and function definitions.
//!
//! When two definitions of a complete rule (or two definitions of a function
//! for the same arguments) both succeed with different values, OPA and the
//! interpreter abort the query with a conflict error. The RVM must do the same
//! in both execution modes, also when the conflicting rule is only reached
//! through another rule, a `not`, a comprehension, `every` or a partial set, and it
//! must not fall back to the rule's default. Definitions may come from different
//! modules, and a conflict may come from an `else` value. A conflicting rule that
//! is never evaluated does not raise an error, and a VM that raised a conflict
//! evaluates correctly afterwards. Non-conflicting definitions, `else` chains and
//! defaults keep their usual results. The expected outcomes were checked
//! manually against OPA 1.2.0.

use anyhow::{anyhow, bail, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Value};

#[derive(Clone, Copy)]
enum Kind {
    Complete,
    Function,
    /// Zero-arg function `f()`: a complete document for OPA and the RVM. The
    /// interpreter reports it with a different message when called as `f()`
    /// and when read as the document `data.<pkg>.f`.
    ZeroArgCall,
    ZeroArgDocument,
}

impl Kind {
    const fn rvm_message(self) -> &'static str {
        match self {
            Kind::Complete | Kind::ZeroArgCall | Kind::ZeroArgDocument => {
                "complete rules must not produce multiple outputs"
            }
            Kind::Function => "functions must not produce multiple outputs for same inputs",
        }
    }

    const fn interpreter_message(self) -> &'static str {
        match self {
            Kind::Complete => "rule conflicts with rule at",
            Kind::Function | Kind::ZeroArgCall => {
                "functions must not produce multiple outputs for same inputs"
            }
            Kind::ZeroArgDocument => "rules should not produce multiple outputs",
        }
    }
}

enum Expect {
    Value(&'static str),
    Conflict {
        rule: &'static str,
        kind: Kind,
    },
    /// Known RVM bug unrelated to conflicts: the interpreter (and OPA) return
    /// `want`, the RVM returns `rvm`.
    RvmDiverges {
        want: &'static str,
        rvm: &'static str,
    },
}

struct Case {
    name: &'static str,
    modules: Vec<&'static str>,
    entrypoint: &'static str,
    input: &'static str,
    expect: Expect,
}

const UNDEFINED: &str = "#undefined";

const BOTH: &str = r#"{"a": true, "b": true, "n": 10}"#;
const ONLY_A: &str = r#"{"a": true, "n": 3}"#;
const NEITHER: &str = r#"{"n": -1}"#;

const COMPLETE: &str = r#"package test
x := 1 if input.a
x := 2 if input.b
"#;

const FUNCTION: &str = r#"package test
f(v) := 1 if v > 0
f(v) := 2 if v > 5
r := f(input.n)
"#;

const HELPER: &str = r#"package test
helper := "a" if input.a
helper := "b" if input.b
uses if helper == "a"
negated if not helper == "z"
negated_fn if not f(input.n) == 3
in_comprehension := [y | some i in [1, 2]; y := concat("", [helper, format_int(i, 10)])]
in_every if {
  every i in [1, 2] {
    helper != sprintf("%d", [i])
  }
}
in_set contains helper if true
f(v) := 1 if v > 0
f(v) := 2 if v > 5
"#;

const SAME: &str = r#"package test
x := 1 if input.a
x := 1 if input.b
f(v) := 1 if v > 0
f(v) := 1 if v > 5
r := f(input.n)
"#;

const ELSE: &str = r#"package test
x := 1 if input.a
else := 2 if input.b
f(v) := 1 if v > 0
else := 2 if v > 5
r := f(input.n)
"#;

const DEFAULT: &str = r#"package test
default x := 0
x := 1 if input.a
x := 2 if input.b
default f(_) := 0
f(v) := 1 if v > 0
f(v) := 2 if v > 5
r := f(input.n)
"#;

const ZERO_ARG: &str = r#"package test
f() := 1 if input.a
f() := 2 if input.b
r := f()
"#;

const VIRTUAL_LOOKUP: &str = r#"package query
y := data.test[input.k]
all := data.test
"#;

const BOOLEAN: &str = r#"package test
p if input.a
p := false if input.b
q := false if input.a
q := false if input.b
"#;

const REF_HEAD: &str = r#"package test
p.q := 1 if input.a
p.q := 2 if input.b
"#;

const REF_HEAD_LOOKUP: &str = r#"package query
parent := data.test.p
"#;

const CROSS_MODULE_A: &str = r#"package test
x := 1 if input.a
f(v) := 1 if v > 0
"#;

const CROSS_MODULE_B: &str = r#"package test
x := 2 if input.b
f(v) := 2 if v > 5
r := f(input.n)
"#;

const FN_IN_COMPREHENSION: &str = r#"package test
f(v) := 1 if v > 0
f(v) := 2 if v > 5
r := [y | some i in [1]; y := f(input.n + i - 1)]
"#;

const UNEVALUATED: &str = r#"package test
x := 1 if input.a
x := 2 if input.b
f(v) := 1 if v > 0
f(v) := 2 if v > 5
unrelated := true
guarded if {
  input.use_x
  x == 1
}
guarded_fn if {
  input.use_x
  f(input.n) == 1
}
"#;

const ELSE_CONFLICT: &str = r#"package test
x := 1 if input.a
else := 3 if input.c
x := 2 if input.b
x := 3 if input.d
f(v) := 1 if v > 5
else := 3 if v > 0
f(v) := 2 if v == 2
f(v) := 3 if v == 3
r := f(input.n)
"#;

const BOTH_KEY_X: &str = r#"{"a": true, "b": true, "k": "x"}"#;
const ONLY_A_KEY_X: &str = r#"{"a": true, "k": "x"}"#;
const ONLY_B: &str = r#"{"b": true}"#;
const ONLY_C_B: &str = r#"{"b": true, "c": true}"#;
const ONLY_C_D: &str = r#"{"c": true, "d": true}"#;
const BOTH_GUARD_OFF: &str = r#"{"a": true, "b": true, "n": 10, "use_x": false}"#;
const BOTH_GUARD_ON: &str = r#"{"a": true, "b": true, "n": 10, "use_x": true}"#;
const ONLY_A_GUARD_ON: &str = r#"{"a": true, "n": 3, "use_x": true}"#;

fn cases() -> Vec<Case> {
    let conflict = |rule| Expect::Conflict {
        rule,
        kind: Kind::Complete,
    };
    let fn_conflict = |rule| Expect::Conflict {
        rule,
        kind: Kind::Function,
    };
    let case = |name, policy, entrypoint, input, expect| Case {
        name,
        modules: vec![policy],
        entrypoint,
        input,
        expect,
    };
    vec![
        case(
            "complete conflict",
            COMPLETE,
            "data.test.x",
            BOTH,
            conflict("data.test.x"),
        ),
        case(
            "complete one definition",
            COMPLETE,
            "data.test.x",
            ONLY_A,
            Expect::Value("1"),
        ),
        case(
            "complete no definition",
            COMPLETE,
            "data.test.x",
            NEITHER,
            Expect::Value(UNDEFINED),
        ),
        case(
            "function conflict",
            FUNCTION,
            "data.test.r",
            BOTH,
            fn_conflict("data.test.f"),
        ),
        case(
            "function one definition",
            FUNCTION,
            "data.test.r",
            ONLY_A,
            Expect::Value("1"),
        ),
        case(
            "helper rule conflict",
            HELPER,
            "data.test.uses",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule conflict under not",
            HELPER,
            "data.test.negated",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "function conflict under not",
            HELPER,
            "data.test.negated_fn",
            BOTH,
            fn_conflict("data.test.f"),
        ),
        case(
            "helper rule conflict in comprehension",
            HELPER,
            "data.test.in_comprehension",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule conflict in every",
            HELPER,
            "data.test.in_every",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule conflict in partial set",
            HELPER,
            "data.test.in_set",
            BOTH,
            conflict("data.test.helper"),
        ),
        case(
            "helper rule one definition",
            HELPER,
            "data.test.negated",
            ONLY_A,
            Expect::Value("true"),
        ),
        case(
            "same value twins",
            SAME,
            "data.test.x",
            BOTH,
            Expect::Value("1"),
        ),
        case(
            "same value function twins",
            SAME,
            "data.test.r",
            BOTH,
            Expect::Value("1"),
        ),
        case("else twins", ELSE, "data.test.x", BOTH, Expect::Value("1")),
        case(
            "else function twins",
            ELSE,
            "data.test.r",
            BOTH,
            Expect::Value("1"),
        ),
        case(
            "default conflict",
            DEFAULT,
            "data.test.x",
            BOTH,
            conflict("data.test.x"),
        ),
        case(
            "default one definition",
            DEFAULT,
            "data.test.x",
            ONLY_A,
            Expect::Value("1"),
        ),
        case(
            "default function conflict",
            DEFAULT,
            "data.test.r",
            BOTH,
            fn_conflict("data.test.f"),
        ),
        case(
            "default function one definition",
            DEFAULT,
            "data.test.r",
            ONLY_A,
            Expect::Value("1"),
        ),
        // The RVM ignores `default f(_) := 0` when no definition matches.
        case(
            "default function without definition",
            DEFAULT,
            "data.test.r",
            NEITHER,
            Expect::RvmDiverges {
                want: "0",
                rvm: UNDEFINED,
            },
        ),
        case(
            "default without definition",
            DEFAULT,
            "data.test.x",
            NEITHER,
            Expect::Value("0"),
        ),
        Case {
            modules: vec![CROSS_MODULE_A, CROSS_MODULE_B],
            ..case(
                "cross-module conflict",
                "",
                "data.test.x",
                BOTH,
                conflict("data.test.x"),
            )
        },
        Case {
            modules: vec![CROSS_MODULE_A, CROSS_MODULE_B],
            ..case(
                "cross-module one definition",
                "",
                "data.test.x",
                ONLY_A,
                Expect::Value("1"),
            )
        },
        Case {
            modules: vec![CROSS_MODULE_A, CROSS_MODULE_B],
            ..case(
                "cross-module function conflict",
                "",
                "data.test.r",
                BOTH,
                fn_conflict("data.test.f"),
            )
        },
        Case {
            modules: vec![CROSS_MODULE_A, CROSS_MODULE_B],
            ..case(
                "cross-module function one definition",
                "",
                "data.test.r",
                ONLY_A,
                Expect::Value("1"),
            )
        },
        case(
            "function conflict in comprehension",
            FN_IN_COMPREHENSION,
            "data.test.r",
            BOTH,
            fn_conflict("data.test.f"),
        ),
        case(
            "function one definition in comprehension",
            FN_IN_COMPREHENSION,
            "data.test.r",
            ONLY_A,
            Expect::Value("[1]"),
        ),
        case(
            "unreferenced conflicting rule",
            UNEVALUATED,
            "data.test.unrelated",
            BOTH,
            Expect::Value("true"),
        ),
        case(
            "conflicting rule behind a false guard",
            UNEVALUATED,
            "data.test.guarded",
            BOTH_GUARD_OFF,
            Expect::Value(UNDEFINED),
        ),
        case(
            "conflicting rule behind a true guard",
            UNEVALUATED,
            "data.test.guarded",
            BOTH_GUARD_ON,
            conflict("data.test.x"),
        ),
        case(
            "one definition behind a true guard",
            UNEVALUATED,
            "data.test.guarded",
            ONLY_A_GUARD_ON,
            Expect::Value("true"),
        ),
        case(
            "conflicting function behind a false guard",
            UNEVALUATED,
            "data.test.guarded_fn",
            BOTH_GUARD_OFF,
            Expect::Value(UNDEFINED),
        ),
        case(
            "conflicting function behind a true guard",
            UNEVALUATED,
            "data.test.guarded_fn",
            BOTH_GUARD_ON,
            fn_conflict("data.test.f"),
        ),
        case(
            "else value conflicts with another definition",
            ELSE_CONFLICT,
            "data.test.x",
            ONLY_C_B,
            conflict("data.test.x"),
        ),
        case(
            "else value agrees with another definition",
            ELSE_CONFLICT,
            "data.test.x",
            ONLY_C_D,
            Expect::Value("3"),
        ),
        case(
            "else function value conflicts with another definition",
            ELSE_CONFLICT,
            "data.test.r",
            r#"{"n": 2}"#,
            fn_conflict("data.test.f"),
        ),
        case(
            "else function value agrees with another definition",
            ELSE_CONFLICT,
            "data.test.r",
            r#"{"n": 3}"#,
            Expect::Value("3"),
        ),
        // OPA 1.2.0 only accepts the zero-arg function as the document
        // `data.test.f` and rejects the call `f()` at compile time.
        case(
            "zero-arg function conflict",
            ZERO_ARG,
            "data.test.r",
            BOTH,
            Expect::Conflict {
                rule: "data.test.f",
                kind: Kind::ZeroArgCall,
            },
        ),
        case(
            "zero-arg function one definition",
            ZERO_ARG,
            "data.test.r",
            ONLY_A,
            Expect::Value("1"),
        ),
        case(
            "zero-arg function document conflict",
            ZERO_ARG,
            "data.test.f",
            BOTH,
            Expect::Conflict {
                rule: "data.test.f",
                kind: Kind::ZeroArgDocument,
            },
        ),
        case(
            "zero-arg function document one definition",
            ZERO_ARG,
            "data.test.f",
            ONLY_A,
            Expect::Value("1"),
        ),
        Case {
            modules: vec![COMPLETE, VIRTUAL_LOOKUP],
            ..case(
                "conflict through virtual document lookup",
                "",
                "data.query.y",
                BOTH_KEY_X,
                conflict("data.test.x"),
            )
        },
        Case {
            modules: vec![COMPLETE, VIRTUAL_LOOKUP],
            ..case(
                "one definition through virtual document lookup",
                "",
                "data.query.y",
                ONLY_A_KEY_X,
                Expect::Value("1"),
            )
        },
        Case {
            modules: vec![COMPLETE, VIRTUAL_LOOKUP],
            ..case(
                "conflict in package document",
                "",
                "data.query.all",
                BOTH_KEY_X,
                conflict("data.test.x"),
            )
        },
        Case {
            modules: vec![COMPLETE, VIRTUAL_LOOKUP],
            ..case(
                "one definition in package document",
                "",
                "data.query.all",
                ONLY_A_KEY_X,
                Expect::Value(r#"{"x": 1}"#),
            )
        },
        case(
            "true conflicts with false",
            BOOLEAN,
            "data.test.p",
            BOTH,
            conflict("data.test.p"),
        ),
        case(
            "only true definition",
            BOOLEAN,
            "data.test.p",
            ONLY_A,
            Expect::Value("true"),
        ),
        case(
            "only false definition",
            BOOLEAN,
            "data.test.p",
            ONLY_B,
            Expect::Value("false"),
        ),
        case(
            "false agrees with false",
            BOOLEAN,
            "data.test.q",
            BOTH,
            Expect::Value("false"),
        ),
        case(
            "single false definition",
            BOOLEAN,
            "data.test.q",
            ONLY_A,
            Expect::Value("false"),
        ),
        case(
            "ref-head conflict",
            REF_HEAD,
            "data.test.p.q",
            BOTH,
            conflict("data.test.p.q"),
        ),
        case(
            "ref-head one definition",
            REF_HEAD,
            "data.test.p.q",
            ONLY_A,
            Expect::Value("1"),
        ),
        Case {
            modules: vec![REF_HEAD, REF_HEAD_LOOKUP],
            ..case(
                "ref-head conflict in parent document",
                "",
                "data.query.parent",
                BOTH,
                // Known RVM divergence: the RVM reads `data.test.p` as the value
                // of `p.q` (see the next case) and currently names the parent
                // rule `data.test.p` in the error. Only the RVM reports a rule
                // name, so the expected name is not verified against OPA; the
                // error itself is.
                conflict("data.test.p"),
            )
        },
        Case {
            modules: vec![REF_HEAD, REF_HEAD_LOOKUP],
            ..case(
                "ref-head one definition in parent document",
                "",
                "data.query.parent",
                ONLY_A,
                // The RVM returns the value of `p.q` instead of `{"q": 1}`.
                Expect::RvmDiverges {
                    want: r#"{"q": 1}"#,
                    rvm: "1",
                },
            )
        },
    ]
}

fn want_value(want: &str) -> Result<Value> {
    if want == UNDEFINED {
        return Ok(Value::Undefined);
    }
    Value::from_json_str(want)
}

fn new_engine(modules: &[&str]) -> Result<Engine> {
    let mut engine = Engine::new();
    for (idx, module) in modules.iter().enumerate() {
        engine.add_policy(format!("test{idx}.rego"), (*module).to_string())?;
    }
    Ok(engine)
}

fn new_vm(modules: &[&str], entrypoints: &[&str], mode: ExecutionMode) -> Result<RegoVM> {
    let mut engine = new_engine(modules)?;
    let first = entrypoints
        .first()
        .ok_or_else(|| anyhow!("no entrypoint"))?;
    let compiled = engine.compile_with_entrypoint(&(*first).into())?;
    let program = Compiler::compile_from_policy(&compiled, entrypoints)?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_execution_mode(mode);
    Ok(vm)
}

fn eval_vm(
    vm: &mut RegoVM,
    mode: ExecutionMode,
    entrypoint: &str,
    input: &Value,
) -> Result<Result<Value, VmError>> {
    vm.set_input(input.clone());
    let result = vm.execute_entry_point_by_name(entrypoint);
    if mode == ExecutionMode::Suspendable {
        match (&result, vm.execution_state()) {
            (Ok(_), ExecutionState::Completed { .. }) => {}
            (Ok(_), ExecutionState::Error { error }) => return Ok(Err(error.clone())),
            (Err(err), ExecutionState::Error { error }) if err.to_string() == error.to_string() => {
            }
            (_, state) => bail!("suspendable execution returned {result:?} in state {state:?}"),
        }
    }
    Ok(result)
}

fn check_interpreter(expect: &Expect, got: &Result<Value>) -> Result<()> {
    match (expect, got) {
        (Expect::Value(want) | Expect::RvmDiverges { want, .. }, Ok(got))
            if want_value(want)? == *got =>
        {
            Ok(())
        }
        (Expect::Conflict { kind, .. }, Err(err)) => {
            let display = format!("{err:#}");
            if display.contains(kind.interpreter_message()) {
                Ok(())
            } else {
                bail!(
                    "interpreter: error `{display}` lacks `{}`",
                    kind.interpreter_message()
                )
            }
        }
        (_, got) => bail!("interpreter: unexpected result {got:?}"),
    }
}

fn check_rvm(expect: &Expect, got: Result<Value, VmError>, mode: ExecutionMode) -> Result<()> {
    match (expect, got) {
        (Expect::Value(want) | Expect::RvmDiverges { rvm: want, .. }, Ok(got))
            if want_value(want)? == got => {}
        (Expect::Conflict { rule, kind }, Err(err)) => {
            let VmError::RuleConflict {
                rule: ref got_rule,
                ref message,
                ..
            } = err
            else {
                bail!("[{mode:?}] expected RuleConflict, got {err:?}");
            };
            if got_rule != rule {
                bail!("[{mode:?}] conflict reported for {got_rule}, expected {rule}");
            }
            if message != kind.rvm_message() {
                bail!(
                    "[{mode:?}] conflict message `{message}`, expected `{}`",
                    kind.rvm_message()
                );
            }
            let display = err.to_string();
            let want_display = format!("rule {rule} conflicts: {}", kind.rvm_message());
            if !display.starts_with(&want_display) {
                bail!("[{mode:?}] error `{display}` does not start with `{want_display}`");
            }
        }
        (_, got) => bail!("[{mode:?}] RVM: unexpected result {got:?}"),
    }
    Ok(())
}

const MODES: [ExecutionMode; 2] = [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable];

fn check(case: &Case) -> Result<()> {
    let input = Value::from_json_str(case.input)?;

    let mut failures = Vec::new();
    let mut engine = new_engine(&case.modules)?;
    engine.set_input(input.clone());
    let got = engine.eval_rule(case.entrypoint.into());
    if let Err(err) = check_interpreter(&case.expect, &got) {
        failures.push(format!("{err:#}"));
    }

    for mode in MODES {
        let result = new_vm(&case.modules, &[case.entrypoint], mode)
            .and_then(|mut vm| eval_vm(&mut vm, mode, case.entrypoint, &input))
            .and_then(|got| check_rvm(&case.expect, got, mode));
        if let Err(err) = result {
            failures.push(format!("{err:#}"));
        }
    }
    if !failures.is_empty() {
        bail!("{}", failures.join("; "));
    }
    Ok(())
}

#[test]
fn rule_conflicts_match_interpreter() {
    let failures: Vec<String> = cases()
        .iter()
        .filter_map(|case| {
            check(case)
                .err()
                .map(|err| format!("{}: {err:#}", case.name))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} rule conflict cases failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// A conflict aborts one evaluation. The same engine or VM must then evaluate
/// other entrypoints and inputs normally, and report a repeated conflict again.
#[test]
fn rule_conflict_does_not_poison_later_evaluations() -> Result<()> {
    const UNRELATED: &str = "data.test.unrelated";
    const GUARDED: &str = "data.test.guarded";
    const GUARDED_FN: &str = "data.test.guarded_fn";
    let x_conflict = || Expect::Conflict {
        rule: "data.test.x",
        kind: Kind::Complete,
    };
    let f_conflict = || Expect::Conflict {
        rule: "data.test.f",
        kind: Kind::Function,
    };
    let steps = [
        (GUARDED, BOTH_GUARD_ON, x_conflict()),
        (UNRELATED, BOTH_GUARD_ON, Expect::Value("true")),
        (GUARDED, BOTH_GUARD_ON, x_conflict()),
        (GUARDED, ONLY_A_GUARD_ON, Expect::Value("true")),
        (GUARDED_FN, BOTH_GUARD_ON, f_conflict()),
        (GUARDED_FN, ONLY_A_GUARD_ON, Expect::Value("true")),
        (GUARDED, BOTH_GUARD_OFF, Expect::Value(UNDEFINED)),
        (GUARDED_FN, BOTH_GUARD_ON, f_conflict()),
        (GUARDED, ONLY_A_GUARD_ON, Expect::Value("true")),
    ];

    let mut failures = Vec::new();
    let mut engine = new_engine(&[UNEVALUATED])?;
    for (step, (entrypoint, input, expect)) in steps.iter().enumerate() {
        engine.set_input(Value::from_json_str(input)?);
        let got = engine.eval_rule((*entrypoint).into());
        if let Err(err) = check_interpreter(expect, &got) {
            failures.push(format!("step {step} {entrypoint}: {err:#}"));
        }
    }
    for mode in MODES {
        let mut vm = new_vm(&[UNEVALUATED], &[GUARDED, UNRELATED, GUARDED_FN], mode)?;
        for (step, (entrypoint, input, expect)) in steps.iter().enumerate() {
            let result = eval_vm(&mut vm, mode, entrypoint, &Value::from_json_str(input)?)
                .and_then(|got| check_rvm(expect, got, mode));
            if let Err(err) = result {
                failures.push(format!("step {step} {entrypoint}: {err:#}"));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} reuse steps failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
    Ok(())
}

/// A conflict that is only reached after the VM suspended and resumed is
/// reported by `resume`, and the VM evaluates the next entry point normally.
#[test]
fn rule_conflict_after_resume() -> Result<()> {
    const AWAITED: &str = r#"package test
x := 1 if input.a
x := v if {
  input.b
  v := __builtin_host_await(1, "id")
}
"#;
    const ENTRYPOINT: &str = "data.test.x";
    let conflict = Expect::Conflict {
        rule: ENTRYPOINT,
        kind: Kind::Complete,
    };
    let both = Value::from_json_str(BOTH)?;
    let only_a = Value::from_json_str(ONLY_A)?;

    let mut failures = Vec::new();
    for (response, expect) in [(2, &conflict), (1, &Expect::Value("1"))] {
        let mut vm = new_vm(&[AWAITED], &[ENTRYPOINT], ExecutionMode::Suspendable)?;
        vm.set_input(both.clone());
        vm.execute_entry_point_by_name(ENTRYPOINT)?;
        if !matches!(vm.execution_state(), ExecutionState::Suspended { .. }) {
            bail!("expected suspension, got {:?}", vm.execution_state());
        }
        let resumed = vm.resume(Some(Value::from(response)));
        let resumed = match (&resumed, vm.execution_state()) {
            (Ok(_), ExecutionState::Completed { result }) => Ok(result.clone()),
            _ => resumed,
        };
        if let Err(err) = check_rvm(expect, resumed, ExecutionMode::Suspendable) {
            failures.push(format!("resume with {response}: {err:#}"));
        }
        let result = eval_vm(&mut vm, ExecutionMode::Suspendable, ENTRYPOINT, &only_a)
            .and_then(|got| check_rvm(&Expect::Value("1"), got, ExecutionMode::Suspendable));
        if let Err(err) = result {
            failures.push(format!("after resume with {response}: {err:#}"));
        }

        let mut vm = new_vm(&[AWAITED], &[ENTRYPOINT], ExecutionMode::RunToCompletion)?;
        vm.set_host_await_responses([(Value::from("id"), [Value::from(response)])]);
        let result = eval_vm(&mut vm, ExecutionMode::RunToCompletion, ENTRYPOINT, &both)
            .and_then(|got| check_rvm(expect, got, ExecutionMode::RunToCompletion));
        if let Err(err) = result {
            failures.push(format!("preloaded response {response}: {err:#}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} resume checks failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
    Ok(())
}
