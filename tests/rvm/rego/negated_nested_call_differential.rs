// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Differential test for `not` over an expression that contains nested calls.
//!
//! OPA evaluates every call nested inside the operands of a negated expression
//! before the negation (`not count(x) == 1` runs as
//! `__local0__ := count(x); not __local0__ == 1`). When such a call is
//! Undefined, for example because a builtin fails without strict mode or a
//! function is undefined for its arguments, the enclosing body fails instead
//! of `not` turning the Undefined into `true`. A failure of the negated call
//! itself (`not count(x)`) still makes `not` succeed.
//!
//! Each case runs in the interpreter and in both RVM execution modes, with and
//! without strict builtin errors, and has a twin whose nested calls succeed.
//! The expected values were checked against OPA 1.2.0 with and without
//! `--strict-builtin-errors`, with operands read from input so that OPA's type
//! checker cannot reject the policies at compile time.

use anyhow::{bail, Result};
use regorus::languages::rego::compiler::Compiler;
use regorus::rvm::vm::{ExecutionMode, ExecutionState, RegoVM, VmError};
use regorus::{Engine, Value};

const ENTRYPOINT: &str = "data.test.y";
const UNDEFINED: &str = "#undefined";

enum Expect {
    Value(&'static str),
    /// OPA and the interpreter raise an error containing `message`. The RVM
    /// does not consistently raise strict builtin errors yet (a separate fix):
    /// it either raises the error or returns `rvm`, the value it gets by
    /// treating the error as a failure of the enclosing body.
    Error {
        message: &'static str,
        rvm: &'static str,
    },
}

struct Case {
    name: &'static str,
    rules: &'static str,
    input: &'static str,
    non_strict: Expect,
    strict: Expect,
}

const COUNT_ERROR: &str = "requires array/object/set/string";

const fn case(
    name: &'static str,
    rules: &'static str,
    input: &'static str,
    non_strict: Expect,
    strict: Expect,
) -> Case {
    Case {
        name,
        rules,
        input,
        non_strict,
        strict,
    }
}

/// The same value with and without strict builtin errors.
const fn same(
    name: &'static str,
    rules: &'static str,
    input: &'static str,
    value: &'static str,
) -> Case {
    case(
        name,
        rules,
        input,
        Expect::Value(value),
        Expect::Value(value),
    )
}

const fn error(message: &'static str, rvm: &'static str) -> Expect {
    Expect::Error { message, rvm }
}

const NOT_COUNT: &str = "y if not count(input.v) == 1";
const NOT_COUNT_IN: &str = "y if not count(input.v) in [1]";
const NOT_COUNT_ARRAY: &str = "y if not [count(input.v)] == [1]";
const NOT_COUNT_BARE: &str = "y if not count(input.v)";
const NOT_DIV: &str = "y if not input.a / input.b == 1";
const NOT_NESTED_ARG: &str = r#"y if not startswith(upper(input.s), "a")"#;
const NOT_FAILING_CALL: &str = r#"y if not startswith(input.s, "a")"#;
const NOT_CALL_CHAIN: &str = "y if not abs(to_number(input.v)) == 1";
const NOT_FUNCTION_ARG: &str = "f(_) := 1\ny if not f(count(input.v)) == 2";
const NOT_INDEX_FIELD: &str = "y if not input.x[count(input.v)].k == 1";
const NOT_OBJECT_OPERAND: &str = r#"y if not {"a": count(input.v)} == {"a": 1}"#;
const NOT_SET_OPERAND: &str = "y if not {count(input.v)} == {1}";
const NOT_COMPREHENSION_OPERAND: &str = "y if not [count(input.v) | true] == [1]";
const NOT_FUNCTION: &str = "f(x) := 1 if x > 0\ny if not f(input.v) == 2";
const NOT_IN_BODY: &str = "y if {\n  input.w == 1\n  not count(input.v) == 1\n  input.w > 0\n}";
const NOT_DEFAULT: &str = "default y := false\ny if not count(input.v) == 1";
const NOT_ELSE: &str = "y := 1 if { not count(input.v) == 1 } else := 2";
const NOT_IN_FUNCTION: &str = "f(v) if not count(v) == 1\ny := f(input.v)";
const NOT_IN_COMPREHENSION: &str = "y := [1 | not count(input.v) == 1]";
const NOT_IN_ITERATION: &str = "y := [x | some x in input.vs; not count(x) == 1]";
const NOT_IN_EVERY: &str = "y if every x in input.vs { not count(x) == 1 }";
const NOT_LOOP: &str = "y if not count(input.vs[_]) == 1";
const NOT_CLOSED_COMPREHENSION: &str = "y if not count([1 | input.v[_]]) == 1";

fn cases() -> Vec<Case> {
    use Expect::Value as V;
    vec![
        case(
            "count",
            NOT_COUNT,
            r#"{"v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same("count twin", NOT_COUNT, r#"{"v": [1, 2]}"#, "true"),
        same("count twin equal", NOT_COUNT, r#"{"v": [1]}"#, UNDEFINED),
        same("count of undefined", NOT_COUNT, "{}", UNDEFINED),
        case(
            "membership",
            NOT_COUNT_IN,
            r#"{"v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same("membership twin", NOT_COUNT_IN, r#"{"v": [1, 2]}"#, "true"),
        case(
            "array operand",
            NOT_COUNT_ARRAY,
            r#"{"v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "array operand twin",
            NOT_COUNT_ARRAY,
            r#"{"v": [1, 2]}"#,
            "true",
        ),
        case(
            "object operand",
            NOT_OBJECT_OPERAND,
            r#"{"v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "object operand twin",
            NOT_OBJECT_OPERAND,
            r#"{"v": [1, 2]}"#,
            "true",
        ),
        case(
            "set operand",
            NOT_SET_OPERAND,
            r#"{"v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "set operand twin",
            NOT_SET_OPERAND,
            r#"{"v": [1, 2]}"#,
            "true",
        ),
        // The negated call itself is not lifted: its failure makes `not`
        // succeed.
        case(
            "failing negated call",
            NOT_COUNT_BARE,
            r#"{"v": 5}"#,
            V("true"),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "failing negated call twin",
            NOT_COUNT_BARE,
            r#"{"v": [1]}"#,
            UNDEFINED,
        ),
        case(
            "failing negated call with arguments",
            NOT_FAILING_CALL,
            r#"{"s": 5}"#,
            V("true"),
            error("`startswith` expects string argument", UNDEFINED),
        ),
        same(
            "failing negated call with arguments twin",
            NOT_FAILING_CALL,
            r#"{"s": "abc"}"#,
            UNDEFINED,
        ),
        case(
            "divide by zero",
            NOT_DIV,
            r#"{"a": 1, "b": 0}"#,
            V(UNDEFINED),
            error("divide by zero", UNDEFINED),
        ),
        same("divide twin", NOT_DIV, r#"{"a": 1, "b": 2}"#, "true"),
        case(
            "nested call argument",
            NOT_NESTED_ARG,
            r#"{"s": 5}"#,
            V(UNDEFINED),
            error("`upper` expects string argument", UNDEFINED),
        ),
        same(
            "nested call argument twin",
            NOT_NESTED_ARG,
            r#"{"s": "b"}"#,
            "true",
        ),
        case(
            "call chain",
            NOT_CALL_CHAIN,
            r#"{"v": "x"}"#,
            V(UNDEFINED),
            error("could not parse", UNDEFINED),
        ),
        same("call chain twin", NOT_CALL_CHAIN, r#"{"v": "2"}"#, "true"),
        case(
            "function argument",
            NOT_FUNCTION_ARG,
            r#"{"v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "function argument twin",
            NOT_FUNCTION_ARG,
            r#"{"v": [1]}"#,
            "true",
        ),
        case(
            "index field",
            NOT_INDEX_FIELD,
            r#"{"x": [{"k": 0}], "v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "index field twin",
            NOT_INDEX_FIELD,
            r#"{"x": [{"k": 0}], "v": []}"#,
            "true",
        ),
        same("undefined function", NOT_FUNCTION, r#"{"v": 0}"#, UNDEFINED),
        same(
            "undefined function twin",
            NOT_FUNCTION,
            r#"{"v": 1}"#,
            "true",
        ),
        case(
            "rule body",
            NOT_IN_BODY,
            r#"{"v": 5, "w": 1}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "rule body twin",
            NOT_IN_BODY,
            r#"{"v": [1, 2], "w": 1}"#,
            "true",
        ),
        case(
            "default",
            NOT_DEFAULT,
            r#"{"v": 5}"#,
            V("false"),
            error(COUNT_ERROR, "false"),
        ),
        same("default twin", NOT_DEFAULT, r#"{"v": [1, 2]}"#, "true"),
        case(
            "else",
            NOT_ELSE,
            r#"{"v": 5}"#,
            V("2"),
            error(COUNT_ERROR, "2"),
        ),
        same("else twin", NOT_ELSE, r#"{"v": [1, 2]}"#, "1"),
        case(
            "function body",
            NOT_IN_FUNCTION,
            r#"{"v": 5}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "function body twin",
            NOT_IN_FUNCTION,
            r#"{"v": [1, 2]}"#,
            "true",
        ),
        case(
            "comprehension",
            NOT_IN_COMPREHENSION,
            r#"{"v": 5}"#,
            V("[]"),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "comprehension twin",
            NOT_IN_COMPREHENSION,
            r#"{"v": [1, 2]}"#,
            "[1]",
        ),
        case(
            "comprehension iteration",
            NOT_IN_ITERATION,
            r#"{"vs": [5, [1, 2], [1]]}"#,
            V("[[1, 2]]"),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "comprehension iteration twin",
            NOT_IN_ITERATION,
            r#"{"vs": [[3], [1, 2], [1]]}"#,
            "[[1, 2]]",
        ),
        case(
            "every",
            NOT_IN_EVERY,
            r#"{"vs": [5, [1, 2]]}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same("every twin", NOT_IN_EVERY, r#"{"vs": [[1, 2]]}"#, "true"),
        case(
            "loop",
            NOT_LOOP,
            r#"{"vs": [[1], 5]}"#,
            V(UNDEFINED),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same("loop twin", NOT_LOOP, r#"{"vs": [[1], [1, 2]]}"#, "true"),
        same(
            "loop twin equal",
            NOT_LOOP,
            r#"{"vs": [[1], [2]]}"#,
            UNDEFINED,
        ),
        // A comprehension is evaluated as a whole; its body is not lifted.
        same(
            "closed comprehension",
            NOT_CLOSED_COMPREHENSION,
            r#"{"v": 5}"#,
            "true",
        ),
        same(
            "closed comprehension twin",
            NOT_CLOSED_COMPREHENSION,
            r#"{"v": [5]}"#,
            UNDEFINED,
        ),
        case(
            "comprehension operand",
            NOT_COMPREHENSION_OPERAND,
            r#"{"v": 5}"#,
            V("true"),
            error(COUNT_ERROR, UNDEFINED),
        ),
        same(
            "comprehension operand twin",
            NOT_COMPREHENSION_OPERAND,
            r#"{"v": [1]}"#,
            UNDEFINED,
        ),
    ]
}

fn want_value(want: &str) -> Result<Value> {
    if want == UNDEFINED {
        return Ok(Value::Undefined);
    }
    Value::from_json_str(want)
}

fn new_engine(module: &str, strict: bool) -> Result<Engine> {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(strict);
    engine.add_policy("test.rego".to_string(), module.to_string())?;
    Ok(engine)
}

fn eval_interpreter(module: &str, input: &Value, strict: bool) -> Result<Result<Value>> {
    let mut engine = new_engine(module, strict)?;
    engine.set_input(input.clone());
    Ok(engine.eval_rule(ENTRYPOINT.to_string()))
}

fn eval_vm(
    module: &str,
    input: &Value,
    strict: bool,
    mode: ExecutionMode,
) -> Result<Result<Value, VmError>> {
    let mut engine = new_engine(module, strict)?;
    let compiled = engine.compile_with_entrypoint(&ENTRYPOINT.into())?;
    let program = Compiler::compile_from_policy(&compiled, &[ENTRYPOINT])?;
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_execution_mode(mode);
    vm.set_strict_builtin_errors(strict);
    vm.set_input(input.clone());
    let result = vm.execute_entry_point_by_name(ENTRYPOINT);
    if mode == ExecutionMode::Suspendable {
        match (&result, vm.execution_state()) {
            (Ok(_), ExecutionState::Completed { .. }) => {}
            (Err(err), ExecutionState::Error { error }) if err.to_string() == error.to_string() => {
            }
            (_, state) => bail!("suspendable execution returned {result:?} in state {state:?}"),
        }
    }
    Ok(result)
}

fn check(case: &Case, strict: bool, expect: &Expect) -> Result<Vec<String>> {
    let module = format!("package test\n\n{}\n", case.rules);
    let input = Value::from_json_str(case.input)?;
    let mut failures = Vec::new();

    let got = eval_interpreter(&module, &input, strict)?;
    let ok = match (expect, &got) {
        (Expect::Value(want), Ok(got)) => want_value(want)? == *got,
        (Expect::Error { message, .. }, Err(err)) => format!("{err:#}").contains(message),
        _ => false,
    };
    if !ok {
        failures.push(format!("interpreter: unexpected result {got:?}"));
    }

    for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
        let got = eval_vm(&module, &input, strict, mode)?;
        let ok = match (expect, &got) {
            (Expect::Value(want) | Expect::Error { rvm: want, .. }, Ok(got)) => {
                want_value(want)? == *got
            }
            (Expect::Error { message, .. }, Err(err)) => err.to_string().contains(message),
            (Expect::Value(_), Err(_)) => false,
        };
        if !ok {
            failures.push(format!("[{mode:?}] RVM: unexpected result {got:?}"));
        }
    }
    Ok(failures)
}

#[test]
fn negated_nested_calls_match_opa() -> Result<()> {
    let mut failures = Vec::new();
    for case in cases() {
        for (strict, expect) in [(false, &case.non_strict), (true, &case.strict)] {
            let label = if strict { "strict" } else { "non-strict" };
            for failure in check(&case, strict, expect)? {
                failures.push(format!("{} ({label}): {failure}", case.name));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} negated nested call checks failed:\n{}",
        failures.len(),
        failures.join("\n")
    );
    Ok(())
}

/// The interpreter evaluates each lifted call once, as OPA and the RVM do:
/// `h` prints once whether it is undefined, defined but the negated
/// expression is undefined, or the negated expression is defined.
#[test]
fn negated_nested_calls_are_evaluated_once() -> Result<()> {
    let module = "package test\n\nh(x) := 1 if {\n  print(\"h\")\n  x == 1\n}\n\ny if not h(input.v) == input.w\n";
    for (input, want) in [
        (r#"{"v": 5}"#, UNDEFINED),
        (r#"{"v": 1}"#, "true"),
        (r#"{"v": 1, "w": 1}"#, UNDEFINED),
    ] {
        let mut engine = new_engine(module, false)?;
        engine.set_gather_prints(true);
        engine.set_input(Value::from_json_str(input)?);
        assert_eq!(engine.eval_rule(ENTRYPOINT.to_string())?, want_value(want)?);
        let prints = engine.take_prints()?;
        assert_eq!(prints.len(), 1, "input {input}: {prints:?}");
    }
    Ok(())
}
