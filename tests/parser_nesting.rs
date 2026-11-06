// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{anyhow, Result};
use regorus::unstable::{Parser, Source};
use regorus::{Engine, Value};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const CHILD: &str = "REGORUS_PARSER_NESTING_CHILD";

fn nested(open: &str, leaf: &str, close: &str, depth: usize) -> String {
    format!("{}{leaf}{}", open.repeat(depth), close.repeat(depth))
}

fn parse_expression(text: &str) -> Result<()> {
    let source = Source::from_contents("nesting.rego".to_string(), text.to_string())?;
    Parser::new(&source)?.parse_expr()?;
    Ok(())
}

fn expect_nesting_error<T>(result: Result<T>) {
    let error = result.err().expect("deep source must fail to parse");
    assert!(
        error
            .to_string()
            .contains("expression nesting too deep (>32)"),
        "{error}"
    );
}

fn check_recovery(text: &str) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "safe.rego".to_string(),
        "package safe\nanswer := 7".to_string(),
    )?;
    for _ in 0..2 {
        expect_nesting_error(engine.add_policy(
            "bad.rego".to_string(),
            format!("package bad\nbefore := 1\nresult := {text}"),
        ));
        assert_eq!(
            engine.eval_rule("data.safe.answer".to_string())?,
            Value::from(7)
        );
        expect_nesting_error(engine.eval_query(text.to_string(), false));
        assert_eq!(
            engine.eval_rule("data.safe.answer".to_string())?,
            Value::from(7)
        );
        assert!(engine.eval_bool_query("1 == 1".to_string(), false)?);
    }
    engine.add_policy(
        "next.rego".to_string(),
        "package next\nanswer := 8".to_string(),
    )?;
    assert_eq!(
        engine.eval_rule("data.next.answer".to_string())?,
        Value::from(8)
    );

    #[cfg(feature = "rvm")]
    {
        use regorus::languages::rego::compiler::Compiler;
        use regorus::rvm::vm::RegoVM;
        let policy = engine.compile_with_entrypoint(&"data.safe.answer".into())?;
        let program = Compiler::compile_from_policy(&policy, &["data.safe.answer"])?;
        let mut vm = RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.safe.answer")?,
            Value::from(7)
        );
    }
    Ok(())
}

fn check_boundaries() -> Result<()> {
    for (open, close) in [
        ("[", "]"),
        ("count(", ")"),
        ("(", ")"),
        ("{1:", "}"),
        ("{", "}"),
        ("input[", "]"),
        ("- ", ""),
    ] {
        parse_expression(&nested(open, "1", close, 31))?;
        expect_nesting_error(parse_expression(&nested(open, "1", close, 32)));
    }
    parse_expression(&nested("[1 | ", "true", "]", 31))?;
    expect_nesting_error(parse_expression(&nested("[1 | ", "true", "]", 32)));
    for (open, leaf, close) in [("[", "[]", "]"), ("f(", "f()", ")")] {
        parse_expression(&nested(open, leaf, close, 31))?;
        expect_nesting_error(parse_expression(&nested(open, leaf, close, 32)));
    }
    for (depth, accept) in [(31, true), (32, false)] {
        let text = nested("every x in input {\n", "true", "\n}", depth);
        let source = Source::from_contents("every.rego".to_string(), text)?;
        let mut parser = Parser::new(&source)?;
        parser.enable_rego_v1()?;
        let result = parser.parse_user_query();
        if accept {
            result?;
        } else {
            expect_nesting_error(result);
        }
    }
    let array = nested("[", "1", "]", 31);
    let mut engine = Engine::new();
    engine.add_policy(
        "boundary.rego".to_string(),
        format!("package boundary\nvalue := {array}\nanswer := count(value)"),
    )?;
    assert_eq!(
        engine.eval_rule("data.boundary.answer".to_string())?,
        Value::from(1)
    );
    let valid_calls = nested("count([", "1", "])", 15);
    engine.add_policy(
        "calls.rego".to_string(),
        format!("package calls\nanswer := {valid_calls}"),
    )?;
    assert_eq!(
        engine.eval_rule("data.calls.answer".to_string())?,
        Value::from(1)
    );
    #[cfg(feature = "rvm")]
    {
        use regorus::languages::rego::compiler::Compiler;
        use regorus::rvm::vm::RegoVM;
        let policy = engine.compile_with_entrypoint(&"data.boundary.answer".into())?;
        let program =
            Compiler::compile_from_policy(&policy, &["data.boundary.answer", "data.calls.answer"])?;
        let mut vm = RegoVM::new();
        vm.load_program(program);
        assert_eq!(
            vm.execute_entry_point_by_name("data.boundary.answer")?,
            Value::from(1)
        );
        assert_eq!(
            vm.execute_entry_point_by_name("data.calls.answer")?,
            Value::from(1)
        );
    }
    Ok(())
}

fn child_case(case: &str) -> Result<()> {
    match case {
        "boundaries" => check_boundaries(),
        "wide-statements" => {
            for statement in ["\"ok\"\n", "`ok`\n", "[1]\n", "(true)\n"] {
                let source = Source::from_contents(
                    "wide.rego".to_string(),
                    format!("{{\n{}}}", statement.repeat(8192)),
                )?;
                let query = Parser::new(&source)?.parse_query_or_literal_stmt()?;
                assert_eq!(query.stmts.len(), 8192);
            }
            Ok(())
        }
        "arrays" => check_recovery(&nested("[\n", "1", "\n]", 4096)),
        "calls" => check_recovery(&nested("count(\n", "1", "\n)", 4096)),
        "set-lookahead" => check_recovery(&nested("set(\n", "1", "\n)", 4096)),
        "later-arguments" => check_recovery(&nested("f(0,\n", "1", "\n)", 4096)),
        "objects" => check_recovery(&nested("{1:\n", "1", "\n}", 4096)),
        "sets" => check_recovery(&nested("{\n", "1", "\n}", 4096)),
        "indices" => check_recovery(&nested("input[\n", "1", "\n]", 4096)),
        "comprehensions" => check_recovery(&nested("[\n", "1", "\n| true]", 4096)),
        "every" => {
            let text = nested("every x in [1] {\n", "true", "\n}", 4096);
            let mut engine = Engine::new();
            expect_nesting_error(engine.add_policy(
                "every.rego".to_string(),
                format!("package p\nr if {{ {text} }}"),
            ));
            expect_nesting_error(engine.eval_query(text, false));
            assert!(engine.eval_bool_query("true".to_string(), false)?);
            Ok(())
        }
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        "resources" => {
            let wide = format!("[{}]", vec!["1"; 256].join(","));
            for text in [
                wide.clone(),
                format!("{{1: {wide}}}"),
                format!("[x | x := {wide}]"),
            ] {
                let source = Source::from_contents("resource.rego".to_string(), text)?;
                let mut parser = Parser::new(&source)?;
                regorus::set_global_memory_limit(Some(1));
                let result = parser.parse_expr();
                regorus::set_global_memory_limit(None);
                let error = result
                    .err()
                    .ok_or_else(|| anyhow!("memory failure was lost"))?;
                assert!(
                    matches!(
                        error.downcast_ref::<regorus::LimitError>(),
                        Some(regorus::LimitError::MemoryLimitExceeded { .. })
                    ),
                    "{error}"
                );
            }
            Ok(())
        }
        _ => Err(anyhow!("unknown parser regression case: {case}")),
    }
}

fn run_child(case: &str) -> Result<()> {
    let mut child = Command::new(std::env::current_exe()?)
        .args(["--exact", "parser_nesting_native_stack", "--nocapture"])
        .env(CHILD, case)
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit())
        .spawn()?;
    let deadline = Instant::now() + Duration::from_secs(30);
    loop {
        if let Some(status) = child.try_wait()? {
            assert!(status.success(), "parser case {case} failed: {status}");
            return Ok(());
        }
        if Instant::now() >= deadline {
            child.kill()?;
            child.wait()?;
            return Err(anyhow!("parser case {case} exceeded its deadline"));
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn parser_nesting_native_stack() -> Result<()> {
    if let Some(case) = std::env::var_os(CHILD) {
        let case = case.to_string_lossy().into_owned();
        return std::thread::Builder::new()
            .stack_size(1_048_576)
            .spawn(move || child_case(&case))?
            .join()
            .map_err(|_| anyhow!("parser regression worker panicked"))?;
    }
    for case in [
        "arrays",
        "calls",
        "set-lookahead",
        "later-arguments",
        "objects",
        "sets",
        "indices",
        "comprehensions",
        "every",
        #[cfg(all(feature = "allocator-memory-limits", not(miri)))]
        "resources",
        "boundaries",
        "wide-statements",
    ] {
        run_child(case)?;
    }
    Ok(())
}
