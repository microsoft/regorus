// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "std")]

use anyhow::{anyhow, Result};
use regorus::unstable::{Parser, Source};
use regorus::{Engine, Value};

mod native_depth_support;

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
        error.to_string().contains("expression nesting too deep"),
        "{error}"
    );
}

fn check_recovery(text: &str) -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy("safe.rego".into(), "package safe\nanswer := 7".into())?;
    for _ in 0..2 {
        expect_nesting_error(engine.add_policy(
            "bad.rego".into(),
            format!("package bad\nbefore := 1\nresult := {text}"),
        ));
        expect_nesting_error(engine.eval_query(text.to_string(), false));
        assert_eq!(engine.eval_rule("data.safe.answer".into())?, Value::from(7));
        assert!(engine
            .eval_query("data.bad.result".into(), false)?
            .result
            .is_empty());
        assert!(engine.eval_bool_query("1 == 1".into(), false)?);
    }
    engine.add_policy("next.rego".into(), "package next\nanswer := 8".into())?;
    assert_eq!(engine.eval_rule("data.next.answer".into())?, Value::from(8));

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

fn on_parser_stack(test_name: &str, check: fn() -> Result<()>) -> Result<()> {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess(test_name);
        return Ok(());
    }
    std::thread::Builder::new()
        .stack_size(1_500_000)
        .spawn(check)?
        .join()
        .map_err(|_| anyhow!("parser regression worker panicked"))?
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn parser_rejects_deep_terms_and_remains_usable() -> Result<()> {
    on_parser_stack("parser_rejects_deep_terms_and_remains_usable", || {
        for (open, close) in [
            ("[\n", "\n]"),
            ("count(\n", "\n)"),
            ("set(\n", "\n)"),
            ("f(0,\n", "\n)"),
            ("{1:\n", "\n}"),
            ("{\n", "\n}"),
            ("input[\n", "\n]"),
            ("(\n", "\n)"),
            ("- \n", ""),
            ("[\n", "\n| true]"),
            ("[0 | \n", "\n]"),
            ("{0 | \n", "\n}"),
            ("{\"k\": 0 | \n", "\n}"),
        ] {
            check_recovery(&nested(open, "1", close, 4096))?;
        }
        let every = nested("every x in [1] {\n", "true", "\n}", 4096);
        let mut engine = Engine::new();
        expect_nesting_error(engine.add_policy(
            "every.rego".into(),
            format!("package p\nr if {{ {every} }}"),
        ));
        expect_nesting_error(engine.eval_query(every, false));
        assert!(engine.eval_bool_query("true".into(), false)?);
        Ok(())
    })
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn parser_preserves_term_boundaries() -> Result<()> {
    on_parser_stack("parser_preserves_term_boundaries", || {
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
        for (open, leaf, close, depth) in [("[", "[]", "]", 31), ("f(", "f()", ")", 30)] {
            parse_expression(&nested(open, leaf, close, depth))?;
            expect_nesting_error(parse_expression(&nested(open, leaf, close, depth + 1)));
        }
        // Query bodies also use the inherited depth budget, unlike plain term wrappers.
        for open in ["[0 | ", "{0 | ", "{\"k\": 0 | "] {
            let close = if open.starts_with('[') { "]" } else { "}" };
            parse_expression(&nested(open, "true", close, 14))?;
            expect_nesting_error(parse_expression(&nested(open, "true", close, 32)));
        }
        for (depth, accept) in [(14, true), (32, false)] {
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
        let calls = nested("count([", "1", "])", 15);
        let mut engine = Engine::new();
        engine.add_policy(
            "boundary.rego".to_string(),
            format!("package boundary\nvalue := {array}\nanswer := count(value)"),
        )?;
        engine.add_policy(
            "calls.rego".to_string(),
            format!("package calls\nanswer := {calls}"),
        )?;
        for entrypoint in ["data.boundary.answer", "data.calls.answer"] {
            assert_eq!(engine.eval_rule(entrypoint.to_string())?, Value::from(1));
        }
        #[cfg(feature = "rvm")]
        {
            use regorus::languages::rego::compiler::Compiler;
            use regorus::rvm::vm::RegoVM;
            let policy = engine.compile_with_entrypoint(&"data.boundary.answer".into())?;
            let program = Compiler::compile_from_policy(
                &policy,
                &["data.boundary.answer", "data.calls.answer"],
            )?;
            let mut vm = RegoVM::new();
            vm.load_program(program);
            for entrypoint in ["data.boundary.answer", "data.calls.answer"] {
                assert_eq!(vm.execute_entry_point_by_name(entrypoint)?, Value::from(1));
            }
        }
        Ok(())
    })
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn parser_accepts_wide_shallow_statements() -> Result<()> {
    on_parser_stack("parser_accepts_wide_shallow_statements", || {
        for statement in ["\"ok\"\n", "`ok`\n", "[1]\n", "(true)\n"] {
            let source = Source::from_contents(
                "wide.rego".to_string(),
                format!("{{\n{}}}", statement.repeat(8192)),
            )?;
            let query = Parser::new(&source)?.parse_query_or_literal_stmt()?;
            assert_eq!(query.stmts.len(), 8192);
        }
        Ok(())
    })
}

#[test]
#[cfg(all(feature = "allocator-memory-limits", not(miri)))]
fn parser_lookahead_preserves_typed_memory_errors() -> Result<()> {
    on_parser_stack("parser_lookahead_preserves_typed_memory_errors", || {
        let wide = format!("[{}]", vec!["1"; 256].join(","));
        for text in [
            wide.clone(),
            format!("{{1: {wide}}}"),
            format!("[x | x := {wide}]"),
            "{0 | true}".into(),
            "{\"k\": 0 | true}".into(),
        ] {
            let source = Source::from_contents("resource.rego".into(), text)?;
            let mut parser = Parser::new(&source)?;
            regorus::set_global_memory_limit(Some(1));
            let result = parser.parse_query_or_literal_stmt();
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
    })
}
