// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "std")]

use regorus::unstable::{Parser, Source};
use regorus::{Engine, Value};

mod native_depth_support;

const LIMIT: usize = 32;

fn chain(operator: &str, depth: usize) -> String {
    format!("1{}", format!("\n{operator}1").repeat(depth))
}

fn parse_expression(expression: &str) -> anyhow::Result<()> {
    let source = Source::from_contents("arithmetic-depth.rego".into(), expression.into())?;
    let mut parser = Parser::new(&source)?;
    parser.enable_rego_v1()?;
    drop(parser.parse_expr()?);
    Ok(())
}

fn expect_depth_error(expression: &str) {
    let error = parse_expression(expression).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("arithmetic expression nesting too deep"),
        "{error}"
    );
}

#[test]
fn arithmetic_depth_boundaries() {
    for operator in ["+", "-", "*", "/", "%"] {
        for depth in [LIMIT - 1, LIMIT] {
            parse_expression(&chain(operator, depth)).unwrap();
        }
        expect_depth_error(&chain(operator, LIMIT + 1));
    }

    // Both precedence levels and the subtraction-as-negative-token path count.
    parse_expression(&format!("{}+1*1", chain("+", LIMIT - 1))).unwrap();
    expect_depth_error(&format!("{}+1*1", chain("*", LIMIT)));
    expect_depth_error(&format!("{}-1", chain("+", LIMIT)));
    expect_depth_error(&format!("1+({})", chain("+", LIMIT)));

    let mut nested = "1".to_owned();
    for _ in 0..8 {
        nested = format!("abs({nested}{})", "\n+1".repeat(4));
    }
    parse_expression(&nested).unwrap();
    expect_depth_error(&format!("1+{nested}"));

    let mut balanced = "1".to_owned();
    for _ in 0..6 {
        balanced = format!("({balanced}+{balanced})");
    }
    // 63 operators, but only six arithmetic nodes along any path.
    parse_expression(&balanced).unwrap();
}

#[test]
fn arithmetic_depth_survives_parser_recovery() {
    let deep = chain("+", LIMIT + 1);
    for expression in [
        format!("[{deep}]"),
        format!("[abs({deep})]"),
        format!("{{{deep}}}"),
        format!("{{\"key\": {deep}}}"),
        format!("abs({deep})"),
        format!("[x | x := {deep}]"),
        format!("{{\"key\": x | x := {deep}}}"),
    ] {
        expect_depth_error(&expression);
    }
    // Arithmetic in non-arithmetic operands contributes to the same path.
    let allowed = chain("+", LIMIT);
    for expression in [
        format!("1 + abs({allowed})"),
        format!("1 + [{allowed}][0]"),
        format!("1 + {{\"key\": {allowed}}}.key"),
        format!("1 + count([x | x := {allowed}])"),
        format!("1 + count([x | some x in [{allowed}]])"),
        format!("1 + count([x | x := 1 with input as {allowed}])"),
        format!("1 + count([x | x := 1; every y in [{allowed}] {{ y > 0 }}])"),
        format!("1 + (false == [{allowed}])"),
        format!("1 + (-({allowed}))"),
    ] {
        expect_depth_error(&expression);
    }
}

fn check_policy_lifecycle() {
    let mut engine = Engine::new();
    engine
        .add_policy("safe.rego".into(), "package safe\nr := 7".into())
        .unwrap();
    let deep = chain("+", 2_000);
    for _ in 0..2 {
        let error = engine
            .add_policy(
                "rejected.rego".into(),
                format!("package rejected\nr := {deep}"),
            )
            .unwrap_err();
        assert!(error
            .to_string()
            .contains("arithmetic expression nesting too deep"));
        let error = engine.eval_query(deep.clone(), false).unwrap_err();
        assert!(error
            .to_string()
            .contains("arithmetic expression nesting too deep"));
        assert_eq!(
            engine.eval_rule("data.safe.r".into()).unwrap(),
            Value::from(7)
        );
    }

    engine
        .add_policy(
            "accepted.rego".into(),
            format!("package accepted\nr := {}", chain("+", LIMIT)),
        )
        .unwrap();
    assert_eq!(
        engine.eval_rule("data.accepted.r".into()).unwrap(),
        Value::from(LIMIT + 1)
    );
    let mut nested = "1".to_owned();
    for _ in 0..8 {
        nested = format!("abs({nested}{})", "\n+1".repeat(4));
    }
    engine
        .add_policy(
            "semantics.rego".into(),
            format!(
                "package semantics\nnested := {nested}\nsub := 10-3-2\ndiv := 20/2/5\nprecedence := 1+2*3"
            ),
        )
        .unwrap();
    let cases = [
        ("data.accepted.r", LIMIT + 1),
        ("data.semantics.nested", LIMIT + 1),
        ("data.semantics.sub", 5),
        ("data.semantics.div", 2),
        ("data.semantics.precedence", 7),
    ];
    for (entry, expected) in cases {
        assert_eq!(
            engine.eval_rule(entry.into()).unwrap(),
            Value::from(expected)
        );
    }
    #[cfg(feature = "rvm")]
    {
        use regorus::languages::rego::compiler::Compiler;
        use regorus::rvm::vm::{ExecutionMode, RegoVM};
        use regorus::Rc;
        let policy = engine
            .compile_with_entrypoint(&Rc::from("data.accepted.r"))
            .unwrap();
        let entries = cases.map(|(entry, _)| entry);
        let program = Compiler::compile_from_policy(&policy, &entries).unwrap();
        for mode in [ExecutionMode::RunToCompletion, ExecutionMode::Suspendable] {
            let mut vm = RegoVM::new();
            vm.load_program(program.clone());
            vm.set_execution_mode(mode);
            for (entry, expected) in cases {
                assert_eq!(
                    vm.execute_entry_point_by_name(entry).unwrap(),
                    Value::from(expected)
                );
            }
        }
        let source = Source::from_contents("direct.rego".into(), nested).unwrap();
        let expr = regorus::unstable::Ref::new(Parser::new(&source).unwrap().parse_expr().unwrap());
        Compiler::with_policy(&policy)
            .compile_rego_expr(&expr)
            .unwrap();
    }

    // Width is not depth: every independent item has arithmetic depth one.
    let wide = format!("[{}]", vec!["1+1"; 16_000].join(",\n"));
    engine
        .add_policy("wide.rego".into(), format!("package wide\nr := {wide}"))
        .unwrap();
    assert_eq!(
        engine.eval_rule("data.wide.r".into()).unwrap(),
        Value::from(vec![Value::from(2); 16_000])
    );
}

#[test]
#[cfg_attr(miri, ignore = "requires native-stack subprocess isolation")]
fn arithmetic_depth_small_stack_lifecycle() {
    if std::env::var_os("REGORUS_NATIVE_DEPTH_CHILD").is_none() {
        native_depth_support::run_in_subprocess("arithmetic_depth_small_stack_lifecycle");
        return;
    }
    std::thread::Builder::new()
        .stack_size(1_048_576)
        .spawn(check_policy_lifecycle)
        .unwrap()
        .join()
        .unwrap();
}
