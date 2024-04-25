// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{anyhow, bail, Result};
use regorus::{unstable::*, *};
use serde::{Deserialize, Serialize};
use test_generator::test_resources;

macro_rules! my_assert_eq {
    ($left:expr, $right:expr, $($arg:tt)+) => {
	match (&($left), &($right)) {
            (left_val, right_val) => {
                if !(*left_val == *right_val) {
		    return Err(anyhow!("mismatch:\nleft  = {}\nright = {}\n{}",
		     		       &$left, &$right, format_args!($($arg)+)));
                }
            }
	}
    }
}

fn skip_value(v: &Value) -> bool {
    matches!(v, Value::String(s) if s.as_ref() == "--skip--")
}

fn match_span(s: &Span, v: &Value) -> Result<()> {
    match &v {
        Value::String(vs) => {
            my_assert_eq!(
                s.text(),
                vs.as_ref(),
                "{}",
                s.source
                    .message(s.line, s.col, "match-error", "mismatch happened here.")
            );
        }
        _ => {
            my_assert_eq!(
                *s.text(),
                serde_json::to_string_pretty(v)?,
                "{}",
                s.source
                    .message(s.line, s.col, "match-error", "mismatch happened here.")
            )
        }
    }

    Ok(())
}

fn match_span_opt(s: &Span, v: &Value) -> Result<()> {
    if *v != Value::Undefined {
        match_span(s, v)
    } else {
        Ok(())
    }
}

fn match_vec(s: &Span, vec: &Vec<Ref<Expr>>, v: &Value) -> Result<()> {
    if v.as_object().is_ok() {
        match_span_opt(s, &v["span"])?;
        return match_vec(s, vec, &v["values"]);
    }
    let v = v.as_array()?;
    my_assert_eq!(
        vec.len(),
        v.len(),
        "{}",
        s.source.message(
            s.line,
            s.col,
            "match-error",
            "mismatch in number of elements in sequence following this location"
        )
    );
    for i in 0..vec.len() {
        match_expr(&vec[i], &v[i])?;
    }
    Ok(())
}

fn match_object(s: &Span, fields: &[(Span, Ref<Expr>, Ref<Expr>)], v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match_span_opt(s, &v["span"])?;
    match &v["fields"].as_array() {
        Ok(a) => {
            my_assert_eq!(fields.len(), a.len(), "field length mismatch");
            for (idx, (_, k, v)) in fields.iter().enumerate() {
                match_expr(k, &a[idx]["key"])?;
                match_expr(v, &a[idx]["value"])?;
            }
            Ok(())
        }
        _ => bail!("incorrect field specification in yaml. Must be array."),
    }
}

fn match_expr_impl(e: &Expr, v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match e {
        Expr::String(s) => match_span(&s.0, &v["string"]),
        Expr::RawString(s) => match_span(&s.0, &v["rawstring"]),
        Expr::Number(s) => match_span(&s.0, &v["number"]),
        Expr::True(s) => match_span(s, v),
        Expr::False(s) => match_span(s, v),
        Expr::Null(s) => match_span(s, v),
        Expr::Var(s) => match_span(&s.0, &v["var"]),
        Expr::Array { span, items } => match_vec(span, items, &v["array"]),
        Expr::Set { span, items } => match_vec(span, items, &v["set"]),
        Expr::Object { span, fields } => match_object(span, fields, &v["object"]),
        Expr::ArrayCompr { span, term, query } => {
            match_span_opt(span, &v["arraycompr"]["span"])?;
            match_expr(term, &v["arraycompr"]["term"])?;
            match_query(query, &v["arraycompr"]["query"])
        }
        Expr::SetCompr { span, term, query } => {
            match_span_opt(span, &v["setcompr"]["span"])?;
            match_expr(term, &v["setcompr"]["term"])?;
            match_query(query, &v["setcompr"]["query"])
        }
        Expr::ObjectCompr {
            span,
            key,
            value,
            query,
        } => {
            match_span_opt(span, &v["objectcompr"]["span"])?;
            match_expr(key, &v["objectcompr"]["key"])?;
            match_expr(value, &v["objectcompr"]["value"])?;
            match_query(query, &v["objectcompr"]["query"])
        }
        Expr::Call { span, fcn, params } => {
            match_span_opt(span, &v["call"]["span"])?;
            match_expr(fcn, &v["call"]["fcn"])?;
            match_vec(span /*dummy*/, params, &v["call"]["params"])
        }
        Expr::RefDot { span, refr, field } => {
            match_span_opt(span, &v["refdot"]["span"])?;
            match_expr(refr, &v["refdot"]["refr"])?;
            match_span(&field.0, &v["refdot"]["field"])
        }
        Expr::RefBrack { span, refr, index } => {
            match_span_opt(span, &v["refbrack"]["span"])?;
            match_expr(refr, &v["refbrack"]["refr"])?;
            match_expr(index, &v["refbrack"]["index"])
        }
        Expr::UnaryExpr { span, expr } => {
            match_span_opt(span, &v["span"])?;
            my_assert_eq!(
                &Value::String("-".into()),
                &v["op"],
                "{}",
                span.source.message(
                    span.line,
                    span.col,
                    "mismatch-error",
                    "could not match `-` operator",
                ),
            );
            match_expr(expr, &v["expr"])
        }
        Expr::BinExpr { span, op, lhs, rhs } => {
            match_span_opt(span, &v["binexpr"]["span"])?;
            match_bin_op(span, op, &v["binexpr"]["op"])?;
            match_expr(lhs, &v["binexpr"]["lhs"])?;
            match_expr(rhs, &v["binexpr"]["rhs"])
        }
        Expr::ArithExpr { span, op, lhs, rhs } => {
            match_span_opt(span, &v["arithexpr"]["span"])?;
            match_arith_op(span, op, &v["arithexpr"]["op"])?;
            match_expr(lhs, &v["arithexpr"]["lhs"])?;
            match_expr(rhs, &v["arithexpr"]["rhs"])
        }
        Expr::BoolExpr { span, op, lhs, rhs } => {
            match_span_opt(span, &v["boolexpr"]["span"])?;
            match_bool_op(span, op, &v["boolexpr"]["op"])?;
            match_expr(lhs, &v["boolexpr"]["lhs"])?;
            match_expr(rhs, &v["boolexpr"]["rhs"])
        }
        Expr::AssignExpr { span, op, lhs, rhs } => {
            match_span_opt(span, &v["assignexpr"]["span"])?;
            match_assign_op(span, op, &v["assignexpr"]["op"])?;
            match_expr(lhs, &v["assignexpr"]["lhs"])?;
            match_expr(rhs, &v["assignexpr"]["rhs"])
        }
        Expr::Membership {
            span,
            key,
            value,
            collection,
        } => {
            match_span_opt(span, &v["inexpr"]["span"])?;
            match_expr_opt(span, key, &v["inexpr"]["key"])?;
            match_expr(value, &v["inexpr"]["value"])?;
            match_expr(collection, &v["inexpr"]["collection"])
        }
    }
}

fn match_expr(expr: &Expr, v: &Value) -> Result<()> {
    match match_expr_impl(expr, v) {
        Ok(()) => Ok(()),
        Err(e) => bail!(
            "{e}\nexpr = {expr:#?}\nv={}\n-----------------------\n",
            serde_json::to_string_pretty(v)?
        ),
    }
}

fn match_with_mod(m: &WithModifier, v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match_span_opt(&m.span, &v["span"])?;
    match_expr(&m.refr, &v["refr"])?;
    match_expr(&m.r#as, &v["as"])
}

fn match_literal_stmt(ls: &LiteralStmt, v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match_span_opt(&ls.span, &v["span"])?;
    match_literal(&ls.literal, &v["literal"])?;

    let with_mods = &v["with-mods"];
    if skip_value(with_mods) {
        return Ok(());
    }

    match with_mods.as_array() {
        Ok(a) => {
            my_assert_eq!(
                ls.with_mods.len(),
                a.len(),
                "{}",
                ls.span.source.message(
                    ls.span.line,
                    ls.span.col,
                    "mismatch-error",
                    "with-modifier count mismatch"
                )
            );
            for (idx, with_mod) in a.iter().enumerate() {
                match_with_mod(&ls.with_mods[idx], with_mod)?;
            }
        }
        _ if ls.with_mods.is_empty() => (),
        _ => {
            bail!(
                "{}",
                ls.span.source.message(
                    ls.span.line,
                    ls.span.col,
                    "mismatch-error",
                    "failed to match with-modifiers"
                )
            )
        }
    }
    Ok(())
}

fn match_query(q: &Query, v: &Value) -> Result<()> {
    match_span_opt(&q.span, &v["span"])?;
    let stmts = &v["stmts"].as_array();
    let stmts = match &stmts {
        Ok(s) => s,
        _ => {
            bail!(
                "{}",
                q.span.source.message(
                    q.span.line,
                    q.span.col,
                    "mismatch-error",
                    "empty statements list in query specified"
                )
            )
        }
    };
    my_assert_eq!(
        q.stmts.len(),
        stmts.len(),
        "{}",
        q.span.source.message(
            q.span.line,
            q.span.col,
            "mismatch-error",
            "mismatch in statement count"
        )
    );
    for (idx, stmt) in stmts.iter().enumerate() {
        match_literal_stmt(&q.stmts[idx], stmt)?;
    }
    Ok(())
}

fn match_expr_opt(s: &Span, e: &Option<Ref<Expr>>, v: &Value) -> Result<()> {
    match (e, v) {
        (Some(e), v) => match_expr(e, v),
        (None, Value::Undefined) => Ok(()),
        _ => {
            bail!(
                "{}",
                s.source.message(
                    s.line,
                    s.col,
                    "mismatch-error",
                    format!(
                        "failed to match {:#?} and {}",
                        e,
                        serde_json::to_string_pretty(&v)?
                    )
                    .as_str()
                )
            )
        }
    }
}

fn match_bin_op(s: &Span, op: &BinOp, v: &Value) -> Result<()> {
    match (op, v) {
        (BinOp::And, Value::String(s)) if s.as_ref() == "&" => Ok(()),
        (BinOp::Or, Value::String(s)) if s.as_ref() == "|" => Ok(()),
        _ => bail!(
            "{}",
            s.source.message(
                s.line,
                s.col,
                "mismatch-error",
                format!("left = {op:?}\nright = {v:?}\n").as_str()
            )
        ),
    }
}

fn match_arith_op(s: &Span, op: &ArithOp, v: &Value) -> Result<()> {
    match (op, v) {
        (ArithOp::Add, Value::String(s)) if s.as_ref() == "+" => Ok(()),
        (ArithOp::Sub, Value::String(s)) if s.as_ref() == "-" => Ok(()),
        (ArithOp::Mul, Value::String(s)) if s.as_ref() == "*" => Ok(()),
        (ArithOp::Div, Value::String(s)) if s.as_ref() == "/" => Ok(()),
        _ => bail!(
            "{}",
            s.source.message(
                s.line,
                s.col,
                "mismatch-error",
                format!("left = {op:?}\nright = {v:?}\n").as_str()
            )
        ),
    }
}

fn match_bool_op(s: &Span, op: &BoolOp, v: &Value) -> Result<()> {
    match (op, v) {
        (BoolOp::Lt, Value::String(s)) if s.as_ref() == "<" => Ok(()),
        (BoolOp::Le, Value::String(s)) if s.as_ref() == "<=" => Ok(()),
        (BoolOp::Eq, Value::String(s)) if s.as_ref() == "==" => Ok(()),
        (BoolOp::Ge, Value::String(s)) if s.as_ref() == ">=" => Ok(()),
        (BoolOp::Gt, Value::String(s)) if s.as_ref() == ">" => Ok(()),
        _ => bail!(
            "{}",
            s.source.message(
                s.line,
                s.col,
                "mismatch-error",
                format!("left = {op:?}\nright = {v:?}\n").as_str()
            )
        ),
    }
}

fn match_assign_op(s: &Span, op: &AssignOp, v: &Value) -> Result<()> {
    match (op, v) {
        (AssignOp::Eq, Value::String(s)) if s.as_ref() == "=" => Ok(()),
        (AssignOp::ColEq, Value::String(s)) if s.as_ref() == ":=" => Ok(()),
        _ => bail!(
            "{}",
            s.source.message(
                s.line,
                s.col,
                "mismatch-error",
                format!("left = {op:?}\nright = {v:?}\n").as_str()
            )
        ),
    }
}

fn match_rule_assign(a: &RuleAssign, v: &Value) -> Result<()> {
    match_span_opt(&a.span, &v["span"])?;
    match_assign_op(&a.span, &a.op, &v["op"])?;
    match_expr(&a.value, &v["value"])
}

fn match_rule_assign_opt(a: &Option<RuleAssign>, v: &Value) -> Result<()> {
    match a {
        Some(a) => match_rule_assign(a, v),
        None => {
            my_assert_eq!(*v, Value::Undefined, "mismatch in null assign");
            Ok(())
        }
    }
}

fn match_rule_head(h: &RuleHead, v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match h {
        RuleHead::Compr { span, refr, assign } => {
            match_span_opt(span, &v["compr"]["span"])?;
            match_expr(refr, &v["compr"]["refr"])?;
            match_rule_assign_opt(assign, &v["compr"]["assign"])
        }
        RuleHead::Set { span, refr, key } => {
            match_span_opt(span, &v["set"]["span"])?;
            match_expr(refr, &v["set"]["refr"])?;
            match_expr_opt(span, key, &v["set"]["key"])
        }
        RuleHead::Func {
            span,
            refr,
            args,
            assign,
        } => {
            match_span_opt(span, &v["func"]["span"])?;
            match_expr(refr, &v["func"]["refr"])?;
            match_vec(span /*dummy*/, args, &v["func"]["args"])?;
            match_rule_assign_opt(assign, &v["func"]["assign"])
        }
    }
}

fn match_literal(l: &Literal, v: &Value) -> Result<()> {
    match l {
        Literal::SomeVars { span, vars } => {
            let v = &v["some-vars"];
            match_span_opt(span, &v["span"])?;
            let values = &v["vars"].as_array()?;
            my_assert_eq!(
                vars.len(),
                values.len(),
                "some-vars mismatch {:#?} {}",
                vars,
                serde_json::to_string_pretty(&values)?
            );
            for idx in 0..vars.len() {
                match_span(&vars[idx], &values[idx])?
            }
            Ok(())
        }
        Literal::SomeIn {
            span,
            key,
            value,
            collection,
        } => {
            let v = &v["some-decl"];
            match_span_opt(span, &v["span"])?;
            match_expr(value, &v["value"])?;
            match_expr_opt(span, key, &v["key"])?;
            match_expr(collection, &v["collection"])
        }
        Literal::Expr { expr, .. } => match_expr(expr, &v["expr"]),
        Literal::NotExpr { expr, span } => {
            let v = &v["notexpr"];
            match &v["op"] {
                Value::String(s) if s.as_ref() == "not" => (),
                _ => {
                    bail!(
                        "{}",
                        span.source.message(
                            span.line,
                            span.col,
                            "mismatch-error",
                            "`op: -` not found in value`"
                        )
                    )
                }
            }
            match_expr(expr, v)
        }
        Literal::Every {
            span,
            key,
            value,
            domain,
            query,
        } => {
            match_span_opt(span, &v["every"]["span"])?;
            match_span(value, &v["every"]["value"])?;
            match key {
                Some(s) => match_span(s, &v["every"]["key"])?,
                None => {
                    my_assert_eq!(
                        &Value::Undefined,
                        &v["key"],
                        "{}",
                        span.source.message(
                            span.line,
                            span.col,
                            "mismatch-error",
                            "could not match `key``"
                        )
                    );
                }
            }
            match_expr(domain, &v["every"]["domain"])?;
            match_query(query, &v["every"]["query"])
        }
    }
}

fn match_rule_body(b: &RuleBody, v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match_span_opt(&b.span, &v["span"])?;
    match_rule_assign_opt(&b.assign, &v["assign"])?;
    match_query(&b.query, &v["query"])
}

fn match_rule_bodies(span: &Span, bodies: &[RuleBody], v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    let v = &v.as_array();
    let v = match &v {
        Ok(v) => v,
        _ => {
            bail!(
                "incorrect yaml. bodies is not an array. Corresponding rego: {}",
                span.source.message(span.line, span.col, "invalid-yaml", "")
            );
        }
    };
    my_assert_eq!(
        bodies.len(),
        v.len(),
        "{}",
        span.source.message(
            span.line,
            span.col,
            "mismatch-error",
            "mismatch in body count",
        ),
    );

    for idx in 0..bodies.len() {
        match_rule_body(&bodies[idx], &v[idx])?;
    }

    Ok(())
}

fn match_rule(r: &Rule, v: &Value) -> Result<()> {
    match r {
        Rule::Spec { span, head, bodies } => {
            let obj = &v["spec"];
            match_span_opt(span, &obj["span"])?;
            match_rule_head(head, &obj["head"])?;
            match_rule_bodies(span, bodies, &obj["bodies"])
        }
        Rule::Default {
            span,
            refr,
            args,
            op,
            value,
        } => {
            let obj = &v["default"];
            match_span_opt(span, &obj["span"])?;
            match_expr(refr, &obj["refr"])?;
            match_vec(span /*dummy*/, args, &obj["args"])?;
            match_assign_op(span, op, &obj["op"])?;
            match_expr(value, &obj["value"])
        }
    }
}

fn match_package(p: &Package, v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match_span_opt(&p.span, &v["span"])?;
    match_expr(&p.refr, &v["refr"])
}

fn match_import(i: &Import, v: &Value) -> Result<()> {
    if skip_value(v) {
        return Ok(());
    }
    match_span_opt(&i.span, &v["span"])?;
    match_expr(&i.refr, &v["refr"])?;
    match (&i.r#as, &v["as"]) {
        (Some(a), v) => match_span(a, v),
        (None, Value::Undefined) => Ok(()),
        _ => Err(i
            .span
            .source
            .error(i.span.line, i.span.col, "import does not have `as` binding")),
    }
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct TestCase {
    rego: String,
    note: String,
    package: Option<Value>,
    imports: Option<Vec<Value>>,
    policy: Option<Vec<Value>>,
    error: Option<String>,
}

#[derive(Serialize, Deserialize, PartialEq, Debug)]
struct YamlTest {
    cases: Vec<TestCase>,
}

fn yaml_test_impl(file: &str) -> Result<()> {
    println!("\nrunning {file}");

    let yaml_str = std::fs::read_to_string(file)?;
    let test: YamlTest = serde_yaml::from_str(&yaml_str)?;

    for case in &test.cases {
        print!("\ncase {} ", case.note);
        let source = Source::from_contents("case.rego".to_string(), case.rego.clone())?;
        let mut parser = Parser::new(&source)?;
        match parser.parse() {
            Ok(module) => {
                if let Some(e) = &case.error {
                    bail!("error `{}` not raised by parser.", e);
                }
                if let Some(p) = &case.package {
                    match_package(&module.package, p)?;
                }

                if let Some(imports) = &case.imports {
                    my_assert_eq!(
                        module.imports.len(),
                        imports.len(),
                        "mismatch in number of imports"
                    );

                    for (idx, import) in imports.iter().enumerate().take(module.imports.len()) {
                        match_import(&module.imports[idx], import)?;
                    }
                }

                if let Some(policy) = &case.policy {
                    my_assert_eq!(
                        module.policy.len(),
                        policy.len(),
                        "mismatch in policy length"
                    );
                    for (idx, policy) in policy.iter().enumerate().take(module.policy.len()) {
                        if skip_value(policy) {
                            continue;
                        }
                        match_rule(&module.policy[idx], policy)?;
                    }
                }
            }
            Err(actual) => match &case.error {
                Some(expected) => {
                    let actual = actual.to_string();
                    if !actual.contains(expected) {
                        bail!(
                            "Error message\n`{}\n`\ndoes not contain `{}`",
                            actual,
                            expected
                        );
                    }
                    println!("{actual}");
                }
                _ => return Err(actual),
            },
        }

        println!("passed");
    }

    println!("{} cases passed.", test.cases.len());
    Ok(())
}

fn yaml_test(file: &str) -> Result<()> {
    match yaml_test_impl(file) {
        Ok(_) => Ok(()),
        Err(e) => {
            // If Err is returned, it doesn't always get printed by cargo test.
            // Therefore, panic with the error.
            panic!("{}", e);
        }
    }
}

#[test_resources("tests/parser/**/*.yaml")]
fn run(path: &str) {
    yaml_test(path).unwrap()
}
