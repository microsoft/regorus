// Numeric ingress never admits a non-finite number.
//
// `units.parse`, `units.parse_bytes`, serde's private big-number envelope, the Rego lexer and
// numeric-string parsing all inherit the shared finite-result check.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::print_stdout)]

use regorus::*;

#[derive(Debug)]
enum Outcome {
    Panic,
    EvalErr,
    NoSolution,
    Val(String),
}

fn catch_eval(e: &mut Engine, expr: &str) -> Outcome {
    let run = || -> anyhow::Result<Option<Value>> {
        let r = e.eval_query(expr.to_string(), false)?;
        Ok(r.result.first().map(|s| s.expressions[0].value.clone()))
    };
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(run)) {
        Err(_) => Outcome::Panic,
        Ok(Err(_)) => Outcome::EvalErr,
        Ok(Ok(None)) => Outcome::NoSolution,
        Ok(Ok(Some(v))) => Outcome::Val(format!("{v:?}")),
    }
}

fn non_finite(dbg: &str) -> bool {
    dbg.contains("Number(inf)") || dbg.contains("Number(-inf)") || dbg.contains("Number(NaN)")
}

/// units.parse / units.parse_bytes hand the whole string to
/// Number::from_str when there is no digit, admitting Rust's inf/nan spellings.
/// OPA returns undefined for every one of these.
#[test]
fn units_builtins_reject_non_finite_spellings() {
    for call in [
        "units.parse(\"NaN\")",
        "units.parse(\"inf\")",
        "units.parse(\"-inf\")",
        "units.parse(\"infinity\")",
        "units.parse_bytes(\"NaN\")",
        "units.parse_bytes(\"+INF\")",
    ] {
        for strict in [true, false] {
            let mut e = Engine::new();
            e.set_strict_builtin_errors(strict);
            let res = catch_eval(&mut e, call);
            assert!(!matches!(res, Outcome::Panic), "{call} aborted the process");
            if strict {
                assert!(
                    matches!(res, Outcome::EvalErr),
                    "{call} must be an eval error in strict mode, got {res:?}"
                );
            } else {
                assert!(
                    matches!(res, Outcome::NoSolution | Outcome::EvalErr),
                    "{call} should be undefined (or an error), got {res:?}"
                );
            }
            if let Outcome::Val(dbg) = &res {
                assert!(
                    !non_finite(dbg),
                    "{call} produced a non-finite number: {dbg}"
                );
            }
        }
    }
}

/// Normalization must not allow obfuscated non-finite spellings past the finite-result check.
#[test]
fn non_finite_numeric_text_is_rejected_by_the_shared_parser() {
    for text in [
        "NaN", "nan", "Nan", "inf", "-inf", "+INF", "Infinity", "i_nf", "+i_nf", "  NaN ",
        "\tinf\n",
    ] {
        let res = Value::from_numeric_string(text);
        assert!(
            res.is_err(),
            "from_numeric_string({text:?}) was accepted: {:?}",
            res.map(|v| format!("{v:?}"))
        );
    }
}

/// serde's private big-number envelope is accepted verbatim, so a JSON
/// *object* smuggles non-finite values in.
#[test]
fn private_number_envelope_cannot_smuggle_non_finite() {
    for text in ["inf", "NaN", "-inf"] {
        let json = format!(r#"{{"$serde_json::private::Number": "{text}"}}"#);
        let res = Value::from_json_str(&json);
        let accepted_number = match &res {
            Ok(v) => non_finite(&format!("{v:?}")),
            Err(_) => false,
        };
        assert!(
            !accepted_number,
            "envelope smuggled a non-finite number: {:?}",
            res.map(|v| format!("{v:?}"))
        );
    }
}

/// Teeth: legitimate numeric text and unit conversions must keep working,
/// including decimal-exact big integers.
#[test]
fn valid_numeric_text_still_parses() {
    for (text, want) in [
        ("-3.5", "Number(-3.5)"),
        ("1e3", "Number(1000)"),
        ("0.5", "Number(0.5)"),
        ("-.5", "Number(-0.5)"),
        (" 1_0 ", "Number(10)"),
        ("1_e5", "Number(100000)"),
    ] {
        let v = Value::from_numeric_string(text)
            .unwrap_or_else(|err| panic!("{text:?} rejected: {err}"));
        assert_eq!(format!("{v:?}"), want, "{text:?} parsed unexpectedly");
    }
    let big = Value::from_numeric_string("18446744073709551616").expect("2^64 rejected");
    assert_eq!(
        format!("{big:?}"),
        "Number(18446744073709551616)",
        "2^64 lost exactness"
    );

    let mut e = Engine::new();
    for (call, want) in [
        ("units.parse(\"1.5Ki\")", "Number(1536)"),
        ("units.parse_bytes(\"0.5Ki\")", "Number(512)"),
    ] {
        let res = catch_eval(&mut e, call);
        match &res {
            Outcome::Val(dbg) => assert_eq!(dbg, want, "{call} regressed"),
            other => panic!("{call} failed: {other:?}"),
        }
    }
}
