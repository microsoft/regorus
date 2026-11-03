// Arithmetic must not fabricate Inf or NaN from finite operands.
//
// Regorus deliberately fails closed when its f64 arithmetic cannot represent a finite result.
// This is a breaking compatibility difference from OPA, which evaluates integer-valued operands
// with big.Int and fractional arithmetic with a bounded-precision, wide-exponent big.Float.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::print_stdout)]

use regorus::*;

struct OverflowCase {
    expr: &'static str,
    operation: &'static str,
    opa_result: &'static str,
}

const OVERFLOW_CASES: &[OverflowCase] = &[
    OverflowCase {
        expr: "(1e300*1e300)/7",
        operation: "division",
        opa_result: "a finite, rounded quotient near 1.4285714285714285714e599",
    },
    OverflowCase {
        expr: "1e308*1e308*1.0",
        operation: "multiplication",
        opa_result: "the exact integer 1e616 because 1.0 is integer-valued",
    },
    OverflowCase {
        expr: "(1e300*1e300)+0.5",
        operation: "addition",
        opa_result: "1e600, with 0.5 rounded away",
    },
    OverflowCase {
        expr: "(1e300*1e300)-0.5",
        operation: "subtraction",
        opa_result: "1e600, with 0.5 rounded away",
    },
    OverflowCase {
        expr: "(1e300*1e300)*0.0",
        operation: "multiplication",
        opa_result: "the exact integer 0 because 0.0 is integer-valued",
    },
    OverflowCase {
        expr: "(-1e300*1e300)*1.0",
        operation: "multiplication",
        opa_result: "the exact integer -1e600 because 1.0 is integer-valued",
    },
    OverflowCase {
        expr: "1.5/1e-320",
        operation: "division",
        opa_result: "a finite, rounded value near 1.5e320",
    },
];

fn eval(e: &mut Engine, expr: &str) -> anyhow::Result<Value> {
    let r = e.eval_query(expr.to_string(), false)?;
    let s = r
        .result
        .first()
        .ok_or_else(|| anyhow::anyhow!("query produced no solution: {expr}"))?;
    Ok(s.expressions[0].value.clone())
}

/// OPA v1.21.2 returns the finite value documented in each case. Regorus instead
/// raises an operation-specific error in both strict and non-strict modes. This
/// is intentionally fail-closed and is a breaking change from OPA and prior
/// Regorus behavior.
#[test]
fn arithmetic_rejects_results_outside_binary64_range() {
    let mut e = Engine::new();

    for strict in [true, false] {
        e.set_strict_builtin_errors(strict);
        for case in OVERFLOW_CASES {
            let result =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| eval(&mut e, case.expr)));
            assert!(result.is_ok(), "{} aborted the process", case.expr);
            let err = result
                .unwrap()
                .expect_err("an out-of-range result was accepted")
                .to_string();
            assert!(
                err.contains(&format!("numeric overflow in {}", case.operation)),
                "{} returned {err:?} with strict={strict}; OPA v1.21.2 returns {}",
                case.expr,
                case.opa_result
            );
        }
    }
}

/// OPA's wide exponent retains approximately 1e-640 here. Binary64 underflows
/// to zero, which remains finite and is therefore outside this PR's rejection rule.
#[test]
fn finite_binary64_underflow_remains_zero() {
    let mut e = Engine::new();
    for strict in [true, false] {
        e.set_strict_builtin_errors(strict);
        assert_eq!(
            format!(
                "{:?}",
                eval(&mut e, "1e-320*1e-320").expect("underflow errored")
            ),
            "Number(0)"
        );
    }
}

/// Values that are already correct must not change: this pins that the overflow error is not a
/// blanket refusal of big-number arithmetic.
#[test]
fn exact_and_float_results_are_preserved() {
    let mut e = Engine::new();
    let big = eval(&mut e, "1e300*1e300").expect("errored");
    let dbg = format!("{big:?}");
    assert!(
        dbg.starts_with("Number(1000000000000000000000000"),
        "big product lost exactness: {dbg}"
    );
    assert!(
        dbg.len() > 600,
        "big product is no longer exact ({})",
        dbg.len()
    );

    for (expr, want) in [("7/2", "Number(3.5)"), ("1.5+2.5", "Number(4)")] {
        let v = eval(&mut e, expr)
            .unwrap_or_else(|err| panic!("{expr} errored: {}", err.to_string().replace('\n', " ")));
        assert_eq!(format!("{v:?}"), want, "{expr} changed");
    }

    // f64 semantics for ordinary float addition must be left alone.
    let v = eval(&mut e, "0.1+0.2").expect("errored");
    assert_eq!(
        v.as_number().ok().and_then(|n| n.as_f64()),
        Some(0.1f64 + 0.2f64),
        "float addition changed"
    );
}
