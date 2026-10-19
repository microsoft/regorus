// Regression gate for exact, coherent numeric equality and ordering. Integer division with a
// remainder can produce a `Number::Float`, for example:
//
//   (2 * 9223372036854775808 + 1) / 2
//     -> Number::Float with exact value 2^63
//
// Lossy mixed comparison can make that float equal to both 2^63 and 2^63 + 1. The resulting
// non-transitive equality merges distinct set elements and object keys. These tests pin behavior
// at the public interpreter boundary; RVM differential fixtures cover the compiled path.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::print_stdout)]

use regorus::*;

/// Evaluate `setup` conjuncts followed by the expression `expr`; return the value of the last
/// expression, or `Value::Undefined` when the query has no solution.
///
/// Rego/query details that require this shape:
///   * `Result::expressions` is ordered by conjunct, so `expressions[0]` of `a; b` is the value of
///     `a` - reading index 0 silently returns `Bool(true)` from the setup conjunct and hides failures.
///   * A bare comparison query yields its boolean value (`1 == 2` -> `Bool(false)`), but
///     `ans := (1 == 2)` has NO solution, so wrapping a boolean in an assignment is wrong here.
///   * Therefore boolean checks with setup conjuncts use unification (`min(P) = -3`): success gives
///     `Bool(true)`, failure gives no solution (`Undefined`), and value checks (`count(x)`) stay
///     value queries so the assertion message shows the number actually produced.
fn q(setup: &[&str], expr: &str) -> Value {
    let mut query = setup.join("; ");
    if !query.is_empty() {
        query.push_str("; ");
    }
    query.push_str(expr);

    let mut e = Engine::new();
    match e.eval_query(query, false) {
        Ok(r) => match r.result.first() {
            Some(sol) => sol.expressions.last().expect("no expression").value.clone(),
            None => Value::Undefined,
        },
        Err(err) => panic!("query failed: {setup:?} ; {expr}\n{err}"),
    }
}

/// `a` is a Number::Float whose exact value is 2^63; `b` = 2^63; `c` = 2^63 + 1.
const A: &str = "((2 * 9223372036854775808 + 1) / 2)";

#[test]
fn float_valued_quotient_does_not_equal_distinct_exact_integers() {
    // The float is exactly 2^63, so it equals the exact integer.
    assert_eq!(
        q(&[], &format!("{A} == 9223372036854775808")),
        Value::Bool(true)
    );
    assert_eq!(
        q(&[], "9223372036854775808 == 9223372036854775809"),
        Value::Bool(false)
    );

    assert_eq!(
        q(&[], &format!("{A} == 9223372036854775809")),
        Value::Bool(false),
        "a Float holding exactly 2^63 must not be equal to 2^63+1"
    );

    assert_eq!(
        q(&[], &format!("{A} < 9223372036854775809")),
        Value::Bool(true),
        "2^63 < 2^63+1 must not be flattened away by an f64 round-trip"
    );
    assert_eq!(
        q(&[], &format!("{A} > 9223372036854775807")),
        Value::Bool(true)
    );
}

#[test]
fn sets_do_not_merge_values_that_are_not_equal() {
    assert_eq!(
        q(
            &[],
            &format!("count({{{A}, 9223372036854775808, 9223372036854775809}})")
        ),
        Value::from(2i64),
        "a set must keep 2^63 and 2^63+1 apart even when a Float is involved"
    );
}

#[test]
fn object_keys_that_are_not_equal_are_not_merged() {
    let obj = format!("x := {{{A}: 1, 9223372036854775809: 2}}");
    assert_eq!(
        q(&[&obj], "count(x)"),
        Value::from(2i64),
        "object key collision destroyed a value"
    );
    assert_eq!(
        q(&[&obj], "x[9223372036854775809]"),
        Value::from(2i64),
        "lookup by the surviving key broke"
    );
    assert_eq!(
        q(&[&obj], "x[9223372036854775808]"),
        Value::from(1i64),
        "the Float key must still resolve to its own value"
    );
}

#[test]
fn equality_and_ordering_are_transitive_over_a_mixed_pool() {
    // The pool mixes ints above 2^53, an f64-valued quotient, signed zero, tiny and huge values.
    let pool = "P := [1, -3, 0, -0.0, 0.5, 2.5, 9007199254740993, 9007199254740992.0, \
                ((2 * 9223372036854775808 + 1) / 2), 9223372036854775808, 9223372036854775809, \
                1e308, 1e-300]";

    // equality transitivity: (x == y && y == z) => x == z
    assert_eq!(
        q(
            &[pool],
            "count([[x, y, z] | x := P[_]; y := P[_]; z := P[_]; x == y; y == z; x != z])"
        ),
        Value::from(0i64),
        "== is not transitive over the pool"
    );

    // antisymmetry of the order: (x <= y && y <= x) => x == y
    assert_eq!(
        q(
            &[pool],
            "count([[x, y] | x := P[_]; y := P[_]; x <= y; y <= x; x != y])"
        ),
        Value::from(0i64),
        "<= is not antisymmetric: cmp reports Equal while == reports not-equal"
    );

    // transitivity of the order
    assert_eq!(
        q(
            &[pool],
            "count([[x, y, z] | x := P[_]; y := P[_]; z := P[_]; x <= y; y <= z; not (x <= z)])"
        ),
        Value::from(0i64),
        "<= is not transitive"
    );

    // totality: exactly one of <, ==, > holds for every pair
    assert_eq!(
        q(
            &[pool],
            "count([[x, y] | x := P[_]; y := P[_]; not (x < y); not (x == y); not (x > y)])"
        ),
        Value::from(0i64),
        "some pair is unordered: cmp is not a total order"
    );

    // `-0.0` merges with integer zero, and `A` merges with the exact integer 2^63.
    assert_eq!(
        q(&[pool], "count({v | v := P[_]})"),
        Value::from(11i64),
        "distinct numbers in the pool were merged into one set element"
    );
}

#[test]
fn sort_output_is_consistent_with_the_engine_order() {
    let pool = "P := [1e308, -3, 0.5, 1, -0.0, 9007199254740993, 9007199254740992.0, \
                ((2 * 9223372036854775808 + 1) / 2), 9223372036854775809, -2.5, 1e-300, 2.5]";

    // no inversions under the engine's own comparator
    assert_eq!(
        q(
            &[pool, "x := sort(P)"],
            "count([[i, j] | i := numbers.range(0, count(x) - 1)[_]; \
             j := numbers.range(0, count(x) - 1)[_]; i < j; x[i] > x[j]])"
        ),
        Value::from(0i64),
        "sort produced an order its own comparator rejects"
    );

    assert_eq!(q(&[pool], "min(P) = -3"), Value::Bool(true));
    assert_eq!(q(&[pool], "max(P) = 1e308"), Value::Bool(true));
}

#[test]
fn signed_zero_stays_equal_to_zero() {
    // Finite numeric comparison keeps signed zero equal to zero.
    assert_eq!(q(&[], "-0.0 == 0"), Value::Bool(true));
    assert_eq!(q(&[], "count({-0.0, 0})"), Value::from(1i64));
    assert_eq!(q(&[], "-0.0 < 0.0"), Value::Bool(false));
    assert_eq!(
        q(&[], "json.marshal(-0.0)"),
        Value::String("-0.0".into()),
        "signed zero must stay distinguishable in output"
    );
}
