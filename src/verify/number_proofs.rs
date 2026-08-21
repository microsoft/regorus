// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use vstd::prelude::*;

verus! {

use core::cmp::Ordering;
use crate::number::Number;
use num_bigint::BigInt;
use super::bigint_assumptions::*;
use super::number_specs::NumberView;
use vstd::arithmetic::div_mod::{
    lemma_div_of0,
    lemma_fundamental_div_mod,
    rust_div,
    rust_rem,
};
use vstd::arithmetic::mul::{
    lemma_mul_cancels_negatives,
    lemma_mul_increases,
    lemma_mul_strictly_increases,
    lemma_mul_unary_negation,
};
use vstd::float::*;
use vstd::std_specs::cmp::*;
use vstd::std_specs::convert::*;
use vstd::std_specs::ops::*;

/// Spec trait implementations

// For various `T`, we implement `From<T>` for `Number`. This means
// that Verus demands a proof that it implements `FromSpecImpl<T>`.
// The easiest (and most obviously correct) way to do this is to just
// define `obeys_from_spec()` as always returning `false`. We also
// need to define a `from_spec`, but it's meaningless since
// `obeys_from_spec()` always returns false. So we may as well leave
// it uninterpreted.

impl FromSpecImpl<BigInt> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: BigInt) -> Number;
}

impl FromSpecImpl<u64> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: u64) -> Number;
}

impl FromSpecImpl<usize> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: usize) -> Number;
}

impl FromSpecImpl<u128> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: u128) -> Number;
}

impl FromSpecImpl<i64> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: i64) -> Number;
}

impl FromSpecImpl<i128> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: i128) -> Number;
}

impl FromSpecImpl<f64> for Number {
    open spec fn obeys_from_spec() -> bool
    {
        false
    }

    uninterp spec fn from_spec(v: f64) -> Number;
}

// We implement `PartialEq` for `Number`. This means that Verus
// demands a proof that it implements `PartialEqSpecImpl`. The
// simplest, and most obviously correct, way to do this is to just say
// that `obeys_eq_spec()` always returns `false`. This makes all the
// postconditions trivial. We also need to define an `eq_spec`, but
// it's meaningless since `obeys_from_spec()` always returns false. So
// we may as well leave it uninterpreted.

impl PartialEqSpecImpl for Number {
    open spec fn obeys_eq_spec() -> bool
    {
        false
    }

    uninterp spec fn eq_spec(&self, other: &Self) -> bool;
}

// We implement `Ord` for `Number`. This means that Verus demands a
// proof that it implements `OrdSpecImpl`. The simplest, and most
// obviously correct, way to do this is to just say that
// `obeys_eq_spec()` always returns `false`. This makes all the
// postconditions trivial. We also need to define a `cmp_spec`, but
// it's meaningless since `obeys_from_spec()` always returns false. So
// we may as well leave it uninterpreted.

impl OrdSpecImpl for Number {
    open spec fn obeys_cmp_spec() -> bool
    {
        false
    }

    uninterp spec fn cmp_spec(&self, other: &Self) -> Ordering;
}

/// View implementation (internal to crate)

impl View for Number
{
    type V = NumberView;

    open(crate) spec fn view(&self) -> NumberView
    {
        match self {
            Number::UInt(n) => NumberView::Integer(n as int),
            Number::Int(n) => NumberView::Integer(n as int),
            Number::Float(f) => NumberView::Float(*f),
            Number::BigInt(b) => NumberView::Integer(b@),
        }
    }
}

/// Helpful lemmas

pub proof fn lemma_div_ensures_cases(lhs: NumberView, rhs: NumberView)
    ensures
        match (lhs, rhs) {
            (NumberView::Integer(integer_lhs), NumberView::Integer(divisor)) => {
                divisor != 0 && rust_rem(integer_lhs, divisor) == 0
                ==> lhs.div_ensures(
                    rhs,
                    NumberView::Integer(rust_div(integer_lhs, divisor)),
                )
            },
            _ => true,
        },
        forall|lhs_float: f64, rhs_float: f64|
            lhs is Integer && rhs is Integer && rhs->Integer_0 != 0 && rust_rem(
                lhs->Integer_0,
                rhs->Integer_0,
            ) != 0 && lhs.to_f64_lossy_ensures(lhs_float) && rhs.to_f64_lossy_ensures(rhs_float)
            ==> #[trigger] lhs.div_ensures(rhs, NumberView::Float(lhs_float / rhs_float)),
        forall|lhs_float: f64, rhs_float: f64|
            (lhs is Float || rhs is Float) && !rhs.is_zero() && lhs.to_f64_lossy_ensures(lhs_float)
                && rhs.to_f64_lossy_ensures(rhs_float)
            ==> #[trigger] lhs.div_ensures(rhs, NumberView::Float(lhs_float / rhs_float)),
{
    reveal(NumberView::is_zero);
    reveal(NumberView::div_ensures);
}

proof fn lemma_rust_div_rem_identity(lhs: int, rhs: int)
    requires
        rhs != 0,
    ensures
        lhs == rhs * rust_div(lhs, rhs) + rust_rem(lhs, rhs),
{
    reveal(rust_div);
    reveal(rust_rem);
    if lhs == 0 {
        lemma_div_of0(rhs);
        lemma_fundamental_div_mod(lhs, rhs);
    } else if lhs > 0 {
        lemma_fundamental_div_mod(lhs, rhs);
    } else {
        let positive_lhs = -lhs;
        let quotient = positive_lhs / rhs;
        let remainder = positive_lhs % rhs;
        lemma_fundamental_div_mod(positive_lhs, rhs);
        lemma_mul_unary_negation(rhs, quotient);
        assert(positive_lhs == rhs * quotient + remainder);
        assert(rhs * (-quotient) == -(rhs * quotient));
        assert(lhs == rhs * (-quotient) + (-remainder));
        assert(rust_div(lhs, rhs) == -quotient);
        assert(rust_rem(lhs, rhs) == -remainder);
    }
}

proof fn lemma_exact_rust_div_fits(
    dividend: int,
    divisor: int,
    minimum: int,
    maximum: int,
)
    requires
        minimum == -maximum - 1,
        minimum <= dividend <= maximum,
        minimum <= divisor <= maximum,
        divisor != 0,
        !(dividend == minimum && divisor == -1),
        rust_rem(dividend, divisor) == 0,
    ensures
        minimum <= rust_div(dividend, divisor) <= maximum,
{
    let quotient = rust_div(dividend, divisor);
    lemma_rust_div_rem_identity(dividend, divisor);
    assert(dividend == divisor * quotient);

    if quotient < minimum {
        assert(quotient <= minimum - 1);
        assert(-quotient > maximum);
        if divisor > 0 {
            lemma_mul_increases(divisor, -quotient);
            lemma_mul_unary_negation(divisor, quotient);
            assert(divisor * quotient <= quotient);
            assert(dividend < minimum);
        } else {
            assert(divisor <= -1);
            lemma_mul_increases(-divisor, -quotient);
            lemma_mul_cancels_negatives(divisor, quotient);
            assert(dividend > maximum);
        }
    } else if quotient > maximum {
        assert(quotient >= maximum + 1);
        assert(quotient >= -minimum);
        if divisor > 0 {
            lemma_mul_increases(divisor, quotient);
            assert(dividend > maximum);
        } else {
            assert(divisor <= -1);
            lemma_mul_increases(-divisor, quotient);
            lemma_mul_unary_negation(divisor, quotient);
            assert(dividend <= minimum);
            assert(dividend == minimum);
            if divisor < -1 {
                lemma_mul_strictly_increases(-divisor, quotient);
                assert(quotient < (-divisor) * quotient);
                assert((-divisor) * quotient == -dividend);
                assert(false);
            }
            assert(divisor == -1);
        }
    }
}

pub proof fn lemma_rust_div_fits_i64(lhs: i64, rhs: i64)
    requires
        rhs != 0,
        !(lhs == i64::MIN && rhs == -1),
        rust_rem(lhs as int, rhs as int) == 0,
    ensures
        i64::MIN as int <= rust_div(lhs as int, rhs as int) <= i64::MAX as int,
{
    lemma_exact_rust_div_fits(
        lhs as int,
        rhs as int,
        i64::MIN as int,
        i64::MAX as int,
    );
}

pub proof fn lemma_checked_div_matches_rust_i64(lhs: i64, rhs: i64, quotient: i64)
    requires
        rhs != 0,
        !(lhs == i64::MIN && rhs == -1),
        rust_rem(lhs as int, rhs as int) == 0,
        i64::checked_div(lhs, rhs) == Some(quotient),
    ensures
        quotient as int == rust_div(lhs as int, rhs as int),
{
    let mathematical_quotient = rust_div(lhs as int, rhs as int);
    lemma_rust_div_fits_i64(lhs, rhs);
    assert(i64::MIN as int <= mathematical_quotient <= i64::MAX as int);
    assert(quotient == mathematical_quotient as i64);
}

pub proof fn lemma_remainder_matches_rust_i64(lhs: i64, rhs: i64)
    requires
        rhs != 0,
        !(lhs == i64::MIN && rhs == -1),
    ensures
        <i64 as RemSpec>::obeys_rem_spec(),
        <i64 as RemSpec>::rem_req(lhs, rhs),
        <i64 as RemSpec>::rem_spec(lhs, rhs) as int == rust_rem(lhs as int, rhs as int),
{
    assert(<i64 as RemSpec>::obeys_rem_spec());
    assert(<i64 as RemSpec>::rem_req(lhs, rhs));
    reveal(rust_rem);
}

pub proof fn lemma_remainder_matches_rust_i128(lhs: i128, rhs: i128)
    requires
        rhs != 0,
        !(lhs == i128::MIN && rhs == -1),
    ensures
        <i128 as RemSpec>::obeys_rem_spec(),
        <i128 as RemSpec>::rem_req(lhs, rhs),
        <i128 as RemSpec>::rem_spec(lhs, rhs) as int == rust_rem(lhs as int, rhs as int),
{
    assert(<i128 as RemSpec>::obeys_rem_spec());
    assert(<i128 as RemSpec>::rem_req(lhs, rhs));
    reveal(rust_rem);
}

pub proof fn lemma_remainder_matches_rust_u64(lhs: u64, rhs: u64)
    requires
        rhs != 0,
    ensures
        <u64 as RemSpec>::obeys_rem_spec(),
        <u64 as RemSpec>::rem_req(lhs, rhs),
        rust_rem(lhs as int, rhs as int) == 0 ==>
            <u64 as RemSpec>::rem_spec(lhs, rhs) == 0,
        <u64 as RemSpec>::rem_spec(lhs, rhs) != 0 ==>
            rust_rem(lhs as int, rhs as int) != 0,
{
    assert(<u64 as RemSpec>::obeys_rem_spec());
    assert(<u64 as RemSpec>::rem_req(lhs, rhs));
    reveal(rust_rem);
    if rust_rem(lhs as int, rhs as int) == 0 {
        if lhs == 0 {
            lemma_div_of0(rhs as int);
        } else {
            assert(lhs > 0);
        }
        assert((lhs as int) % (rhs as int) == 0);
        assert(<u64 as RemSpec>::rem_spec(lhs, rhs)
            == ((lhs as int) % (rhs as int)) as u64);
    }
}

pub proof fn lemma_number_primitive_division_facts(lhs: &Number, rhs: &Number)
    ensures
        match (lhs, rhs) {
            (Number::Int(lhs), Number::Int(rhs)) =>
                *rhs != 0 && !(*lhs == i64::MIN && *rhs == -1) ==>
                    <i64 as RemSpec>::obeys_rem_spec()
                        && <i64 as RemSpec>::rem_req(*lhs, *rhs)
                        && <i64 as RemSpec>::rem_spec(*lhs, *rhs) as int
                            == rust_rem(*lhs as int, *rhs as int),
            (Number::UInt(lhs), Number::UInt(rhs)) =>
                *rhs != 0 ==>
                    <u64 as RemSpec>::obeys_rem_spec()
                        && <u64 as RemSpec>::rem_req(*lhs, *rhs)
                        && (rust_rem(*lhs as int, *rhs as int) == 0 ==>
                            <u64 as RemSpec>::rem_spec(*lhs, *rhs) == 0)
                        && (<u64 as RemSpec>::rem_spec(*lhs, *rhs) != 0 ==>
                            rust_rem(*lhs as int, *rhs as int) != 0),
            (Number::Int(lhs), Number::UInt(rhs)) =>
                *rhs != 0 ==>
                    *rhs as i128 > 0
                        && <i128 as RemSpec>::obeys_rem_spec()
                        && <i128 as RemSpec>::rem_req(*lhs as i128, *rhs as i128)
                        && <i128 as RemSpec>::rem_spec(*lhs as i128, *rhs as i128) as int
                            == rust_rem(*lhs as int, *rhs as int)
                        && (rust_rem(*lhs as int, *rhs as int) == 0 ==>
                            i128::MIN as int <= rust_div(*lhs as int, *rhs as int)
                                <= i128::MAX as int),
            (Number::UInt(lhs), Number::Int(rhs)) =>
                *rhs != 0 ==>
                    *lhs as i128 >= 0
                        && *rhs as i128 != 0
                        && rust_div(*lhs as int, *rhs as int)
                            == (*lhs as int) / (*rhs as int)
                        && <i128 as RemSpec>::obeys_rem_spec()
                        && <i128 as RemSpec>::rem_req(*lhs as i128, *rhs as i128)
                        && (rust_rem(*lhs as int, *rhs as int) == 0 ==>
                            <i128 as RemSpec>::rem_spec(*lhs as i128, *rhs as i128) == 0)
                        && (<i128 as RemSpec>::rem_spec(*lhs as i128, *rhs as i128) != 0 ==>
                            rust_rem(*lhs as int, *rhs as int) != 0)
                        && (rust_rem(*lhs as int, *rhs as int) == 0 ==>
                            i128::MIN as int <= rust_div(*lhs as int, *rhs as int)
                                <= i128::MAX as int),
            _ => true,
        },
{
    match (lhs, rhs) {
        (Number::Int(lhs), Number::Int(rhs)) => {
            if *rhs != 0 && !(*lhs == i64::MIN && *rhs == -1) {
                lemma_remainder_matches_rust_i64(*lhs, *rhs);
            }
        },
        (Number::UInt(lhs), Number::UInt(rhs)) => {
            if *rhs != 0 {
                lemma_remainder_matches_rust_u64(*lhs, *rhs);
            }
        },
        (Number::Int(lhs), Number::UInt(rhs)) => {
            if *rhs != 0 {
                lemma_remainder_matches_rust_i128(*lhs as i128, *rhs as i128);
                if rust_rem(*lhs as int, *rhs as int) == 0 {
                    lemma_rust_div_fits_i128(*lhs as i128, *rhs as i128);
                }
            }
        },
        (Number::UInt(lhs), Number::Int(rhs)) => {
            if *rhs != 0 {
                lemma_nonnegative_div_matches_rust(*lhs as i128, *rhs as i128);
                lemma_nonnegative_remainder_matches_rust(*lhs as i128, *rhs as i128);
                if rust_rem(*lhs as int, *rhs as int) == 0 {
                    lemma_rust_div_fits_i128(*lhs as i128, *rhs as i128);
                }
            }
        },
        _ => {},
    }
}

pub proof fn lemma_rust_div_fits_i128(lhs: i128, rhs: i128)
    requires
        rhs != 0,
        !(lhs == i128::MIN && rhs == -1),
        rust_rem(lhs as int, rhs as int) == 0,
    ensures
        i128::MIN as int <= rust_div(lhs as int, rhs as int) <= i128::MAX as int,
{
    lemma_exact_rust_div_fits(
        lhs as int,
        rhs as int,
        i128::MIN as int,
        i128::MAX as int,
    );
}

pub proof fn lemma_nonnegative_div_matches_rust(lhs: i128, rhs: i128)
    requires
        lhs >= 0,
        rhs != 0,
    ensures
        rust_div(lhs as int, rhs as int) == (lhs as int) / (rhs as int),
{
    reveal(rust_div);
    if lhs == 0 {
        lemma_div_of0(rhs as int);
    } else {
        assert(lhs > 0);
    }
}

pub proof fn lemma_nonnegative_remainder_matches_rust(lhs: i128, rhs: i128)
    requires
        lhs >= 0,
        rhs != 0,
    ensures
        <i128 as RemSpec>::obeys_rem_spec(),
        <i128 as RemSpec>::rem_req(lhs, rhs),
        rust_rem(lhs as int, rhs as int) == 0 ==>
            <i128 as RemSpec>::rem_spec(lhs, rhs) == 0,
        <i128 as RemSpec>::rem_spec(lhs, rhs) != 0 ==>
            rust_rem(lhs as int, rhs as int) != 0,
{
    assert(<i128 as RemSpec>::obeys_rem_spec());
    assert(<i128 as RemSpec>::rem_req(lhs, rhs));
    reveal(rust_rem);
    if rust_rem(lhs as int, rhs as int) == 0 {
        if lhs == 0 {
            lemma_div_of0(rhs as int);
        } else {
            assert(lhs > 0);
        }
        assert((lhs as int) % (rhs as int) == 0);
        assert(<i128 as RemSpec>::rem_spec(lhs, rhs)
            == ((lhs as int) % (rhs as int)) as i128);
    }
}

}
