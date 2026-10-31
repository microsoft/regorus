// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use vstd::prelude::*;

verus! {

use core::cmp::Ordering;
use crate::number::Number;
use num_bigint::BigInt;
use super::bigint_assumptions::*;
use super::f64_assumptions::*;
use super::number_specs::NumberView;
use vstd::arithmetic::power2::pow2;
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
use vstd::std_specs::cmp::*;
use vstd::std_specs::convert::*;
use vstd::std_specs::ops::*;
use vstd::float::*;

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

pub proof fn lemma_f64_integer_part(f: f64, exponent: int)
    requires
        f.is_finite_spec(),
        exponent == if f64_finite_exponent(f) < 0 { f64_finite_exponent(f) } else { 0 },
    ensures
        0 <= f64_finite_significand(f) < pow2(53),
        f64_scaled_value(f, exponent) >= 0 ==> {
            &&& f64_scaled_value(f, 0) >= 0
            &&& f64_scaled_value(f, 0) * pow2((-exponent) as nat)
                <= f64_scaled_value(f, exponent)
            &&& (f64_scaled_value(f, exponent)
                > f64_scaled_value(f, 0) * pow2((-exponent) as nat)) == f64_has_fraction(f)
        },
        f64_scaled_value(f, exponent) <= 0 ==> {
            &&& f64_scaled_value(f, 0) <= 0
            &&& f64_scaled_value(f, exponent)
                <= f64_scaled_value(f, 0) * pow2((-exponent) as nat)
        },
        (f64_scaled_value(f, 0) - 1) * pow2((-exponent) as nat)
            < f64_scaled_value(f, exponent)
            < (f64_scaled_value(f, 0) + 1) * pow2((-exponent) as nat),
        (f64_scaled_value(f, exponent)
            < f64_scaled_value(f, 0) * pow2((-exponent) as nat))
                == (f.is_sign_negative_spec() && f64_has_fraction(f)),
        (f64_scaled_value(f, exponent)
            > f64_scaled_value(f, 0) * pow2((-exponent) as nat))
                == (!f.is_sign_negative_spec() && f64_has_fraction(f)),
        f64_biased_exponent(f) < 1023 ==> f64_scaled_value(f, 0) == 0,
{
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::arithmetic::power2::lemma_pow2_pos((-exponent) as nat);
    let significand = f64_finite_significand(f);
    let unit = pow2((-exponent) as nat) as int;
    let bits = f.to_bits_abs_spec();
    assert((bits & 0x000f_ffff_ffff_ffff) < 0x0010_0000_0000_0000u64)
        by (bit_vector);
    assert(0 <= significand < pow2(53));
    if exponent < 0 {
        let shift = f64_finite_exponent(f) - exponent;
        let magnitude = significand * pow2(shift as nat);
        assert(magnitude == significand) by (nonlinear_arith)
            requires shift == 0, pow2(0) == 1, magnitude == significand * pow2(shift as nat);
        assert(f64_scaled_value(f, exponent) ==
            if f.is_sign_negative_spec() { -significand } else { significand });
        lemma_fundamental_div_mod(significand, unit);
        vstd::arithmetic::div_mod::lemma_mod_bound(significand, unit);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(significand, unit);
        if f64_biased_exponent(f) < 1023 {
            if -exponent > 53 {
                vstd::arithmetic::power2::lemma_pow2_strictly_increases(
                    53, (-exponent) as nat,
                );
            }
            assert(unit >= pow2(53));
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(
                significand, unit, 0, significand,
            );
        }
        let quotient = significand / unit;
        assert(f64_scaled_value(f, 0) ==
            if f.is_sign_negative_spec() { -quotient } else { quotient });
        assert(quotient * unit <= significand < (quotient + 1) * unit)
            by (nonlinear_arith)
            requires
                significand == unit * quotient + significand % unit,
                0 <= significand % unit < unit;
        assert((significand > quotient * unit) == f64_has_fraction(f))
            by (nonlinear_arith)
            requires
                significand == unit * quotient + significand % unit,
                0 <= significand % unit < unit,
                f64_has_fraction(f) == (significand % unit != 0);
        let value = f64_scaled_value(f, exponent);
        let truncated = f64_scaled_value(f, 0);
        assert({
            &&& (value >= 0 ==> truncated >= 0 && truncated * unit <= value
                && ((value > truncated * unit) == f64_has_fraction(f)))
            &&& (value <= 0 ==> truncated <= 0 && value <= truncated * unit)
            &&& (truncated - 1) * unit < value < (truncated + 1) * unit
            &&& (value < truncated * unit)
                == (f.is_sign_negative_spec() && f64_has_fraction(f))
            &&& (value > truncated * unit)
                == (!f.is_sign_negative_spec() && f64_has_fraction(f))
        }) by (nonlinear_arith)
            requires
                unit > 0,
                quotient >= 0,
                quotient * unit <= significand < (quotient + 1) * unit,
                (significand > quotient * unit) == f64_has_fraction(f),
                value == if f.is_sign_negative_spec() { -significand } else { significand },
                truncated == if f.is_sign_negative_spec() { -quotient } else { quotient };
    } else {
        assert(exponent == 0);
        assert(unit == 1);
        assert(!f64_has_fraction(f));
        assert(f64_scaled_value(f, 0) * unit == f64_scaled_value(f, exponent))
            by (nonlinear_arith)
            requires unit == 1, exponent == 0;
        assert((f64_scaled_value(f, 0) - 1) * unit
            < f64_scaled_value(f, exponent)
            < (f64_scaled_value(f, 0) + 1) * unit)
            by (nonlinear_arith)
            requires unit == 1, exponent == 0;
    }
}

// Cast facts follow execution order: earlier returns do not evaluate the later casts.
pub proof fn lemma_cmp_float_uint(f: f64, n: u64)
    ensures
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        f.is_nan_spec() ==>
            NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) == Ordering::Greater,
        !f.is_nan_spec() && !f.is_finite_spec() ==>
            NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                if f.is_lt(&0.0f64) { Ordering::Less } else { Ordering::Greater },
        f.is_finite_spec() && f.is_lt(&0.0f64) ==>
            NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) == Ordering::Less,
        forall|upper: f64| #[trigger] float_cast_spec::<u64, f64>(u64::MAX, upper)
            && f.is_finite_spec() && !f.is_lt(&0.0f64) ==> {
                &&& f.is_ge(&upper) ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                        == Ordering::Greater
                &&& forall|integer_part: u64| #[trigger] float_cast_spec::<f64, u64>(f, integer_part)
                    && !f.is_ge(&upper) ==> {
                        &&& integer_part < n ==>
                            NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                == Ordering::Less
                        &&& integer_part > n ==>
                            NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                == Ordering::Greater
                        &&& forall|back: f64| #[trigger] float_cast_spec::<u64, f64>(integer_part, back)
                            && integer_part == n ==>
                            NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                                if f.is_gt(&back) { Ordering::Greater } else { Ordering::Equal }
                    }
            },
{
    axiom_f64_obeys_partial_cmp_spec();
    axiom_f64_comparisons_match_ieee();
    axiom_f64_ops_deterministic();
    let exponent = if f64_finite_exponent(f) < 0 {
        f64_finite_exponent(f)
    } else {
        0
    };
    if !f.is_nan_spec() {
        axiom_f64_order_zero(f, exponent);
    }
    vstd::arithmetic::power2::lemma_pow2_pos((-exponent) as nat);
    let value = f64_scaled_value(f, exponent);
    let unit = pow2((-exponent) as nat);
    assert(NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
        if f.is_nan_spec() {
            Ordering::Greater
        } else if !f.is_finite_spec() {
            if f.is_sign_negative_spec() { Ordering::Less } else { Ordering::Greater }
        } else if value < n as int * unit {
            Ordering::Less
        } else if value > n as int * unit {
            Ordering::Greater
        } else {
            Ordering::Equal
        });
    assert(0 <= n as int * unit <= (u64::MAX as int) * unit)
        by (nonlinear_arith)
        requires 0 <= n <= u64::MAX, unit > 0;
    assert(n as int * unit < (u64::MAX as int + 1) * unit)
        by (nonlinear_arith)
        requires 0 <= n <= u64::MAX, unit > 0;
    assert forall|upper: f64| #[trigger] float_cast_spec::<u64, f64>(u64::MAX, upper)
        && f.is_finite_spec() && !f.is_lt(&0.0f64) implies {
            &&& f.is_ge(&upper) ==>
                NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                    == Ordering::Greater
            &&& forall|integer_part: u64| #[trigger] float_cast_spec::<f64, u64>(f, integer_part)
                && !f.is_ge(&upper) ==> {
                    &&& integer_part < n ==>
                        NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                            == Ordering::Less
                    &&& integer_part > n ==>
                        NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                            == Ordering::Greater
                    &&& forall|back: f64| #[trigger] float_cast_spec::<u64, f64>(integer_part, back)
                        && integer_part == n ==>
                        NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                            if f.is_gt(&back) { Ordering::Greater } else { Ordering::Equal }
                }
        } by
    {
        axiom_f64_u64_max_cast(exponent);
        vstd::arithmetic::power2::lemma_pow2_adds(52, (12 - exponent) as nat);
        vstd::arithmetic::power2::lemma_pow2_adds(64, (-exponent) as nat);
        vstd::arithmetic::power2::lemma2_to64();
        assert(f64_scaled_value(upper, exponent)
            == (u64::MAX as int + 1) * unit);
        axiom_f64_finite_order(f, upper, exponent);
        assert forall|integer_part: u64| #[trigger] float_cast_spec::<f64, u64>(f, integer_part)
            && !f.is_ge(&upper) implies {
                &&& integer_part < n ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                        == Ordering::Less
                &&& integer_part > n ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                        == Ordering::Greater
                &&& forall|back: f64| #[trigger] float_cast_spec::<u64, f64>(integer_part, back)
                    && integer_part == n ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                        if f.is_gt(&back) { Ordering::Greater } else { Ordering::Equal }
            } by
        {
            lemma_f64_integer_part(f, exponent);
            assert(f64_scaled_value(f, 0) <= u64::MAX)
                by (nonlinear_arith)
                requires
                    f64_scaled_value(f, 0) * unit <= value,
                    value < (u64::MAX as int + 1) * unit,
                    unit > 0;
            if f64_biased_exponent(f) < 1023 {
                axiom_f64_to_u64_below_one(f);
            } else {
                axiom_f64_to_u64_in_range(f);
            }
            assert(integer_part < n ==> value < n as int * unit)
                by (nonlinear_arith)
                requires
                    value < (integer_part as int + 1) * unit,
                    unit > 0;
            assert(integer_part > n ==> value > n as int * unit)
                by (nonlinear_arith)
                requires
                    integer_part as int * unit <= value,
                    unit > 0;
            assert forall|back: f64| #[trigger] float_cast_spec::<u64, f64>(integer_part, back)
                && integer_part == n implies
                NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                    if f.is_gt(&back) { Ordering::Greater } else { Ordering::Equal } by
            {
                axiom_f64_to_u64_backcast(f);
            }
        }
    }
}

pub proof fn lemma_cmp_float_sint(f: f64, n: i64)
    ensures
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        f.is_nan_spec() ==>
            NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) == Ordering::Greater,
        !f.is_nan_spec() && !f.is_finite_spec() ==>
            NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                if f.is_lt(&0.0f64) { Ordering::Less } else { Ordering::Greater },
        forall|lower: f64| #[trigger] float_cast_spec::<i64, f64>(i64::MIN, lower)
            && f.is_finite_spec() ==> {
                &&& f.is_lt(&lower) ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                        == Ordering::Less
                &&& forall|upper: f64| #[trigger] float_cast_spec::<i64, f64>(i64::MAX, upper)
                    && !f.is_lt(&lower) ==> {
                        &&& f.is_ge(&upper) ==>
                            NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                == Ordering::Greater
                        &&& forall|integer_part: i64| #[trigger] float_cast_spec::<f64, i64>(f, integer_part)
                            && !f.is_ge(&upper) ==> {
                                &&& integer_part < n ==>
                                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                        == Ordering::Less
                                &&& integer_part > n ==>
                                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                        == Ordering::Greater
                                &&& forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                                    && integer_part == n ==>
                                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                                        if f.is_lt(&back) { Ordering::Less }
                                        else if f.is_gt(&back) { Ordering::Greater }
                                        else { Ordering::Equal }
                            }
                    }
            },
{
    axiom_f64_obeys_partial_cmp_spec();
    axiom_f64_comparisons_match_ieee();
    axiom_f64_ops_deterministic();
    let exponent = if f64_finite_exponent(f) < 0 {
        f64_finite_exponent(f)
    } else {
        0
    };
    if !f.is_nan_spec() {
        axiom_f64_order_zero(f, exponent);
    }
    vstd::arithmetic::power2::lemma_pow2_pos((-exponent) as nat);
    let value = f64_scaled_value(f, exponent);
    let unit = pow2((-exponent) as nat);
    assert((if n < 0 { -(-(n as int) * unit) } else { n as int * unit })
        == n as int * unit) by (nonlinear_arith);
    assert(NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
        if f.is_nan_spec() {
            Ordering::Greater
        } else if !f.is_finite_spec() {
            if f.is_sign_negative_spec() { Ordering::Less } else { Ordering::Greater }
        } else if value < n as int * unit {
            Ordering::Less
        } else if value > n as int * unit {
            Ordering::Greater
        } else {
            Ordering::Equal
        });
    assert(i64::MIN as int * unit <= n as int * unit
        < (i64::MAX as int + 1) * unit)
        by (nonlinear_arith)
        requires i64::MIN <= n <= i64::MAX, unit > 0;
    axiom_f64_i64_limit_casts();
    vstd::arithmetic::power2::lemma_pow2_adds(52, (11 - exponent) as nat);
    vstd::arithmetic::power2::lemma_pow2_adds(63, (-exponent) as nat);
    vstd::arithmetic::power2::lemma2_to64_rest();
    assert(-(pow2(63) as int * unit) == i64::MIN as int * unit)
        by (nonlinear_arith)
        requires pow2(63) == 9_223_372_036_854_775_808;
    assert forall|lower: f64| #[trigger] float_cast_spec::<i64, f64>(i64::MIN, lower)
        && f.is_finite_spec() implies {
            &&& f.is_lt(&lower) ==>
                NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                    == Ordering::Less
            &&& forall|upper: f64| #[trigger] float_cast_spec::<i64, f64>(i64::MAX, upper)
                && !f.is_lt(&lower) ==> {
                    &&& f.is_ge(&upper) ==>
                        NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                            == Ordering::Greater
                    &&& forall|integer_part: i64| #[trigger] float_cast_spec::<f64, i64>(f, integer_part)
                        && !f.is_ge(&upper) ==> {
                            &&& integer_part < n ==>
                                NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                    == Ordering::Less
                            &&& integer_part > n ==>
                                NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                    == Ordering::Greater
                            &&& forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                                && integer_part == n ==>
                                NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                                    if f.is_lt(&back) { Ordering::Less }
                                    else if f.is_gt(&back) { Ordering::Greater }
                                    else { Ordering::Equal }
                        }
                }
        } by
    {
        assert(f64_scaled_value(lower, exponent) == i64::MIN as int * unit);
        axiom_f64_finite_order(f, lower, exponent);
        assert forall|upper: f64| #[trigger] float_cast_spec::<i64, f64>(i64::MAX, upper)
            && !f.is_lt(&lower) implies {
                &&& f.is_ge(&upper) ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                        == Ordering::Greater
                &&& forall|integer_part: i64| #[trigger] float_cast_spec::<f64, i64>(f, integer_part)
                    && !f.is_ge(&upper) ==> {
                        &&& integer_part < n ==>
                            NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                == Ordering::Less
                        &&& integer_part > n ==>
                            NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                                == Ordering::Greater
                        &&& forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                            && integer_part == n ==>
                            NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                                if f.is_lt(&back) { Ordering::Less }
                                else if f.is_gt(&back) { Ordering::Greater }
                                else { Ordering::Equal }
                    }
            } by
        {
            assert(f64_scaled_value(upper, exponent) == (i64::MAX as int + 1) * unit);
            axiom_f64_finite_order(f, upper, exponent);
            assert forall|integer_part: i64| #[trigger] float_cast_spec::<f64, i64>(f, integer_part)
                && !f.is_ge(&upper) implies {
                    &&& integer_part < n ==>
                        NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                            == Ordering::Less
                    &&& integer_part > n ==>
                        NumberView::Float(f).cmp_values(NumberView::Integer(n as int))
                            == Ordering::Greater
                    &&& forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                        && integer_part == n ==>
                        NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                            if f.is_lt(&back) { Ordering::Less }
                            else if f.is_gt(&back) { Ordering::Greater }
                            else { Ordering::Equal }
                } by
            {
                lemma_f64_integer_part(f, exponent);
                let truncated = f64_scaled_value(f, 0);
                if value >= 0 {
                    assert(truncated <= i64::MAX) by (nonlinear_arith)
                        requires
                            truncated * unit <= value,
                            value < (i64::MAX as int + 1) * unit,
                            unit > 0;
                } else {
                    assert(truncated >= i64::MIN) by (nonlinear_arith)
                        requires
                            i64::MIN as int * unit <= value,
                            value <= truncated * unit,
                            unit > 0;
                }
                if f64_biased_exponent(f) < 1023 {
                    axiom_f64_to_i64_below_one(f);
                } else {
                    axiom_f64_to_i64_in_range(f);
                }
                assert(integer_part < n ==> value < n as int * unit)
                    by (nonlinear_arith)
                    requires value < (integer_part as int + 1) * unit, unit > 0;
                assert(integer_part > n ==> value > n as int * unit)
                    by (nonlinear_arith)
                    requires (integer_part as int - 1) * unit < value, unit > 0;
                assert forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                    && integer_part == n implies
                    NumberView::Float(f).cmp_values(NumberView::Integer(n as int)) ==
                        if f.is_lt(&back) { Ordering::Less }
                        else if f.is_gt(&back) { Ordering::Greater }
                        else { Ordering::Equal } by
                {
                    axiom_f64_to_i64_backcast(f);
                }
            }
        }
    }
}

pub proof fn lemma_cmp_float_int(f: f64, n: &BigInt)
    ensures
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        <BigInt as OrdSpec>::obeys_cmp_spec(),
        forall|value: &BigInt| match #[trigger] value.cmp_spec(n) {
            Ordering::Less => value@ < n@,
            Ordering::Greater => value@ > n@,
            Ordering::Equal => value@ == n@,
        },
        <BigInt as NegSpec>::obeys_neg_spec(),
        forall|value: BigInt| #[trigger] value.neg_req(),
        forall|value: BigInt| #[trigger] value.neg_spec()@ == -value@,
        <BigInt as ShlSpec<usize>>::obeys_shl_spec(),
        forall|value: BigInt, shift: usize| #[trigger] value.shl_req(shift),
        forall|value: BigInt, shift: usize| #[trigger] value.shl_spec(shift)@
            == value@ * pow2(shift as nat) as int,
        f.is_nan_spec() ==>
            NumberView::Float(f).cmp_values(NumberView::Integer(n@)) == Ordering::Greater,
        !f.is_nan_spec() && !f.is_finite_spec() ==>
            NumberView::Float(f).cmp_values(NumberView::Integer(n@)) ==
                if f.is_lt(&0.0f64) { Ordering::Less } else { Ordering::Greater },
        forall|decoded: (u64, i16, i8)| #[trigger] f64_integer_decode_ensures(f, decoded)
            && f.is_finite_spec() ==> {
                &&& (decoded.1 < 0) == (f64_finite_exponent(f) < 0)
                &&& decoded.1 >= 0 ==> {
                    let value = (if f.is_sign_negative_spec() {
                        -(decoded.0 as int)
                    } else {
                        decoded.0 as int
                    }) * pow2((decoded.1 as usize) as nat);
                    NumberView::Float(f).cmp_values(NumberView::Integer(n@)) ==
                        if value < n@ { Ordering::Less }
                        else if value > n@ { Ordering::Greater }
                        else { Ordering::Equal }
                }
            },
        f.is_finite_spec() && f64_finite_exponent(f) < 0 ==>
            forall|integer_part: i64| #[trigger] float_cast_spec::<f64, i64>(f, integer_part) ==> {
                &&& NumberView::Integer(n@).cmp_values(NumberView::Integer(integer_part as int)) ==
                    if n@ < integer_part as int { Ordering::Less }
                    else if n@ > integer_part as int { Ordering::Greater }
                    else { Ordering::Equal }
                &&& (integer_part as int) < n@ ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n@)) == Ordering::Less
                &&& (integer_part as int) > n@ ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n@)) == Ordering::Greater
                &&& forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                    && (integer_part as int) == n@ ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n@)) ==
                        if f.is_lt(&back) { Ordering::Less }
                        else if f.is_gt(&back) { Ordering::Greater }
                        else { Ordering::Equal }
            },
{
    axiom_f64_obeys_partial_cmp_spec();
    axiom_f64_comparisons_match_ieee();
    axiom_f64_ops_deterministic();
    axiom_bigint_obeys_cmp_spec();
    axiom_bigint_obeys_shl_spec();
    axiom_bigint_neg_spec(*n);
    assert forall|value: BigInt| #[trigger] value.neg_req() by {
        axiom_bigint_neg_spec(value);
    }
    assert forall|value: BigInt| #[trigger] value.neg_spec()@ == -value@ by {
        axiom_bigint_neg_spec(value);
    }
    let exponent = if f64_finite_exponent(f) < 0 { f64_finite_exponent(f) } else { 0 };
    if !f.is_nan_spec() {
        axiom_f64_order_zero(f, exponent);
    }
    vstd::arithmetic::power2::lemma2_to64();
    vstd::arithmetic::power2::lemma2_to64_rest();
    vstd::arithmetic::power2::lemma_pow2_pos((-exponent) as nat);
    let value = f64_scaled_value(f, exponent);
    let unit = pow2((-exponent) as nat);
    assert((if n@ < 0 { -(-n@ * unit) } else { n@ * unit }) == n@ * unit)
        by (nonlinear_arith);
    assert(NumberView::Float(f).cmp_values(NumberView::Integer(n@)) ==
        if f.is_nan_spec() {
            Ordering::Greater
        } else if !f.is_finite_spec() {
            if f.is_sign_negative_spec() { Ordering::Less } else { Ordering::Greater }
        } else if value < n@ * unit {
            Ordering::Less
        } else if value > n@ * unit {
            Ordering::Greater
        } else {
            Ordering::Equal
        });
    assert forall|decoded: (u64, i16, i8)| #[trigger] f64_integer_decode_ensures(f, decoded)
        && f.is_finite_spec() implies {
            &&& (decoded.1 < 0) == (f64_finite_exponent(f) < 0)
            &&& decoded.1 >= 0 ==> {
                let integral = (if f.is_sign_negative_spec() {
                    -(decoded.0 as int)
                } else {
                    decoded.0 as int
                }) * pow2((decoded.1 as usize) as nat);
                NumberView::Float(f).cmp_values(NumberView::Integer(n@)) ==
                    if integral < n@ { Ordering::Less }
                    else if integral > n@ { Ordering::Greater }
                    else { Ordering::Equal }
            }
        } by
    {
        if decoded.1 >= 0 {
            let bits = f.to_bits_abs_spec();
            assert((bits >> 52) < 2047u64) by (bit_vector)
                requires bits < 0x7ff0_0000_0000_0000u64;
            assert(0 < f64_biased_exponent(f) < 2047);
            assert((decoded.1 as usize) as int == f64_finite_exponent(f));
            assert(value == (if f.is_sign_negative_spec() {
                -(decoded.0 as int)
            } else {
                decoded.0 as int
            }) * pow2((decoded.1 as usize) as nat))
                by (nonlinear_arith)
                requires
                    exponent == 0,
                    f64_finite_exponent(f) == (decoded.1 as usize) as int,
                    decoded.0 as int == f64_finite_significand(f),
                    value == if f.is_sign_negative_spec() {
                        -(f64_finite_significand(f) * pow2(f64_finite_exponent(f) as nat))
                    } else {
                        f64_finite_significand(f) * pow2(f64_finite_exponent(f) as nat)
                    };
            assert(n@ * unit == n@) by (nonlinear_arith) requires unit == 1;
        }
    }
    if f.is_finite_spec() && f64_finite_exponent(f) < 0 {
        lemma_f64_integer_part(f, exponent);
        let significand = f64_finite_significand(f);
        assert(value == if f.is_sign_negative_spec() { -significand } else { significand })
            by (nonlinear_arith)
            requires
                exponent == f64_finite_exponent(f),
                pow2(0) == 1,
                value == if f.is_sign_negative_spec() { -(significand * pow2(0)) }
                    else { significand * pow2(0) };
        let truncated = f64_scaled_value(f, 0);
        assert(i64::MIN <= truncated <= i64::MAX) by (nonlinear_arith)
            requires
                -(pow2(53) as int) < value < pow2(53),
                pow2(53) == 9_007_199_254_740_992,
                unit >= 1,
                value >= 0 ==> truncated >= 0 && truncated * unit <= value,
                value <= 0 ==> truncated <= 0 && value <= truncated * unit;
        if f64_biased_exponent(f) < 1023 {
            axiom_f64_to_i64_below_one(f);
        } else {
            axiom_f64_to_i64_in_range(f);
        }
        assert forall|integer_part: i64| #[trigger] float_cast_spec::<f64, i64>(f, integer_part)
            implies {
                &&& NumberView::Integer(n@).cmp_values(NumberView::Integer(integer_part as int)) ==
                    if n@ < integer_part as int { Ordering::Less }
                    else if n@ > integer_part as int { Ordering::Greater }
                    else { Ordering::Equal }
                &&& (integer_part as int) < n@ ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n@)) == Ordering::Less
                &&& (integer_part as int) > n@ ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n@)) == Ordering::Greater
                &&& forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                    && (integer_part as int) == n@ ==>
                    NumberView::Float(f).cmp_values(NumberView::Integer(n@)) ==
                        if f.is_lt(&back) { Ordering::Less }
                        else if f.is_gt(&back) { Ordering::Greater }
                        else { Ordering::Equal }
            } by
        {
            lemma_integer_cmp_values(n@, integer_part as int);
            assert((integer_part as int) < n@ ==> value < n@ * unit)
                by (nonlinear_arith)
                requires value < (integer_part as int + 1) * unit, unit > 0;
            assert((integer_part as int) > n@ ==> value > n@ * unit)
                by (nonlinear_arith)
                requires (integer_part as int - 1) * unit < value, unit > 0;
            assert forall|back: f64| #[trigger] float_cast_spec::<i64, f64>(integer_part, back)
                && (integer_part as int) == n@ implies
                NumberView::Float(f).cmp_values(NumberView::Integer(n@)) ==
                    if f.is_lt(&back) { Ordering::Less }
                    else if f.is_gt(&back) { Ordering::Greater }
                    else { Ordering::Equal } by
            {
                axiom_f64_to_i64_backcast(f);
            }
        }
    }
}

pub proof fn lemma_cmp_non_nan_float(a: f64, b: f64)
    requires
        !a.is_nan_spec(),
        !b.is_nan_spec(),
    ensures
        <f64 as PartialOrdSpec>::obeys_partial_cmp_spec(),
        NumberView::Float(a).cmp_values(NumberView::Float(b)) ==
            if a.is_lt(&b) { Ordering::Less }
            else if a.is_gt(&b) { Ordering::Greater }
            else { Ordering::Equal },
{
    axiom_f64_obeys_partial_cmp_spec();
    axiom_f64_comparisons_match_ieee();
    if a.is_finite_spec() && b.is_finite_spec() {
        let exponent = if f64_finite_exponent(a) < f64_finite_exponent(b) {
            f64_finite_exponent(a)
        } else {
            f64_finite_exponent(b)
        };
        axiom_f64_finite_order(a, b, exponent);
    } else if !a.is_finite_spec() {
        assert(a.is_infinite_spec());
        axiom_f64_infinite_order(b, a);
    } else {
        assert(b.is_infinite_spec());
        axiom_f64_infinite_order(a, b);
    }
}

pub open spec fn reverse_ordering(ordering: Ordering) -> Ordering
{
    match ordering {
        Ordering::Less => Ordering::Greater,
        Ordering::Equal => Ordering::Equal,
        Ordering::Greater => Ordering::Less,
    }
}

pub proof fn lemma_integer_cmp_values(lhs: int, rhs: int)
    ensures
        NumberView::Integer(lhs).cmp_values(NumberView::Integer(rhs)) ==
            if lhs < rhs {
                Ordering::Less
            } else if lhs > rhs {
                Ordering::Greater
            } else {
                Ordering::Equal
            },
{
    vstd::arithmetic::power::lemma_pow0(2);
    assert(NumberView::Integer(lhs).cmp_values(NumberView::Integer(rhs)) ==
        if lhs < rhs {
            Ordering::Less
        } else if lhs > rhs {
            Ordering::Greater
        } else {
            Ordering::Equal
        }) by (nonlinear_arith)
        requires pow2(0) == 1;
}

pub proof fn lemma_integer_cmp_values_reverse(lhs: int, rhs: int)
    ensures
        reverse_ordering(
            NumberView::Integer(lhs).cmp_values(NumberView::Integer(rhs)),
        ) == NumberView::Integer(rhs).cmp_values(NumberView::Integer(lhs)),
{
    lemma_integer_cmp_values(lhs, rhs);
    lemma_integer_cmp_values(rhs, lhs);
}

pub proof fn lemma_mixed_cmp_values_reverse(f: f64, n: int)
    ensures
        reverse_ordering(
            NumberView::Float(f).cmp_values(NumberView::Integer(n)),
        ) == NumberView::Integer(n).cmp_values(NumberView::Float(f)),
        reverse_ordering(
            NumberView::Integer(n).cmp_values(NumberView::Float(f)),
        ) == NumberView::Float(f).cmp_values(NumberView::Integer(n)),
{
    reveal(pow2);
}

pub proof fn lemma_eq_values_iff_cmp_equal(lhs: NumberView, rhs: NumberView)
    ensures
        lhs.eq_values(rhs) <==> lhs.cmp_values(rhs) == Ordering::Equal,
{
    reveal(pow2);
}

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
                && (lhs_float / rhs_float).is_finite_spec()
            ==> #[trigger] lhs.div_ensures(rhs, NumberView::Float(lhs_float / rhs_float)),
        forall|lhs_float: f64, rhs_float: f64|
            (lhs is Float || rhs is Float) && !rhs.is_zero() && lhs.to_f64_lossy_ensures(lhs_float)
                && rhs.to_f64_lossy_ensures(rhs_float) && (lhs_float / rhs_float).is_finite_spec()
            ==> #[trigger] lhs.div_ensures(rhs, NumberView::Float(lhs_float / rhs_float)),
{
    reveal(NumberView::is_finite);
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
