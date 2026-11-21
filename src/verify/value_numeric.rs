// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Canonical number keys for history data. Two numbers have the same key exactly when
//! `NumberView::cmp_values` (src/verify/number_specs.rs) says they are equal.
#![allow(clippy::arithmetic_side_effects, clippy::as_conversions)]

use super::number_specs::*;
use core::cmp::Ordering;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::lemma_mul_basics;
use vstd::arithmetic::power2::*;
use vstd::float::*;
use vstd::prelude::*;

verus! {

/// Canonical number key for `Data`. Structural equality coincides with
/// `NumberView::cmp_values(..) == Ordering::Equal`; see `lemma_numeric_of_eq`.
pub struct Numeric {
    pub rank: int,
    pub units: int,
}

/// Signed value in units of 2^-1074; NaN/Inf payload bits scaled the same way (exponent 0).
pub open spec fn scaled_units(n: NumberView) -> int {
    let unsigned = n.scaled_magnitude() * pow2((n.scaled_exponent() + 1074) as nat) as int;
    if n.scaled_sign() { -unsigned } else { unsigned }
}

pub open spec fn numeric_of(n: NumberView) -> Numeric {
    Numeric { rank: n.cmp_rank(), units: scaled_units(n) }
}

pub proof fn lemma_scaled_exponent_lower_bound(n: NumberView)
    ensures n.scaled_exponent() >= -1074,
{
}

/// `scaled_units` factors through any common exponent `c` at or below the number's own.
proof fn lemma_scaled_units_factor(n: NumberView, c: int)
    requires -1074 <= c <= n.scaled_exponent(),
    ensures ({
        let unsigned = n.scaled_magnitude() * pow2((n.scaled_exponent() - c) as nat) as int;
        let signed = if n.scaled_sign() { -unsigned } else { unsigned };
        scaled_units(n) == signed * pow2((c + 1074) as nat) as int
    }),
{
    let m = n.scaled_magnitude();
    let shift = (n.scaled_exponent() - c) as nat;
    let base = (c + 1074) as nat;
    lemma_pow2_adds(shift, base);
    assert(shift + base == (n.scaled_exponent() + 1074) as nat);
    let p = pow2(shift) as int;
    let q = pow2(base) as int;
    assert(m * (p * q) == (m * p) * q) by(nonlinear_arith);
    assert(-(m * (p * q)) == (-(m * p)) * q) by(nonlinear_arith);
}

pub proof fn lemma_numeric_of_eq(a: NumberView, b: NumberView)
    ensures (numeric_of(a) == numeric_of(b)) == (a.cmp_values(b) == Ordering::Equal),
{
    if a.cmp_rank() == b.cmp_rank() {
        lemma_scaled_exponent_lower_bound(a);
        lemma_scaled_exponent_lower_bound(b);
        let ea = a.scaled_exponent();
        let eb = b.scaled_exponent();
        let c = if ea < eb { ea } else { eb };
        lemma_scaled_units_factor(a, c);
        lemma_scaled_units_factor(b, c);
        lemma_pow2_pos((c + 1074) as nat);
        let ua = a.scaled_magnitude() * pow2((ea - c) as nat) as int;
        let ub = b.scaled_magnitude() * pow2((eb - c) as nat) as int;
        let la = if a.scaled_sign() { -ua } else { ua };
        let lb = if b.scaled_sign() { -ub } else { ub };
        let k = pow2((c + 1074) as nat) as int;
        assert((la * k == lb * k) == (la == lb)) by(nonlinear_arith)
            requires k > 0;
    }
}

/// Exact float-to-index conversion: `Some(i)` iff `f == i` exactly and `0 <= i <= u64::MAX`.
pub open spec fn float_index_spec(f: f64) -> Option<u64> {
    let biased = f64_biased_exponent(f);
    let significand = f64_scaled_significand(f);
    if f.to_bits_abs_spec() == 0 {
        Some(0)
    } else if f.is_sign_negative_spec() || biased < 1023 {
        None
    } else if biased <= 1074 {
        let divisor = pow2((1075 - biased) as nat) as int;
        if significand % divisor == 0 { Some((significand / divisor) as u64) } else { None }
    } else if biased <= 1086 {
        Some((significand * pow2((biased - 1075) as nat) as int) as u64)
    } else {
        None
    }
}

/// Bit-field facts about `to_bits_abs_spec`.
pub proof fn lemma_f64_fields(f: f64)
    ensures
        0 <= f64_biased_exponent(f) <= 2047,
        0 <= f64_fraction(f) < 0x0010_0000_0000_0000int,
        (f.to_bits_abs_spec() == 0) == (f64_biased_exponent(f) == 0 && f64_fraction(f) == 0),
        (f.to_bits_abs_spec() < 0x7ff0_0000_0000_0000u64) == (f64_biased_exponent(f) < 2047),
{
    let abs = f.to_bits_abs_spec();
    assert(abs < 0x8000_0000_0000_0000u64);
    assert(abs < 0x8000_0000_0000_0000u64 ==> (abs >> 52) <= 2047u64) by(bit_vector);
    assert((abs & 0x000f_ffff_ffff_ffffu64) < 0x0010_0000_0000_0000u64) by(bit_vector);
    assert((abs == 0) == ((abs >> 52) == 0 && (abs & 0x000f_ffff_ffff_ffffu64) == 0)) by(bit_vector);
    assert(abs < 0x8000_0000_0000_0000u64 ==>
        ((abs < 0x7ff0_0000_0000_0000u64) == ((abs >> 52) < 2047u64))) by(bit_vector);
}

/// `a * scale` with `scale == factor * divisor` selects the index `a / divisor` exactly.
proof fn lemma_fraction_index(significand: int, factor: int, divisor: int)
    requires significand >= 0, factor > 0, divisor > 0, factor * divisor == pow2(1074),
    ensures ({
        let units = significand * factor;
        let scale = pow2(1074) as int;
        &&& units >= 0
        &&& (units % scale == 0) == (significand % divisor == 0)
        &&& units % scale == 0 ==> units / scale == significand / divisor
    }),
{
    lemma_fundamental_div_mod(significand, divisor);
    lemma_mod_pos_bound(significand, divisor);
    let quotient = significand / divisor;
    let remainder = significand % divisor;
    assert(significand * factor == quotient * (factor * divisor) + remainder * factor) by(nonlinear_arith)
        requires significand == divisor * quotient + remainder;
    assert(0 <= remainder * factor < factor * divisor) by(nonlinear_arith)
        requires 0 <= remainder < divisor, factor > 0;
    lemma_fundamental_div_mod_converse(significand * factor, factor * divisor, quotient, remainder * factor);
    assert((remainder * factor == 0) == (remainder == 0)) by(nonlinear_arith)
        requires factor > 0;
    assert(significand * factor >= 0) by(nonlinear_arith)
        requires significand >= 0, factor > 0;
}

/// Bridge from the native bit pattern to the `to_bits_abs_spec` field views.
pub proof fn lemma_float_bits(f: f64, bits: u64)
    requires bits == f.to_bits_spec(),
    ensures
        (bits & 0x7fff_ffff_ffff_ffffu64) == f.to_bits_abs_spec(),
        ((bits & 0x8000_0000_0000_0000u64) != 0) == f.is_sign_negative_spec(),
        ((bits & 0x7fff_ffff_ffff_ffffu64) >> 52) as int == f64_biased_exponent(f),
        ((bits & 0x7fff_ffff_ffff_ffffu64) & 0x000f_ffff_ffff_ffffu64) as int == f64_fraction(f),
{
    assert((bits & 0x7fff_ffff_ffff_ffffu64) == if bits >= 0x8000_0000_0000_0000u64 {
        (bits - 0x8000_0000_0000_0000u64) as u64
    } else {
        bits
    }) by(bit_vector);
    assert(((bits & 0x8000_0000_0000_0000u64) != 0) == (bits >= 0x8000_0000_0000_0000u64)) by(bit_vector);
}

pub proof fn lemma_float_index_matches_numeric(f: f64)
    ensures match float_index_spec(f) {
        Some(i) => numeric_of(NumberView::Float(f)) == Numeric { rank: 0, units: i as int * pow2(1074) as int },
        None => numeric_of(NumberView::Float(f)).rank != 0
             || scaled_units(NumberView::Float(f)) < 0
             || scaled_units(NumberView::Float(f)) % (pow2(1074) as int) != 0
             || scaled_units(NumberView::Float(f)) / (pow2(1074) as int) > u64::MAX,
    },
{
    lemma2_to64();
    lemma2_to64_rest();
    lemma_f64_fields(f);
    lemma_pow2_pos(1074);
    let n = NumberView::Float(f);
    let biased = f64_biased_exponent(f);
    let fraction = f64_fraction(f);
    let significand = f64_scaled_significand(f);
    let scale = pow2(1074) as int;
    let units = scaled_units(n);
    if f.to_bits_abs_spec() == 0 {
        assert(significand == 0);
        assert(units == 0);
        assert(n.cmp_rank() == 0);
        lemma_mul_basics(scale);
        assert(float_index_spec(f) == Some(0u64));
        return;
    }
    if biased == 2047 {
        assert(!f.is_finite_spec());
        assert(n.cmp_rank() != 0);
        return;
    }
    assert(f.is_finite_spec());
    assert(n.cmp_rank() == 0);
    lemma_scaled_exponent_lower_bound(n);
    let shift = (n.scaled_exponent() + 1074) as nat;
    lemma_pow2_pos(shift);
    let unsigned = significand * pow2(shift) as int;
    assert(significand > 0) by {
        if biased == 0 { assert(fraction != 0); }
    }
    assert(unsigned > 0) by(nonlinear_arith)
        requires significand > 0, pow2(shift) > 0, unsigned == significand * pow2(shift) as int;
    if f.is_sign_negative_spec() {
        assert(units < 0);
        return;
    }
    assert(units == unsigned);
    if biased < 1023 {
        // 0 < |f| < 1: below one whole unit of 2^1074.
        assert(significand < 0x0020_0000_0000_0000int);
        if biased == 0 {
            assert(shift == 0);
            assert(pow2(0) == 1);
            lemma_mul_basics(significand);
            assert(unsigned == significand);
            lemma_pow2_strictly_increases(53, 1074);
            assert(pow2(53) == 0x0020_0000_0000_0000nat);
        } else {
            assert(shift == (biased - 1) as nat);
            lemma_pow2_adds(53, shift);
            assert(pow2(53) == 0x0020_0000_0000_0000nat);
            assert(unsigned < pow2(53 + shift) as int) by(nonlinear_arith)
                requires significand < 0x0020_0000_0000_0000int, pow2(shift) > 0,
                    unsigned == significand * pow2(shift) as int,
                    pow2(53 + shift) as int == 0x0020_0000_0000_0000int * pow2(shift) as int;
            if 53 + shift < 1074 { lemma_pow2_strictly_increases(53 + shift, 1074); }
        }
        assert(0 < unsigned < scale);
        lemma_small_mod(unsigned as nat, scale as nat);
        return;
    }
    assert(significand == fraction + 0x0010_0000_0000_0000int);
    assert(0x0010_0000_0000_0000int <= significand < 0x0020_0000_0000_0000int);
    assert(shift == (biased - 1) as nat);
    if biased <= 1074 {
        let factor = pow2(shift) as int;
        let divisor = pow2((1075 - biased) as nat) as int;
        lemma_pow2_pos((1075 - biased) as nat);
        lemma_pow2_adds(shift, (1075 - biased) as nat);
        assert(shift + (1075 - biased) as nat == 1074);
        assert(factor * divisor == scale);
        lemma_fraction_index(significand, factor, divisor);
        if significand % divisor == 0 {
            lemma_div_pos_is_pos(significand, divisor);
            lemma_div_is_ordered_by_denominator(significand, 1, divisor);
            assert(significand / 1 == significand);
            assert(0 <= significand / divisor <= significand);
            assert((significand / divisor) as u64 as int == significand / divisor);
            lemma_fundamental_div_mod(units, scale);
            let q = units / scale;
            assert(q == significand / divisor);
            assert(units == q * scale) by(nonlinear_arith)
                requires units == scale * q + units % scale, units % scale == 0;
        }
        return;
    }
    let shift2 = (biased - 1075) as nat;
    let factor = pow2(shift2) as int;
    lemma_pow2_pos(shift2);
    lemma_pow2_adds(shift2, 1074);
    assert(shift2 + 1074 == shift);
    let integer = significand * factor;
    assert(units == integer * scale) by(nonlinear_arith)
        requires units == significand * pow2(shift) as int,
            pow2(shift) as int == pow2(shift2) as int * pow2(1074) as int,
            integer == significand * factor, factor == pow2(shift2) as int, scale == pow2(1074) as int;
    assert(integer > 0) by(nonlinear_arith)
        requires significand > 0, factor > 0, integer == significand * factor;
    assert(scale * integer == integer * scale) by(nonlinear_arith);
    lemma_mod_multiples_basic(integer, scale);
    lemma_div_multiples_vanish(integer, scale);
    if biased <= 1086 {
        if shift2 < 11 { lemma_pow2_strictly_increases(shift2, 11); }
        assert(pow2(11) == 2048);
        assert(integer < 18446744073709551616int) by(nonlinear_arith)
            requires significand < 0x0020_0000_0000_0000int, 0 < factor <= 2048, integer == significand * factor;
        assert(integer as u64 as int == integer);
    } else {
        if 12 < shift2 { lemma_pow2_strictly_increases(12, shift2); }
        assert(pow2(12) == 4096);
        assert(integer >= 18446744073709551616int) by(nonlinear_arith)
            requires significand >= 0x0010_0000_0000_0000int, factor >= 4096, integer == significand * factor;
    }
}

} // verus!
