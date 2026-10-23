// This file contains assumptions about Rust's primitive numeric types,
// encoded in Verus.
//
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use vstd::prelude::*;

verus! {

use core::cmp::Ordering;
use vstd::arithmetic::power::pow;
use vstd::arithmetic::power2::pow2;
use vstd::float::*;

pub assume_specification[ i128::abs ](value: i128) -> (res: i128)
    requires
        value != i128::MIN,
    ensures
        res as int == if value < 0 { -(value as int) } else { value as int },
;

pub assume_specification[ i64::checked_abs ](value: i64) -> (res: Option<i64>)
    ensures
        if value == i64::MIN {
            res is None
        } else {
            res matches Some(abs) && abs as int == if value < 0 { -(value as int) } else { value as int }
        },
;

pub assume_specification[ u64::checked_pow ](x: u64, exp: u32) -> (res: Option<u64>)
    ensures
        match res {
            Some(value) => value == pow(x as int, exp as nat),
            None => pow(x as int, exp as nat) > u64::MAX,
        },
;

pub open spec fn cmp_float_uint_result(f: f64, n: u64) -> Ordering
{
    if f.is_nan_spec() {
        Ordering::Greater
    } else if !f.is_finite_spec() {
        if f.ieee_lt(0.0f64) { Ordering::Less } else { Ordering::Greater }
    } else if f.ieee_lt(0.0f64) {
        Ordering::Less
    } else if f.ieee_ge(ieee_float_cast::<u64, f64>(u64::MAX)) {
        Ordering::Greater
    } else {
        let integer_part = ieee_float_cast::<f64, u64>(f);
        if integer_part < n {
            Ordering::Less
        } else if integer_part > n ||
            f.ieee_gt(ieee_float_cast::<u64, f64>(integer_part)) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

pub open spec fn cmp_float_sint_result(f: f64, n: i64) -> Ordering
{
    if f.is_nan_spec() {
        Ordering::Greater
    } else if !f.is_finite_spec() {
        if f.ieee_lt(0.0f64) { Ordering::Less } else { Ordering::Greater }
    } else if f.ieee_lt(ieee_float_cast::<i64, f64>(i64::MIN)) {
        Ordering::Less
    } else if f.ieee_ge(ieee_float_cast::<i64, f64>(i64::MAX)) {
        Ordering::Greater
    } else {
        let integer_part = ieee_float_cast::<f64, i64>(f);
        if integer_part < n ||
            (integer_part == n &&
                f.ieee_lt(ieee_float_cast::<i64, f64>(integer_part))) {
            Ordering::Less
        } else if integer_part > n ||
            f.ieee_gt(ieee_float_cast::<i64, f64>(integer_part)) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

pub open spec fn cmp_non_nan_float_result(a: f64, b: f64) -> Ordering
{
    if a.ieee_lt(b) {
        Ordering::Less
    } else if a.ieee_gt(b) {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

pub open spec fn f64_decode_mantissa(f: f64) -> int
{
    if ((f.to_bits_abs_spec() >> 52) as int) == 0 {
        ((f.to_bits_abs_spec() & 0x000f_ffff_ffff_ffff) << 1) as int
    } else {
        ((f.to_bits_abs_spec() & 0x000f_ffff_ffff_ffff) |
            0x0010_0000_0000_0000) as int
    }
}

pub open spec fn f64_decode_exponent(f: f64) -> int
{
    ((f.to_bits_abs_spec() >> 52) as int) - 1075
}

pub open spec fn cmp_float_int_result(f: f64, n: int) -> Ordering
{
    if f.is_nan_spec() {
        Ordering::Greater
    } else if !f.is_finite_spec() {
        if f.ieee_lt(0.0f64) { Ordering::Less } else { Ordering::Greater }
    } else if f64_decode_exponent(f) < 0 {
        let integer_part = ieee_float_cast::<f64, i64>(f) as int;
        if integer_part < n ||
            (integer_part == n &&
                f.ieee_lt(ieee_float_cast::<i64, f64>(integer_part as i64))) {
            Ordering::Less
        } else if integer_part > n ||
            f.ieee_gt(ieee_float_cast::<i64, f64>(integer_part as i64)) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    } else {
        let unsigned = f64_decode_mantissa(f) * pow2(f64_decode_exponent(f) as nat);
        let value = if f.is_sign_negative_spec() { -unsigned } else { unsigned };
        if value < n {
            Ordering::Less
        } else if value > n {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
}

} // end verus!
