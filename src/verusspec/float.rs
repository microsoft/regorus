// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::float_cmp,
    clippy::unwrap_used,
    clippy::unreachable,
    clippy::option_if_let_else,
    clippy::unseparated_literal_suffix,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]

#[cfg(verus_keep_ghost)]
use vstd::float::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialEqIs;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::cmp::PartialOrdIs;
use vstd::prelude::*;

verus! {

pub axiom fn axiom_f64_obeys_eq_spec()
    ensures
        <f64 as vstd::std_specs::cmp::PartialEqSpec>::obeys_eq_spec(),
;

pub axiom fn axiom_f64_obeys_partial_cmp_spec()
    ensures
        <f64 as vstd::std_specs::cmp::PartialOrdSpec>::obeys_partial_cmp_spec(),
;

pub axiom fn axiom_f64_comparisons_match_ieee()
    ensures
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_lt(f2) <==> f1.is_lt(&f2),
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_le(f2) <==> f1.is_le(&f2),
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_gt(f2) <==> f1.is_gt(&f2),
        forall|f1: f64, f2: f64| #[trigger] f1.ieee_ge(f2) <==> f1.is_ge(&f2),
;

pub axiom fn axiom_f64_ops_deterministic()
    ensures
        <f64 as vstd::std_specs::ops::NegSpec>::obeys_neg_spec(),
        <f64 as vstd::std_specs::ops::AddSpec>::obeys_add_spec(),
        <f64 as vstd::std_specs::ops::SubSpec>::obeys_sub_spec(),
        <f64 as vstd::std_specs::ops::MulSpec>::obeys_mul_spec(),
        <f64 as vstd::std_specs::ops::DivSpec>::obeys_div_spec(),
        forall|n: i8, f: f64| float_cast_spec::<i8, f64>(n, f) ==> f == ieee_float_cast::<i8, f64>(n),
        forall|n: u8, f: f64| float_cast_spec::<u8, f64>(n, f) ==> f == ieee_float_cast::<u8, f64>(n),
        forall|n: i8, f: f64| float_cast_spec::<f64, i8>(f, n) ==> n == ieee_float_cast::<f64, i8>(f),
        forall|n: u8, f: f64| float_cast_spec::<f64, u8>(f, n) ==> n == ieee_float_cast::<f64, u8>(f),
        forall|n: i16, f: f64| float_cast_spec::<i16, f64>(n, f) ==> f == ieee_float_cast::<i16, f64>(n),
        forall|n: u16, f: f64| float_cast_spec::<u16, f64>(n, f) ==> f == ieee_float_cast::<u16, f64>(n),
        forall|n: i16, f: f64| float_cast_spec::<f64, i16>(f, n) ==> n == ieee_float_cast::<f64, i16>(f),
        forall|n: u16, f: f64| float_cast_spec::<f64, u16>(f, n) ==> n == ieee_float_cast::<f64, u16>(f),
        forall|n: i32, f: f64| float_cast_spec::<i32, f64>(n, f) ==> f == ieee_float_cast::<i32, f64>(n),
        forall|n: u32, f: f64| float_cast_spec::<u32, f64>(n, f) ==> f == ieee_float_cast::<u32, f64>(n),
        forall|n: i32, f: f64| float_cast_spec::<f64, i32>(f, n) ==> n == ieee_float_cast::<f64, i32>(f),
        forall|n: u32, f: f64| float_cast_spec::<f64, u32>(f, n) ==> n == ieee_float_cast::<f64, u32>(f),
        forall|n: i64, f: f64| float_cast_spec::<i64, f64>(n, f) ==> f == ieee_float_cast::<i64, f64>(n),
        forall|n: u64, f: f64| float_cast_spec::<u64, f64>(n, f) ==> f == ieee_float_cast::<u64, f64>(n),
        forall|n: i64, f: f64| float_cast_spec::<f64, i64>(f, n) ==> n == ieee_float_cast::<f64, i64>(f),
        forall|n: u64, f: f64| float_cast_spec::<f64, u64>(f, n) ==> n == ieee_float_cast::<f64, u64>(f),
        forall|n: i128, f: f64| float_cast_spec::<i128, f64>(n, f) ==> f == ieee_float_cast::<i128, f64>(n),
        forall|n: u128, f: f64| float_cast_spec::<u128, f64>(n, f) ==> f == ieee_float_cast::<u128, f64>(n),
        forall|n: i128, f: f64| float_cast_spec::<f64, i128>(f, n) ==> n == ieee_float_cast::<f64, i128>(f),
        forall|n: u128, f: f64| float_cast_spec::<f64, u128>(f, n) ==> n == ieee_float_cast::<f64, u128>(f),
;

pub assume_specification [ f64::is_finite ](f: f64) -> (res: bool)
    ensures
        res == f.is_finite_spec(),
;

pub uninterp spec fn spec_f64_fract(f: f64) -> f64;

pub assume_specification [ f64::fract ](f: f64) -> (res: f64)
    requires
        f.is_finite_spec(),
    ensures
        res == spec_f64_fract(f),
;

pub uninterp spec fn spec_f64_abs(f: f64) -> f64;

pub assume_specification [ f64::abs ](f: f64) -> (res: f64)
    requires
        f.is_finite_spec(),
    ensures
        res == spec_f64_abs(f),
;

pub assume_specification [ f64::is_nan ](f: f64) -> (res: bool)
    ensures
        res == f.is_nan_spec(),
;

pub uninterp spec fn spec_f64_neg_infinity() -> f64;

#[inline]
#[verifier::external_body]
pub fn f64_neg_infinity() -> (res: f64)
    ensures
        res == spec_f64_neg_infinity(),
{
    f64::NEG_INFINITY
}

pub uninterp spec fn spec_f64_infinity() -> f64;

#[inline]
#[verifier::external_body]
pub fn f64_infinity() -> (res: f64)
    ensures
        res == spec_f64_infinity(),
{
    f64::INFINITY
}

} // end verus!
