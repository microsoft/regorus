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

use vstd::prelude::*;

verus! {

pub uninterp spec fn spec_f64_as_u64(f: f64) -> u64;

#[inline]
#[verifier::external_body]
pub fn f64_as_u64(f: f64) -> (res: u64)
    ensures
        res == spec_f64_as_u64(f),
{
    f as u64
}

pub uninterp spec fn spec_u64_as_f64(u: u64) -> f64;

#[inline]
#[verifier::external_body]
pub fn u64_as_f64(u: u64) -> (res: f64)
    ensures
        res == spec_u64_as_f64(u),
{
    u as f64
}

pub uninterp spec fn spec_f64_as_i64(f: f64) -> i64;

#[inline]
#[verifier::external_body]
pub fn f64_as_i64(f: f64) -> (res: i64)
    ensures
        res == spec_f64_as_i64(f),
{
    f as i64
}

pub uninterp spec fn spec_i64_as_f64(u: i64) -> f64;

#[inline]
#[verifier::external_body]
pub fn i64_as_f64(i: i64) -> (res: f64)
    ensures
        res == spec_i64_as_f64(i),
{
    i as f64
}

pub uninterp spec fn spec_f64_is_finite(f: f64) -> bool;

pub assume_specification [ f64::is_finite ](f: f64) -> (res: bool)
    ensures
        res == spec_f64_is_finite(f),
;

pub uninterp spec fn spec_f64_fract(f: f64) -> f64;

pub assume_specification [ f64::fract ](f: f64) -> (res: f64)
    requires
        spec_f64_is_finite(f),
    ensures
        res == spec_f64_fract(f),
;

pub uninterp spec fn spec_f64_abs(f: f64) -> f64;

pub assume_specification [ f64::abs ](f: f64) -> (res: f64)
    requires
        spec_f64_is_finite(f),
    ensures
        res == spec_f64_abs(f),
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
