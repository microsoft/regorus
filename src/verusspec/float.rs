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
