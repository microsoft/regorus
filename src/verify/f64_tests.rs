// This file contains executable tests that justify the assumptions about `f64`
// declared in `f64_assumptions.rs`.
//
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::as_conversions, clippy::unseparated_literal_suffix)]

#[test]
fn f64_safe_integer_casts_match_runtime() {
    let safe_integer = 9_007_199_254_740_992.0f64;

    assert_eq!(safe_integer as u64, 9_007_199_254_740_992u64);
    assert_eq!(safe_integer as i128, 9_007_199_254_740_992i128);
}
