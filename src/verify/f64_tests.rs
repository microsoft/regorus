// This file contains executable tests that justify the assumptions about `f64`
// declared in `f64_assumptions.rs`.
//
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::as_conversions,
    clippy::unseparated_literal_suffix
)]

use crate::number::Number;
use core::cmp::Ordering;
use num_bigint::BigInt;

fn decode(f: f64) -> (u64, i32) {
    let bits = f.to_bits() & 0x7fff_ffff_ffff_ffff;
    let exponent = (bits >> 52) as i32;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    if exponent == 0 {
        (fraction, -1074)
    } else {
        (fraction + (1u64 << 52), exponent - 1075)
    }
}

fn scaled_value(f: f64, exponent: i32) -> BigInt {
    let (significand, decoded_exponent) = decode(f);
    let shift = decoded_exponent - exponent;
    let magnitude = if shift >= 0 {
        BigInt::from(significand) << shift as usize
    } else {
        BigInt::from(significand) >> (-shift) as usize
    };
    if f.is_sign_negative() {
        -magnitude
    } else {
        magnitude
    }
}

#[test]
fn f64_scaled_coarse_values_truncate_toward_zero() {
    for (f, exponent, expected) in [
        (1.5, 0, 1),
        (-1.5, 0, -1),
        (0.5, 0, 0),
        (-0.5, 0, 0),
        (3.5, 1, 1),
        (-3.5, 1, -1),
        (f64::from_bits(1), -1074, 1),
        (f64::from_bits(1), -1073, 0),
        (0.0, 1024, 0),
        (-0.0, 1024, 0),
    ] {
        assert_eq!(scaled_value(f, exponent), BigInt::from(expected));
    }
}

#[test]
fn f64_safe_integer_casts_match_runtime() {
    let safe_integer = 9_007_199_254_740_992.0f64;

    assert_eq!(safe_integer as u64, 9_007_199_254_740_992u64);
    assert_eq!(safe_integer as i128, 9_007_199_254_740_992i128);
}

#[test]
fn f64_scaled_order_and_u64_casts_match_runtime() {
    let upper = u64::MAX as f64;
    let zero = BigInt::from(0u8);
    let comparisons = [
        -f64::MAX,
        -1.0,
        -0.0,
        f64::from_bits(1),
        0.5,
        1.0,
        4_503_599_627_370_496.0,
        9_007_199_254_740_992.0,
        upper,
        f64::MAX,
    ];

    for exponent_bits in 0u64..=0x7ff {
        for fraction in [
            0u64,
            1,
            0x0008_0000_0000_0000,
            0x000f_ffff_ffff_fffe,
            0x000f_ffff_ffff_ffff,
        ] {
            for sign in [0u64, 1u64 << 63] {
                let f = f64::from_bits(sign | (exponent_bits << 52) | fraction);
                let exponent = decode(f).1.min(0);
                let value = scaled_value(f, exponent);
                assert_eq!(
                    f < 0.0,
                    !f.is_nan()
                        && if f.is_finite() {
                            value < zero
                        } else {
                            f.is_sign_negative()
                        }
                );
                if !f.is_finite() {
                    continue;
                }
                if exponent_bits < 1023 {
                    assert_eq!(f as u64, 0);
                }
                let integer_part = scaled_value(f, 0);
                if exponent_bits >= 1023
                    && integer_part >= zero
                    && integer_part <= BigInt::from(u64::MAX)
                {
                    assert_eq!(BigInt::from(f as u64), integer_part);
                }

                for g in comparisons {
                    let common = exponent.min(decode(g).1);
                    let lhs = scaled_value(f, common);
                    let rhs = scaled_value(g, common);
                    assert_eq!(f < g, lhs < rhs);
                    assert_eq!(f > g, lhs > rhs);
                    assert_eq!(f >= g, lhs >= rhs);
                }

                let unit = BigInt::from(1u8) << (-exponent) as usize;
                let upper_value = (BigInt::from(u64::MAX) + 1u8) * &unit;
                assert_eq!(scaled_value(upper, exponent), upper_value);
                if value >= zero && value < upper_value {
                    let truncated = f as u64;
                    let back = truncated as f64;
                    let floor = BigInt::from(truncated) * &unit;
                    assert!(floor <= value && value < &floor + &unit);
                    assert_eq!(BigInt::from(truncated), integer_part);
                    assert!(back.is_finite());
                    assert_eq!(scaled_value(back, exponent), floor);
                    let (significand, decoded_exponent) = decode(f);
                    let has_fraction = decoded_exponent < 0
                        && BigInt::from(significand)
                            % (BigInt::from(1u8) << (-decoded_exponent) as usize)
                            != zero;
                    assert_eq!(f > back, has_fraction);
                }
            }
        }
    }
}

#[test]
fn f64_scaled_order_and_i64_casts_match_runtime() {
    let lower = i64::MIN as f64;
    let upper = i64::MAX as f64;
    let zero = BigInt::from(0u8);
    let min = BigInt::from(i64::MIN);
    let max = BigInt::from(i64::MAX);
    for (bound, negative) in [(lower, true), (upper, false)] {
        assert!(bound.is_finite());
        assert_eq!(bound.is_sign_negative(), negative);
        assert_eq!((bound.to_bits() & 0x7fff_ffff_ffff_ffff) >> 52, 1086);
        assert_eq!(bound.to_bits() & 0x000f_ffff_ffff_ffff, 0);
    }
    assert_eq!(scaled_value(lower, 0), min);
    assert_eq!(scaled_value(upper, 0), &max + 1u8);

    for exponent_bits in 0u64..=0x7ff {
        for fraction in [
            0u64,
            1,
            0x0008_0000_0000_0000,
            0x000f_ffff_ffff_fffe,
            0x000f_ffff_ffff_ffff,
        ] {
            for sign in [0u64, 1u64 << 63] {
                let f = f64::from_bits(sign | (exponent_bits << 52) | fraction);
                let exponent = decode(f).1.min(0);
                let value = scaled_value(f, exponent);
                let unit = BigInt::from(1u8) << (-exponent) as usize;
                for n in [
                    i64::MIN,
                    i64::MIN + 1,
                    -9_007_199_254_740_993,
                    -1,
                    0,
                    1,
                    9_007_199_254_740_993,
                    i64::MAX - 1,
                    i64::MAX,
                ] {
                    let expected = if f.is_nan() {
                        Ordering::Greater
                    } else if !f.is_finite() {
                        if f.is_sign_negative() {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        }
                    } else {
                        value.cmp(&(BigInt::from(n) * &unit))
                    };
                    assert_eq!(
                        Number::Float(f).cmp(&Number::Int(n)),
                        expected,
                        "{f:?} vs {n}"
                    );
                }
                if !f.is_finite() {
                    continue;
                }
                if exponent_bits < 1023 {
                    assert_eq!(f as i64, 0);
                }
                let integer_part = scaled_value(f, 0);
                if integer_part < min || integer_part > max {
                    continue;
                }
                let truncated = f as i64;
                let back = truncated as f64;
                let integer_value = BigInt::from(truncated) * &unit;
                assert_eq!(BigInt::from(truncated), integer_part);
                assert!(back.is_finite());
                assert_eq!(scaled_value(back, exponent), integer_value);
                if value >= zero {
                    assert!(integer_value <= value && value < &integer_value + &unit);
                } else {
                    assert!(&integer_value - &unit < value && value <= integer_value);
                }
                let (significand, decoded_exponent) = decode(f);
                let has_fraction = decoded_exponent < 0
                    && BigInt::from(significand)
                        % (BigInt::from(1u8) << (-decoded_exponent) as usize)
                        != zero;
                assert_eq!(f < back, f.is_sign_negative() && has_fraction);
                assert_eq!(f > back, !f.is_sign_negative() && has_fraction);
            }
        }
    }
}
