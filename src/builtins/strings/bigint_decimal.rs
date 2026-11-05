// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Decimal conversion used only while a global memory ceiling is active.
//!
//! num-bigint's Display allocates the entire decimal representation and opaque
//! divide-and-conquer workspace before a formatting writer can check the limit.
//! Here the only workspace is one binary-limb vector, and digits are appended
//! directly to the destination. Unlimited conversions keep num-bigint's faster
//! divide-and-conquer implementation.

use crate::number::BigInt;
use crate::utils::limits::{check_global_memory_limit, check_memory_allocation, reserve_string};
use crate::*;
use anyhow::Result;

pub(super) fn append(out: &mut String, value: &BigInt) -> Result<()> {
    let negative = value.sign() == num_bigint::Sign::Minus;
    // 30103/100000 is an upper bound for log10(2). u128 keeps this
    // multiplication safe even for the full u64 range of BigInt::bits().
    let digits = u128::from(value.bits()) * 30_103 / 100_000 + 1;
    let additional = usize::try_from(digits + u128::from(negative))?;
    reserve_string(out, additional)?;

    let limbs = value.iter_u32_digits();
    let bytes = limbs
        .len()
        .checked_mul(core::mem::size_of::<u32>())
        .ok_or_else(|| anyhow::anyhow!("sprintf BigInt workspace size overflow"))?;
    check_memory_allocation(bytes)?;
    let mut workspace = Vec::new();
    workspace.try_reserve_exact(limbs.len())?;
    workspace.extend(limbs);
    check_global_memory_limit()?;

    // Reuse the destination allocation; there is no decimal temporary or copy.
    let mut output = core::mem::take(out).into_bytes();
    if negative {
        output.push(b'-');
    }
    let start = output.len();
    loop {
        let mut remainder = 0u64;
        for limb in workspace.iter_mut().rev() {
            // remainder < 10^9, so this fits in u64 and the quotient in u32.
            let dividend = (remainder << 32) | u64::from(*limb);
            *limb = (dividend / 1_000_000_000) as u32;
            remainder = dividend % 1_000_000_000;
        }
        while workspace.last() == Some(&0) {
            workspace.pop();
        }
        // Every non-leading base-10^9 chunk needs nine digits, including zeroes.
        let count = if workspace.is_empty() {
            if remainder == 0 {
                1
            } else {
                remainder.ilog10() as usize + 1
            }
        } else {
            9
        };
        for _ in 0..count {
            output.push(b'0' + (remainder % 10) as u8);
            remainder /= 10;
        }
        if workspace.is_empty() {
            break;
        }
    }
    output[start..].reverse();
    // The existing UTF-8 prefix is untouched; only ASCII digits/sign were added.
    *out = String::from_utf8(output)?;
    check_global_memory_limit()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decimal_blocks_preserve_sign_zeroes_and_existing_utf8() {
        for decimal in [
            "0",
            "1",
            "-1",
            "4294967295",
            "4294967296",
            "999999999",
            "1000000000",
            "1000000001",
            "999999999999999999",
            "1000000000000000000",
            "1000000000000000001",
            "18446744073709551616",
            "-18446744073709551616",
            "1000000000000000000000000000000000001",
            "-1000000000000000000000000000000000001",
        ] {
            let number = BigInt::parse_bytes(decimal.as_bytes(), 10).unwrap();
            let mut output = "\u{03bb}:".to_string();
            append(&mut output, &number).unwrap();
            assert_eq!(output, format!("\u{03bb}:{decimal}"));
        }
    }

    #[test]
    fn decimal_conversion_matches_num_bigint_across_binary_boundaries() {
        for shift in [0, 31, 32, 63, 64, 127, 128, 255, 256, 1023, 4096] {
            for offset in [-1i32, 0, 1] {
                let number = (BigInt::from(1u32) << shift as usize) + offset;
                for number in [number.clone(), -number] {
                    let mut output = String::new();
                    append(&mut output, &number).unwrap();
                    assert_eq!(output, number.to_string());
                }
            }
        }
    }
}
