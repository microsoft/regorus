//! Checked `u64` shifts with verified bodies, used where `u64::checked_shl`/`checked_shr`
//! would otherwise need an assumed specification (the pinned vstd specifies neither).

use vstd::prelude::*;

/// `value << shift`, or `None` when `shift` is at least 64, like `u64::checked_shl`.
#[verus_verify]
#[verus_spec(result => ensures result == if shift < 64 { Some(value << shift) } else { None })]
pub fn checked_shl(value: u64, shift: u32) -> Option<u64> {
    if shift < 64 {
        Some(value << shift)
    } else {
        None
    }
}

/// `value >> shift`, or `None` when `shift` is at least 64, like `u64::checked_shr`.
#[verus_verify]
#[verus_spec(result => ensures result == if shift < 64 { Some(value >> shift) } else { None })]
pub fn checked_shr(value: u64, shift: u32) -> Option<u64> {
    if shift < 64 {
        Some(value >> shift)
    } else {
        None
    }
}
