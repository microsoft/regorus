// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ASCII case-insensitive comparison for ARM object property keys.
//!
//! ARM resource property names are restricted to ASCII letters, digits, and
//! underscores.  Key lookup in normalized ARM objects therefore only needs
//! `OrdinalIgnoreCase` semantics (fold A-Z → a-z, nothing else).
//!
//! This module wraps `eq_ignore_ascii_case` and provides an ASCII-only
//! case-insensitive ordering, both zero-allocation and branchless on modern
//! hardware.
//!
//! # Usage
//!
//! ```rust,ignore
//! use regorus::languages::azure_policy::strings::keys;
//!
//! assert!(keys::eq("Location", "location"));
//! assert_eq!(keys::cmp("Name", "name"), std::cmp::Ordering::Equal);
//! ```

use core::cmp::Ordering;

/// ASCII case-insensitive equality for ARM property keys.
///
/// This is a thin wrapper around [`str::eq_ignore_ascii_case`], made explicit
/// to document the `OrdinalIgnoreCase` semantics and keep call sites readable.
#[inline]
pub const fn eq(a: &str, b: &str) -> bool {
    a.eq_ignore_ascii_case(b)
}

/// ASCII case-insensitive ordering for ARM property keys.
///
/// Compares byte-by-byte after folding each byte with
/// [`u8::to_ascii_lowercase`].  This gives a stable total order consistent
/// with [`eq`].
#[inline]
pub fn cmp(a: &str, second: &str) -> Ordering {
    a.bytes()
        .map(|byte| byte.to_ascii_lowercase())
        .cmp(second.bytes().map(|byte| byte.to_ascii_lowercase()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eq_same() {
        assert!(eq("location", "location"));
    }

    #[test]
    fn eq_diff_case() {
        assert!(eq("Location", "LOCATION"));
        assert!(eq("apiVersion", "APIversion"));
    }

    #[test]
    fn eq_not_equal() {
        assert!(!eq("name", "type"));
    }

    #[test]
    fn eq_empty() {
        assert!(eq("", ""));
        assert!(!eq("", "a"));
    }

    #[test]
    fn cmp_equal() {
        assert_eq!(cmp("Location", "location"), Ordering::Equal);
    }

    #[test]
    fn cmp_less() {
        assert_eq!(cmp("apiVersion", "Name"), Ordering::Less);
    }

    #[test]
    fn cmp_greater() {
        assert_eq!(cmp("type", "Name"), Ordering::Greater);
    }
}
