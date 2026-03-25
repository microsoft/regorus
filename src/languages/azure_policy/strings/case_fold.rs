// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Full Unicode case folding for Azure Policy string value comparisons.
//!
//! Azure Policy evaluates most condition operators (`equals`, `notEquals`,
//! `contains`, `like`, `in`, …) using .NET's `InvariantCultureIgnoreCase`.
//! Under .NET 5+ this is backed by ICU, performing *full* Unicode case folding:
//!
//! - ß → ss  (German sharp s)
//! - ﬃ → ffi (Latin ligatures)
//! - Σ/σ/ς → σ (Greek sigma variants)
//!
//! We use [`icu_casemap::CaseMapper`] with compiled data, which provides the
//! same ICU case folding tables that .NET uses internally.
//!
//! # Usage
//!
//! ```rust,ignore
//! use regorus::languages::azure_policy::strings::case_fold;
//!
//! // Equality
//! assert!(case_fold::eq("Straße", "STRASSE"));
//! assert!(case_fold::eq("hello", "HELLO"));
//!
//! // Ordering
//! assert_eq!(case_fold::cmp("alpha", "BETA"), std::cmp::Ordering::Less);
//!
//! // Folded form (for hashing, indexing, etc.)
//! let folded: std::borrow::Cow<str> = case_fold::fold("Straße");
//! assert_eq!(&*folded, "strasse");
//! ```

use alloc::borrow::Cow;
use core::cmp::Ordering;

use icu_casemap::CaseMapperBorrowed;

static CASE_MAPPER: CaseMapperBorrowed<'static> = CaseMapperBorrowed::new();

/// Return the full-case-folded form of `s`.
///
/// The result is a [`Cow::Borrowed`] when `s` is already in folded form
/// (common for ASCII lowercase), avoiding allocation.
///
/// This is the canonical form for case-insensitive hashing and indexing.
pub fn fold(s: &str) -> Cow<'_, str> {
    CASE_MAPPER.fold_string(s)
}

/// Case-insensitive equality using full Unicode case folding.
///
/// Equivalent to .NET `String.Equals(a, b, StringComparison.InvariantCultureIgnoreCase)`.
///
/// # Fast path
///
/// If both strings are plain ASCII, falls back to `eq_ignore_ascii_case`
/// which avoids allocation entirely.
pub fn eq(a: &str, b: &str) -> bool {
    // Fast path: ASCII-only strings are extremely common in Azure data.
    if a.is_ascii() && b.is_ascii() {
        return a.eq_ignore_ascii_case(b);
    }

    CASE_MAPPER.fold_string(a) == CASE_MAPPER.fold_string(b)
}

/// Case-insensitive ordering using full Unicode case folding.
///
/// Equivalent to .NET `String.Compare(a, b, StringComparison.InvariantCultureIgnoreCase)`.
///
/// # Note
///
/// This compares the *folded* UTF-8 byte sequences, which gives a stable
/// total order suitable for sorting and binary search, but is not the same
/// as a full locale-aware collation.  For Azure Policy's purposes (where
/// ordering is used by `greater`/`less` operators on string values) this is
/// sufficient.
pub fn cmp(a: &str, second: &str) -> Ordering {
    if a.is_ascii() && second.is_ascii() {
        // Compare char-by-char with ASCII folding, no allocation.
        let ord = a
            .bytes()
            .map(|byte| byte.to_ascii_lowercase())
            .cmp(second.bytes().map(|byte| byte.to_ascii_lowercase()));
        return ord;
    }

    let fa = CASE_MAPPER.fold_string(a);
    let fb = CASE_MAPPER.fold_string(second);
    fa.cmp(&fb)
}

/// Case-insensitive substring test using full Unicode case folding.
///
/// Returns `true` if the folded form of `haystack` contains the folded form
/// of `needle`.
///
/// Equivalent to the `contains` / `notContains` Azure Policy operators on
/// string values.
pub fn contains(haystack: &str, needle: &str) -> bool {
    if haystack.is_ascii() && needle.is_ascii() {
        // ASCII fast path: avoid allocation.
        // Note: This is O(n*m) but strings are typically short in policy data.
        let h = haystack.as_bytes();
        let n = needle.as_bytes();
        if n.is_empty() {
            return true;
        }
        if n.len() > h.len() {
            return false;
        }
        return h.windows(n.len()).any(|w| w.eq_ignore_ascii_case(n));
    }

    let fh = CASE_MAPPER.fold_string(haystack);
    let fn_ = CASE_MAPPER.fold_string(needle);
    fh.contains(&*fn_)
}

#[cfg(test)]
mod tests {
    use super::*;

    // ── eq ────────────────────────────────────────────────────────────

    #[test]
    fn eq_ascii_same_case() {
        assert!(eq("hello", "hello"));
    }

    #[test]
    fn eq_ascii_diff_case() {
        assert!(eq("Hello", "hELLO"));
    }

    #[test]
    fn eq_sharp_s() {
        // ß (U+00DF) folds to "ss"
        assert!(eq("Straße", "STRASSE"));
        assert!(eq("straße", "strasse"));
    }

    #[test]
    fn eq_greek_sigma() {
        // Σ, σ, ς all fold to σ
        assert!(eq("ΣΕΛΑΣ", "σελας"));
        assert!(eq("σελας", "σελας"));
    }

    #[test]
    fn eq_ligature() {
        // ﬃ (U+FB03) folds to "ffi"
        assert!(eq("ﬃ", "ffi"));
        assert!(eq("ﬃ", "FFI"));
    }

    #[test]
    fn eq_not_equal() {
        assert!(!eq("abc", "abd"));
        assert!(!eq("abc", "ab"));
    }

    #[test]
    fn eq_empty() {
        assert!(eq("", ""));
        assert!(!eq("", "a"));
    }

    // ── cmp ──────────────────────────────────────────────────────────

    #[test]
    fn cmp_equal() {
        assert_eq!(cmp("hello", "HELLO"), Ordering::Equal);
    }

    #[test]
    fn cmp_less() {
        assert_eq!(cmp("alpha", "BETA"), Ordering::Less);
    }

    #[test]
    fn cmp_greater() {
        assert_eq!(cmp("beta", "ALPHA"), Ordering::Greater);
    }

    // ── contains ─────────────────────────────────────────────────────

    #[test]
    fn contains_ascii() {
        assert!(contains("Hello World", "lo wo"));
    }

    #[test]
    fn contains_empty_needle() {
        assert!(contains("anything", ""));
    }

    #[test]
    fn contains_sharp_s() {
        assert!(contains("Die Straße ist lang", "STRASSE"));
    }

    #[test]
    fn contains_no_match() {
        assert!(!contains("hello", "xyz"));
    }

    // ── fold ─────────────────────────────────────────────────────────

    #[test]
    fn fold_ascii_lowercase_borrows() {
        let result = fold("hello");
        assert!(matches!(result, Cow::Borrowed(_)));
        assert_eq!(&*result, "hello");
    }

    #[test]
    fn fold_sharp_s() {
        let result = fold("Straße");
        assert_eq!(&*result, "strasse");
    }
}
