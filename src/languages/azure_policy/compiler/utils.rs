// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Free helper functions used by the Azure Policy compiler.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::languages::azure_policy::ast::{Expr, ExprLiteral, JsonValue, ObjectEntry};
use crate::Value;

/// Extract a string literal from an expression, or bail.
pub(super) fn extract_string_literal(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Literal {
            value: ExprLiteral::String(value),
            ..
        } => Ok(value.clone()),
        other => bail!("expected string literal argument, found {:?}", other),
    }
}

/// Byte span of a quoted subscript found by [`QuotedSubscripts::at`].
struct QuotedSubscript {
    /// Byte range of the key between the quotes.
    key: core::ops::Range<usize>,
    /// Byte offset just past the closing `]`.
    end: usize,
}

/// Recognizes quoted bracket subscripts (`['key']` / `["key"]`) in a field
/// path.
///
/// A subscript is quoted when the first non-whitespace character after `[`
/// is `'` or `"`.  The key then runs to the first matching quote that is
/// followed, after optional whitespace, by `]`.  There is no escaping, and
/// `[`, `]`, `.` and `[*]` inside the key are literal: `p['a][*].x[b']` is
/// the single key `a][*].x[b`.  A quote with no such closing quote does not
/// open a quoted subscript; the bracket is read as unquoted text instead
/// (count field paths reject it, see [`ensure_count_field_path`]).
/// Whitespace is skipped with [`char::is_whitespace`], as [`str::trim`] does.
///
/// Remembers which quote characters have no closing quote left in the path,
/// so scanning a whole path stays linear.
#[derive(Default)]
struct QuotedSubscripts {
    single_unclosed: bool,
    double_unclosed: bool,
}

impl QuotedSubscripts {
    /// If the `[` at byte offset `open` starts a quoted subscript, return its
    /// span.
    fn at(&mut self, path: &str, open: usize) -> Option<QuotedSubscript> {
        let body = path.get(open.checked_add(1)?..)?;
        let lead = body.trim_start();
        let quote = lead.chars().next().filter(|c| *c == '\'' || *c == '"')?;
        let unclosed = if quote == '\'' {
            &mut self.single_unclosed
        } else {
            &mut self.double_unclosed
        };
        if *unclosed {
            return None;
        }

        let key_start = path.len().saturating_sub(lead.len()).saturating_add(1);
        let mut search = key_start;
        while let Some(rel) = path.get(search..)?.find(quote) {
            let close = search.saturating_add(rel);
            let after = path.get(close.saturating_add(1)..)?.trim_start();
            if let Some(tail) = after.strip_prefix(']') {
                return Some(QuotedSubscript {
                    key: key_start..close,
                    end: path.len().saturating_sub(tail.len()),
                });
            }
            search = path.len().saturating_sub(after.len());
        }
        *unclosed = true;
        None
    }
}

/// Byte offset of the first unquoted `[*]` wildcard in a field path, or
/// `None` when the path has no wildcard.
///
/// A `[*]` inside a quoted subscript (`m['a[*]']`) is part of a literal key
/// and is skipped; see [`QuotedSubscripts`] for the quoting rule.  The
/// wildcard itself is matched exactly: `[ * ]` is not a wildcard.  Runs in
/// linear time.
pub(super) fn find_unquoted_wildcard(path: &str) -> Option<usize> {
    unquoted_wildcards(path).next()
}

/// Byte offsets of every unquoted `[*]` in a field path, in order, found in a
/// single linear scan (see [`find_unquoted_wildcard`]).
fn unquoted_wildcards(path: &str) -> impl Iterator<Item = usize> + '_ {
    let mut quoted = QuotedSubscripts::default();
    let mut pos = 0_usize;
    core::iter::from_fn(move || {
        while let Some(rel) = path.get(pos..)?.find('[') {
            let open = pos.saturating_add(rel);
            if path.get(open..)?.starts_with("[*]") {
                pos = open.saturating_add("[*]".len());
                return Some(open);
            }
            pos = quoted
                .at(path, open)
                .map_or_else(|| open.saturating_add(1), |q| q.end);
        }
        None
    })
}

/// Whether a field path contains an unquoted `[*]` wildcard
/// (see [`find_unquoted_wildcard`]).
pub(super) fn has_unquoted_wildcard(path: &str) -> bool {
    find_unquoted_wildcard(path).is_some()
}

/// Reject a field path with a bracket that opens a quote but never closes it
/// (e.g. `m['a` or `m['a].x`).
///
/// [`QuotedSubscripts`] reads such a bracket as unquoted text, so a later
/// `[*]` would count as a wildcard in one path and as part of a quoted key
/// in a longer path that closes the quote.  Rejecting it in count field
/// paths keeps the textual `prefix[*].` comparisons against count binding
/// prefixes sound.  Other field paths keep reading such a bracket as
/// unquoted text.
fn ensure_quotes_closed(path: &str) -> Result<()> {
    let mut quoted = QuotedSubscripts::default();
    let mut pos = 0_usize;
    while let Some(rel) = path.get(pos..).and_then(|rest| rest.find('[')) {
        let open = pos.saturating_add(rel);
        pos = match quoted.at(path, open) {
            Some(q) => q.end,
            None => {
                let body = path.get(open.saturating_add(1)..).unwrap_or_default();
                if body.trim_start().starts_with(['\'', '"']) {
                    bail!("unclosed quote in field path: {}", path);
                }
                open.saturating_add(1)
            }
        };
    }
    Ok(())
}

/// Check that a count field path selects array members: it must end with an
/// unquoted `[*]`, and every quote it opens must close.
///
/// Anything after the last unquoted `[*]` (`items[*].x`, or a quoted-only
/// key such as `items[*]['a[*]']`) would otherwise be ignored and the count
/// would silently count the elements of the array before it.  Count field
/// paths become count binding prefixes, so they must not contain an
/// unclosed quote (see [`ensure_quotes_closed`]).
pub(super) fn ensure_count_field_path(path: &str) -> Result<()> {
    ensure_quotes_closed(path)?;
    let tail = unquoted_wildcards(path)
        .last()
        .and_then(|last| path.get(last.saturating_add("[*]".len())..));
    match tail {
        Some(tail) if tail.trim().is_empty() => Ok(()),
        Some(_) => bail!(
            "count field must end with an unquoted [*] (an array alias): {}",
            path
        ),
        None => bail!("wildcard path must contain [*]: {}", path),
    }
}

/// Split a count field path at its first unquoted `[*]` wildcard into
/// `(prefix, optional_suffix)`.
pub(super) fn split_count_wildcard_path(path: &str) -> Result<(String, Option<String>)> {
    let wildcard_index = find_unquoted_wildcard(path)
        .ok_or_else(|| anyhow!("wildcard path must contain [*]: {}", path))?;

    let (prefix_str, rest) = path.split_at(wildcard_index);
    let prefix = prefix_str.trim_end_matches('.');
    if prefix.is_empty() {
        bail!(
            "wildcard path must have a non-empty prefix before [*]: {}",
            path
        );
    }
    let after_wildcard = rest.strip_prefix("[*]").ok_or_else(|| {
        anyhow!(
            "wildcard path could not be parsed after [*] split: {}",
            path
        )
    })?;
    let suffix_str = after_wildcard.trim_start_matches('.');
    let suffix = if suffix_str.is_empty() {
        None
    } else {
        Some(suffix_str.to_string())
    };

    Ok((prefix.to_string(), suffix))
}

/// One segment of a field path.
///
/// The distinction is decided while parsing because it exists only in the
/// source syntax: `tags['123']` names an object key and `ipRules[0]`
/// subscripts an array, yet both reduce to digits once quoting is stripped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum PathSegment {
    Key(String),
    Index(u64),
}

/// Split a dotted path (without `[*]` wildcards) into its component segments.
///
/// Handles bracket notation:
///   - `tags['key']` -> `[Key("tags"), Key("key")]`
///   - `tags['123']` -> `[Key("tags"), Key("123")]`
///   - `properties.ipRules[0].value` -> `[Key("properties"), Key("ipRules"), Index(0), Key("value")]`
///
/// Only a bare, unquoted, all-ASCII-digit subscript is an index. Dotted segments are
/// always keys because Azure Policy spells array access with brackets.
///
/// A quoted subscript is one literal key (see [`QuotedSubscripts`]), so
/// `m['a[*]']` and `m['a]b']` are accepted; only an unquoted `[*]` is
/// rejected as a wildcard.
pub(super) fn split_path_without_wildcards(path: &str) -> Result<Vec<PathSegment>> {
    if path.trim().is_empty() {
        bail!("empty path");
    }
    if has_unquoted_wildcard(path) {
        bail!(
            "wildcard field paths are not supported in this context: {}",
            path
        );
    }
    if path.ends_with('.') {
        bail!("path must not end with '.': {}", path);
    }

    let mut parts = Vec::new();
    let mut token = String::new();
    let mut bracket = String::new();
    let mut in_bracket = false;
    let mut after_bracket = false;
    let mut quoted = QuotedSubscripts::default();
    let mut pos = 0_usize;

    while let Some(ch) = path.get(pos..).and_then(|rest| rest.chars().next()) {
        let open = pos;
        pos = pos.saturating_add(ch.len_utf8());
        match ch {
            '.' if !in_bracket => {
                let t = token.trim();
                if t.is_empty() && !after_bracket {
                    bail!("empty segment in path: {}", path);
                }
                if !t.is_empty() {
                    parts.push(PathSegment::Key(t.to_string()));
                }
                token.clear();
                after_bracket = false;
            }
            '[' => {
                if in_bracket {
                    bail!("nested brackets in path: {}", path);
                }
                let t = token.trim();
                if !t.is_empty() {
                    parts.push(PathSegment::Key(t.to_string()));
                }
                token.clear();
                if let Some(q) = quoted.at(path, open) {
                    let key = path
                        .get(q.key)
                        .ok_or_else(|| anyhow!("invalid quoted key in path: {}", path))?;
                    if key.is_empty() {
                        bail!("empty quoted key in path: {}", path);
                    }
                    parts.push(PathSegment::Key(key.to_string()));
                    after_bracket = true;
                    pos = q.end;
                } else {
                    in_bracket = true;
                    after_bracket = false;
                }
            }
            ']' => {
                if !in_bracket {
                    bail!("unexpected closing bracket in path: {}", path);
                }
                in_bracket = false;
                after_bracket = true;
                let raw = bracket.trim();
                if raw.is_empty() {
                    bail!("empty bracket in path: {}", path);
                }
                let segment = if raw.bytes().all(|b| b.is_ascii_digit()) {
                    // Bare digits are always an index. One too large for u64
                    // saturates: it is out of range on any array and never
                    // matches an object key, rather than becoming a key.
                    PathSegment::Index(raw.parse::<u64>().unwrap_or(u64::MAX))
                } else {
                    PathSegment::Key(raw.to_string())
                };
                parts.push(segment);
                bracket.clear();
            }
            _ => {
                if in_bracket {
                    bracket.push(ch);
                } else {
                    if after_bracket {
                        bail!("expected '.' or '[' after bracket in path: {}", path);
                    }
                    token.push(ch);
                }
            }
        }
    }

    if in_bracket {
        bail!("unclosed bracket in path: {}", path);
    }

    let t = token.trim();
    if !t.is_empty() {
        parts.push(PathSegment::Key(t.to_string()));
    }

    Ok(parts)
}

/// Convert a parsed JSON value from the Azure Policy AST into a runtime [`Value`].
pub(super) fn json_value_to_runtime(value: &JsonValue) -> Result<Value> {
    match value {
        JsonValue::Null(_) => Ok(Value::Null),
        JsonValue::Bool(_, b) => Ok(Value::Bool(*b)),
        JsonValue::Number(_, raw) => {
            Value::from_numeric_string(raw).map_err(|_| anyhow!("invalid number literal: {}", raw))
        }
        JsonValue::Str(_, s) => {
            // Handle ARM template escape: `[[...` → `[...`
            s.strip_prefix("[[").map_or_else(
                || Ok(Value::from(s.clone())),
                |unescaped| Ok(Value::from(alloc::format!("[{unescaped}"))),
            )
        }
        JsonValue::Array(_, items) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                out.push(json_value_to_runtime(item)?);
            }
            Ok(Value::from(out))
        }
        JsonValue::Object(_, entries) => {
            let mut obj = Value::new_object();
            let map = obj.as_object_mut()?;
            for ObjectEntry {
                key,
                value: entry_value,
                ..
            } in entries
            {
                map.insert(
                    Value::from(key.clone()),
                    json_value_to_runtime(entry_value)?,
                );
            }
            Ok(obj)
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use alloc::vec;

    use crate::lexer::Source;

    use super::*;

    fn dummy_span() -> crate::lexer::Span {
        let source = Source::from_contents("test".into(), " ".into()).unwrap();
        crate::lexer::Span {
            source,
            line: 1,
            col: 1,
            start: 0,
            end: 0,
        }
    }

    // -----------------------------------------------------------------------
    // extract_string_literal
    // -----------------------------------------------------------------------

    #[test]
    fn extract_string_literal_ok() {
        let expr = Expr::Literal {
            span: dummy_span(),
            value: ExprLiteral::String("hello".into()),
        };
        assert_eq!(extract_string_literal(&expr).unwrap(), "hello");
    }

    #[test]
    fn extract_string_literal_number_err() {
        let expr = Expr::Literal {
            span: dummy_span(),
            value: ExprLiteral::Number("42".into()),
        };
        extract_string_literal(&expr).unwrap_err();
    }

    #[test]
    fn extract_string_literal_ident_err() {
        let expr = Expr::Ident {
            span: dummy_span(),
            name: "x".into(),
        };
        extract_string_literal(&expr).unwrap_err();
    }

    // -----------------------------------------------------------------------
    // json_value_to_runtime
    // -----------------------------------------------------------------------

    #[test]
    fn json_null() {
        let v = json_value_to_runtime(&JsonValue::Null(dummy_span())).unwrap();
        assert_eq!(v, Value::Null);
    }

    #[test]
    fn json_bool() {
        let v = json_value_to_runtime(&JsonValue::Bool(dummy_span(), true)).unwrap();
        assert_eq!(v, Value::Bool(true));
    }

    #[test]
    fn json_number_int() {
        let v = json_value_to_runtime(&JsonValue::Number(dummy_span(), "42".into())).unwrap();
        assert_eq!(v, Value::from(42_i64));
    }

    #[test]
    fn json_number_float() {
        let v = json_value_to_runtime(&JsonValue::Number(dummy_span(), "1.5".into())).unwrap();
        assert_eq!(v, Value::from(1.5_f64));
    }

    #[test]
    fn json_number_invalid() {
        json_value_to_runtime(&JsonValue::Number(dummy_span(), "abc".into())).unwrap_err();
    }

    #[test]
    fn json_string() {
        let v = json_value_to_runtime(&JsonValue::Str(dummy_span(), "hello".into())).unwrap();
        assert_eq!(v, Value::from("hello".to_string()));
    }

    #[test]
    fn json_string_double_bracket_escape() {
        let v = json_value_to_runtime(&JsonValue::Str(dummy_span(), "[[escaped]".into())).unwrap();
        assert_eq!(v, Value::from("[escaped]".to_string()));
    }

    #[test]
    fn json_array() {
        let arr = JsonValue::Array(
            dummy_span(),
            vec![
                JsonValue::Bool(dummy_span(), true),
                JsonValue::Null(dummy_span()),
            ],
        );
        let v = json_value_to_runtime(&arr).unwrap();
        let items = v.as_array().unwrap();
        assert_eq!(items.len(), 2);
    }

    #[test]
    fn json_object() {
        let obj = JsonValue::Object(
            dummy_span(),
            vec![ObjectEntry {
                key_span: dummy_span(),
                key: "k".into(),
                value: JsonValue::Bool(dummy_span(), false),
            }],
        );
        let v = json_value_to_runtime(&obj).unwrap();
        let map = v.as_object().unwrap();
        assert_eq!(map.len(), 1);
    }

    // -----------------------------------------------------------------------
    // find_unquoted_wildcard
    // -----------------------------------------------------------------------

    #[test]
    fn find_wildcard_unquoted() {
        assert_eq!(find_unquoted_wildcard("a[*]"), Some(1));
        assert_eq!(find_unquoted_wildcard("a.b[*].c[*]"), Some(3));
        assert_eq!(find_unquoted_wildcard("[*]"), Some(0));
        assert_eq!(find_unquoted_wildcard("a[0].b['c'][*]"), Some(11));
        assert_eq!(find_unquoted_wildcard("a.b"), None);
        assert_eq!(find_unquoted_wildcard(""), None);
    }

    #[test]
    fn find_wildcard_skips_quoted_keys() {
        assert_eq!(find_unquoted_wildcard("m['a[*]']"), None);
        assert_eq!(find_unquoted_wildcard("m[\"a[*]\"]"), None);
        assert_eq!(find_unquoted_wildcard("m[ 'a[*]' ].b"), None);
        assert_eq!(find_unquoted_wildcard("m[\t\"a[*]\"\n]"), None);
        assert_eq!(find_unquoted_wildcard("items[*]['a[*]']"), Some(5));
        assert_eq!(find_unquoted_wildcard("m['a[*]'][*]"), Some(9));
        assert_eq!(find_unquoted_wildcard("m['a[*]'].b[*]"), Some(11));
    }

    #[test]
    fn find_wildcard_twin_without_quotes_matches() {
        // Non-quoted twins of the quoted cases above.
        assert_eq!(find_unquoted_wildcard("m[a[*]]"), Some(3));
        assert_eq!(find_unquoted_wildcard("m.a[*]"), Some(3));
    }

    #[test]
    fn find_wildcard_close_bracket_inside_quotes() {
        assert_eq!(find_unquoted_wildcard("m['a]'][*]"), Some(7));
        assert_eq!(find_unquoted_wildcard("m['a]b'].c"), None);
        assert_eq!(find_unquoted_wildcard("m['a]'].x[*]"), Some(9));
    }

    #[test]
    fn find_wildcard_quoted_key_runs_to_quote_before_close_bracket() {
        // Pinned rule: the quote opened after `[` runs to the matching quote
        // that is followed by `]`, so this is one key with no wildcard.
        assert_eq!(find_unquoted_wildcard("p['a][*].x[b']"), None);
        // Twin: without the closing quote the `[*]` is unquoted.
        assert_eq!(find_unquoted_wildcard("p['a][*].x[b]"), Some(5));
    }

    #[test]
    fn find_wildcard_quote_kinds_do_not_mix() {
        assert_eq!(find_unquoted_wildcard("m[\"a'][*]'\"]"), None);
        assert_eq!(find_unquoted_wildcard("m['a\"][*]\"']"), None);
        assert_eq!(find_unquoted_wildcard("m[\"a'][*]"), Some(6));
    }

    #[test]
    fn find_wildcard_unterminated_quote_is_unquoted() {
        assert_eq!(find_unquoted_wildcard("m['a[*]"), Some(4));
        assert_eq!(find_unquoted_wildcard("m['a'x[*]"), Some(6));
        // A failed quote does not hide a later, well-formed quoted key.
        assert_eq!(find_unquoted_wildcard("m[\"a].n['b[*]']"), None);
    }

    #[test]
    fn find_wildcard_quote_must_open_the_subscript() {
        assert_eq!(find_unquoted_wildcard("m[x'[*]']"), Some(4));
        assert_eq!(find_unquoted_wildcard("a'[*]'"), Some(2));
    }

    #[test]
    fn find_wildcard_requires_exact_token() {
        assert_eq!(find_unquoted_wildcard("a[ * ]"), None);
        assert_eq!(find_unquoted_wildcard("a[**]"), None);
        assert_eq!(find_unquoted_wildcard("a[*"), None);
    }

    #[test]
    fn find_wildcard_non_ascii() {
        assert_eq!(find_unquoted_wildcard("é['ü[*]'][*]"), Some(11));
        assert_eq!(find_unquoted_wildcard("é['ü[*]']"), None);
    }

    #[test]
    fn find_wildcard_is_linear_on_unclosed_quotes() {
        // Each `['` would rescan the rest of the path without memoization.
        let single = "['".repeat(50_000) + "[*]";
        assert_eq!(find_unquoted_wildcard(&single), Some(100_000));
        let double = "[\"x']".repeat(50_000);
        assert_eq!(find_unquoted_wildcard(&double), None);
        split_path_without_wildcards(&alloc::format!("m{}", "['a]".repeat(50_000))).unwrap();
    }

    #[test]
    fn unquoted_wildcards_lists_every_wildcard_linearly() {
        assert_eq!(
            unquoted_wildcards("a[*].b['c[*]'][*]").collect::<Vec<_>>(),
            vec![1, 14]
        );
        let many = "['".repeat(50_000) + "[*]";
        assert_eq!(unquoted_wildcards(&many).last(), Some(100_000));
    }

    #[test]
    fn count_field_path_must_end_with_unquoted_wildcard() {
        for ok in [
            "items[*]",
            "a[*].b[*]",
            "m['a[*]'][*]",
            "items[*] ",
            "items[*]['k'][*]",
        ] {
            ensure_count_field_path(ok).unwrap();
        }
        for bad in ["items[*]['a[*]']", "items[*].x", "items[*].", "a[*].b[*].c"] {
            let err = ensure_count_field_path(bad).unwrap_err();
            assert!(
                err.to_string().contains("must end with an unquoted [*]"),
                "{bad}: {err}"
            );
        }
        for bad in ["m['a[*]']", "items"] {
            let err = ensure_count_field_path(bad).unwrap_err();
            assert!(err.to_string().contains("must contain [*]"), "{bad}: {err}");
        }
    }

    #[test]
    fn count_field_path_rejects_unclosed_quote() {
        // Without the check, `m['a].x` would be the binding prefix while the
        // longer `m['a].x[*].y['b']` reads as one quoted key with no wildcard.
        for bad in ["m['a].x[*]", "m[ \"a].x[*]", "m[*].x['b[*]"] {
            let err = ensure_count_field_path(bad).unwrap_err();
            assert!(err.to_string().contains("unclosed quote"), "{bad}: {err}");
        }
        ensure_count_field_path("m['a]'].x[*]").unwrap();
        // An apparent opener inside a closed quoted key is part of the key.
        ensure_count_field_path("m['x[\"y'][*]").unwrap();
        // A quote that does not open the bracket body is plain text.
        ensure_count_field_path("m[a'b][*]").unwrap();
        // Field paths outside counts keep reading the bracket as unquoted.
        split_count_wildcard_path("m['a].x[*]").unwrap();
    }

    #[test]
    fn has_wildcard_matches_finder() {
        assert!(has_unquoted_wildcard("items[*]['a[*]']"));
        assert!(!has_unquoted_wildcard("items['a[*]']"));
    }

    // -----------------------------------------------------------------------
    // split_count_wildcard_path
    // -----------------------------------------------------------------------

    #[test]
    fn wildcard_simple() {
        let (prefix, suffix) = split_count_wildcard_path("a.b[*].c").unwrap();
        assert_eq!(prefix, "a.b");
        assert_eq!(suffix.as_deref(), Some("c"));
    }

    #[test]
    fn wildcard_no_suffix() {
        let (prefix, suffix) = split_count_wildcard_path("a[*]").unwrap();
        assert_eq!(prefix, "a");
        assert_eq!(suffix, None);
    }

    #[test]
    fn wildcard_trailing_dot_prefix() {
        let (prefix, _) = split_count_wildcard_path("a.[*].c").unwrap();
        assert_eq!(prefix, "a");
    }

    #[test]
    fn wildcard_missing() {
        split_count_wildcard_path("a.b.c").unwrap_err();
    }

    #[test]
    fn wildcard_empty_prefix() {
        split_count_wildcard_path("[*].c").unwrap_err();
    }

    #[test]
    fn wildcard_nested() {
        let (prefix, suffix) = split_count_wildcard_path("a[*].b[*].c").unwrap();
        assert_eq!(prefix, "a");
        assert_eq!(suffix.as_deref(), Some("b[*].c"));
    }

    #[test]
    fn wildcard_quoted_key_after_wildcard_is_suffix() {
        let (prefix, suffix) = split_count_wildcard_path("items[*]['a[*]']").unwrap();
        assert_eq!(prefix, "items");
        assert_eq!(suffix.as_deref(), Some("['a[*]']"));
    }

    #[test]
    fn wildcard_quoted_key_before_wildcard_is_prefix() {
        let (prefix, suffix) = split_count_wildcard_path("m['a[*]'][*].x").unwrap();
        assert_eq!(prefix, "m['a[*]']");
        assert_eq!(suffix.as_deref(), Some("x"));
        let (dq_prefix, dq_suffix) = split_count_wildcard_path("m[\"a]\"][*]").unwrap();
        assert_eq!(dq_prefix, "m[\"a]\"]");
        assert_eq!(dq_suffix, None);
    }

    #[test]
    fn wildcard_only_quoted_is_missing() {
        split_count_wildcard_path("m['a[*]']").unwrap_err();
        split_count_wildcard_path("p['a][*].x[b']").unwrap_err();
    }

    // -----------------------------------------------------------------------
    // split_path_without_wildcards
    // -----------------------------------------------------------------------

    fn key(name: &str) -> PathSegment {
        PathSegment::Key(name.to_string())
    }

    #[test]
    fn path_simple_dotted() {
        assert_eq!(
            split_path_without_wildcards("a.b.c").unwrap(),
            vec![key("a"), key("b"), key("c")]
        );
    }

    #[test]
    fn path_bracket_quoted() {
        assert_eq!(
            split_path_without_wildcards("tags['key']").unwrap(),
            vec![key("tags"), key("key")]
        );
    }

    #[test]
    fn path_bracket_numeric() {
        assert_eq!(
            split_path_without_wildcards("a[0].b").unwrap(),
            vec![key("a"), PathSegment::Index(0), key("b")]
        );
    }

    #[test]
    fn path_bracket_quoted_digits_is_a_key() {
        assert_eq!(
            split_path_without_wildcards("tags['123']").unwrap(),
            vec![key("tags"), key("123")]
        );
        assert_eq!(
            split_path_without_wildcards("tags[\"123\"]").unwrap(),
            vec![key("tags"), key("123")]
        );
    }

    #[test]
    fn path_empty_quoted_key_is_an_error() {
        for path in ["a['']", "a[\"\"]", "a[ '' ]"] {
            let err = split_path_without_wildcards(path).unwrap_err().to_string();
            assert!(err.contains("empty quoted key in path"), "{path}: {err}");
        }
        let err = split_path_without_wildcards("a[]").unwrap_err().to_string();
        assert!(err.contains("empty bracket in path"), "{err}");
    }

    #[test]
    fn path_bracket_preserves_quotes_inside_delimiters() {
        assert_eq!(
            split_path_without_wildcards("properties.config[\"'123'\"]").unwrap(),
            vec![key("properties"), key("config"), key("'123'")]
        );
        assert_eq!(
            split_path_without_wildcards("properties.config['\"123\"']").unwrap(),
            vec![key("properties"), key("config"), key("\"123\"")]
        );
    }

    #[test]
    fn path_bracket_preserves_mismatched_quotes() {
        assert_eq!(
            split_path_without_wildcards("properties.config[\"123']").unwrap(),
            vec![key("properties"), key("config"), key("\"123'")]
        );
        assert_eq!(
            split_path_without_wildcards("properties.config['123\"]").unwrap(),
            vec![key("properties"), key("config"), key("'123\"")]
        );
    }

    #[test]
    fn path_dotted_digits_is_a_key() {
        assert_eq!(
            split_path_without_wildcards("tags.123").unwrap(),
            vec![key("tags"), key("123")]
        );
    }

    #[test]
    fn path_single_segment() {
        assert_eq!(
            split_path_without_wildcards("name").unwrap(),
            vec![key("name")]
        );
    }

    #[test]
    fn path_empty() {
        split_path_without_wildcards("").unwrap_err();
    }

    #[test]
    fn path_whitespace_only() {
        split_path_without_wildcards("   ").unwrap_err();
    }

    #[test]
    fn path_trailing_dot() {
        split_path_without_wildcards("a.").unwrap_err();
    }

    #[test]
    fn path_leading_dot() {
        split_path_without_wildcards(".a").unwrap_err();
    }

    #[test]
    fn path_consecutive_dots() {
        split_path_without_wildcards("a..b").unwrap_err();
    }

    #[test]
    fn path_wildcard_rejected() {
        split_path_without_wildcards("a[*].b").unwrap_err();
    }

    #[test]
    fn path_quoted_wildcard_is_key() {
        assert_eq!(
            split_path_without_wildcards("m['a[*]']").unwrap(),
            vec![key("m"), key("a[*]")]
        );
        assert_eq!(
            split_path_without_wildcards("m[ \"a[*]\" ].b").unwrap(),
            vec![key("m"), key("a[*]"), key("b")]
        );
    }

    #[test]
    fn path_quoted_close_bracket_is_key() {
        assert_eq!(
            split_path_without_wildcards("m['a]b'].c").unwrap(),
            vec![key("m"), key("a]b"), key("c")]
        );
        assert_eq!(
            split_path_without_wildcards("m['a.b'][0]").unwrap(),
            vec![key("m"), key("a.b"), PathSegment::Index(0)]
        );
    }

    #[test]
    fn path_quoted_key_runs_to_quote_before_close_bracket() {
        // Pinned rule: one key, no wildcard.
        assert_eq!(
            split_path_without_wildcards("p['a][*].x[b']").unwrap(),
            vec![key("p"), key("a][*].x[b")]
        );
        assert_eq!(
            split_path_without_wildcards("m['it's']").unwrap(),
            vec![key("m"), key("it's")]
        );
    }

    #[test]
    fn path_quoted_key_with_unquoted_wildcard_rejected() {
        split_path_without_wildcards("m['a[*]'][*]").unwrap_err();
        split_path_without_wildcards("m['a]'][*]").unwrap_err();
    }

    #[test]
    fn path_unterminated_quote_is_unquoted() {
        assert_eq!(
            split_path_without_wildcards("m['a]").unwrap(),
            vec![key("m"), key("'a")]
        );
        split_path_without_wildcards("m['a[*]").unwrap_err();
        split_path_without_wildcards("m['a[0]").unwrap_err();
    }

    #[test]
    fn path_spaced_star_is_a_key_not_a_wildcard() {
        assert_eq!(
            split_path_without_wildcards("a[ * ]").unwrap(),
            vec![key("a"), key("*")]
        );
    }

    #[test]
    fn path_nested_brackets() {
        split_path_without_wildcards("a[[0]]").unwrap_err();
    }

    #[test]
    fn path_stray_close_bracket() {
        split_path_without_wildcards("a]b").unwrap_err();
    }

    #[test]
    fn path_unclosed_bracket() {
        split_path_without_wildcards("a[0").unwrap_err();
    }

    #[test]
    fn path_empty_bracket() {
        split_path_without_wildcards("a[]").unwrap_err();
    }

    #[test]
    fn path_empty_quoted_bracket() {
        split_path_without_wildcards("a['']").unwrap_err();
        split_path_without_wildcards("a[\"\"]").unwrap_err();
    }

    #[test]
    fn path_lone_quote_is_a_literal_key() {
        assert_eq!(
            split_path_without_wildcards("a[']").unwrap(),
            vec![key("a"), key("'")]
        );
        assert_eq!(
            split_path_without_wildcards("a[\"]").unwrap(),
            vec![key("a"), key("\"")]
        );
    }

    #[test]
    fn path_signed_subscript_is_a_key() {
        assert_eq!(
            split_path_without_wildcards("a[+1]").unwrap(),
            vec![key("a"), key("+1")]
        );
        assert_eq!(
            split_path_without_wildcards("a[-1]").unwrap(),
            vec![key("a"), key("-1")]
        );
    }

    #[test]
    fn path_leading_zero_subscript_is_an_index() {
        assert_eq!(
            split_path_without_wildcards("a[007]").unwrap(),
            vec![key("a"), PathSegment::Index(7)]
        );
    }

    #[test]
    fn path_overflowing_digit_subscript_stays_an_index() {
        assert_eq!(
            split_path_without_wildcards("a[18446744073709551616]").unwrap(),
            vec![key("a"), PathSegment::Index(u64::MAX)]
        );
        assert_eq!(
            split_path_without_wildcards("a['18446744073709551616']").unwrap(),
            vec![key("a"), key("18446744073709551616")]
        );
    }

    #[test]
    fn path_bracket_whitespace_is_trimmed() {
        assert_eq!(
            split_path_without_wildcards("a[ '1' ]").unwrap(),
            vec![key("a"), key("1")]
        );
        assert_eq!(
            split_path_without_wildcards("a[ 1 ]").unwrap(),
            vec![key("a"), PathSegment::Index(1)]
        );
    }

    #[test]
    fn path_char_after_bracket_without_separator() {
        split_path_without_wildcards("a[0]b").unwrap_err();
    }
}
