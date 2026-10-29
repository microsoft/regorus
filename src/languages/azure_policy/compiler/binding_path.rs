// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Segment-wise matching of field paths against `count` binding prefixes.
//!
//! A count over `items[*]` binds `items[*].state`, `items[*]['state']`,
//! `items[*][0]` and `items[*]['subs'][*]` to its current element.  Paths
//! are compared as parsed segments rather than raw strings, so dotted and
//! quoted-bracket spellings of the same path (`a.b[*]` / `a['b'][*]`) are
//! equal, while a quoted key is always one literal segment: `m['a.b']` is
//! not `m.a.b`, and the quoted `[*]` in `m['a[*]']` is not a wildcard.
//!
//! [`match_count_prefix`] is the single entry point used by every binding
//! site in the compiler.

use alloc::string::String;
use alloc::vec::Vec;

use anyhow::{anyhow, Result};

use super::utils::PathSegment;

/// One parsed segment of a field path, for binding comparison only.
///
/// Keys are ASCII-lowercased, matching the case-insensitive lookup used for
/// normalized resource keys.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Segment {
    Key(String),
    Index(u64),
    Wildcard,
}

#[derive(Debug)]
struct ParsedSegment {
    segment: Segment,
    /// Byte offset in the source path where this segment's spelling starts
    /// (the key's first character, or the opening `[`).
    start: usize,
}

/// How a field path relates to a count binding's wildcard prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum CountPrefixMatch<'a> {
    /// The path is the prefix itself or `prefix[*]`: the current element.
    CurrentElement,
    /// The path continues below the current element.
    BelowElement {
        /// The remaining path relative to the current element, sliced from the
        /// original spelling (e.g. `state`, `['state']`, `[0]`,
        /// `['subs'][*]`).
        rest: &'a str,
        /// Whether `rest` contains an unquoted `[*]`.
        rest_has_wildcard: bool,
        /// Whether the path reached `rest` through the counted `[*]`
        /// (`prefix[*]…`) rather than the legacy `prefix.…` form.
        via_wildcard: bool,
    },
}

/// Match `field_path` against a count binding's wildcard `prefix`.
///
/// Returns `None` when the path does not select from the binding's current
/// element, including when either path fails to parse.  Recognized shapes:
///
/// - the exact legacy `prefix`, or an equivalent `prefix[*]` →
///   [`CountPrefixMatch::CurrentElement`];
/// - `prefix[*]<rest>` where `rest` starts with a key or an index;
/// - the exact legacy `prefix.<key>…` form without `[*]`.
///
/// Segment equivalence applies only when the counted wildcard is present.
/// Bare prefixes and no-wildcard suffixes retain their legacy raw spelling.
///
/// An index straight after the prefix (`prefix[0]`) names a fixed member of
/// the array, not the current element, and is left unbound; the legacy dotted
/// spelling `prefix.[0]` does bind and indexes the current element.  A second
/// consecutive wildcard (`prefix[*][*]`) is also left unbound, because the
/// downstream collectors cannot yet navigate it from an element.
pub(super) fn match_count_prefix<'a>(
    prefix: &str,
    field_path: &'a str,
) -> Option<CountPrefixMatch<'a>> {
    let prefix_segments = parse_binding_path(prefix)?;
    let field_segments = parse_binding_path(field_path)?;

    let head = field_segments.get(..prefix_segments.len())?;
    let mut rest = field_segments.get(prefix_segments.len()..)?;
    if !head
        .iter()
        .zip(prefix_segments.iter())
        .all(|(a, b)| a.segment == b.segment)
    {
        return None;
    }

    let via_wildcard = matches!(
        rest.first(),
        Some(ParsedSegment {
            segment: Segment::Wildcard,
            ..
        })
    );
    if via_wildcard {
        rest = rest.get(1..)?;
    } else if !has_legacy_raw_prefix(prefix, field_path) {
        return None;
    }

    let first = match rest.first() {
        None => return Some(CountPrefixMatch::CurrentElement),
        Some(first) => first,
    };
    if first.segment == Segment::Wildcard {
        return None;
    }

    Some(CountPrefixMatch::BelowElement {
        rest: field_path.get(first.start..)?,
        rest_has_wildcard: rest.iter().any(|s| s.segment == Segment::Wildcard),
        via_wildcard,
    })
}

/// Whether `field_path` is `prefix` itself or `prefix.<…>`, compared as raw
/// text (ASCII case-insensitively).  Bindings without the counted `[*]` keep
/// this legacy spelling; segment equivalence does not widen them.
///
/// The one spelling difference ignored is a `.` (and any blanks after it)
/// before a `[`: nested count prefixes are built without it (`a[*]['b']`),
/// while the legacy form spelled them with it (`a[*].['b']`).
fn has_legacy_raw_prefix(prefix: &str, field_path: &str) -> bool {
    let p = prefix.as_bytes();
    let f = field_path.as_bytes();
    let (mut i, mut j) = (0_usize, 0_usize);
    loop {
        i = skip_dot_before_bracket(p, i);
        let Some(pc) = p.get(i) else {
            break;
        };
        j = skip_dot_before_bracket(f, j);
        match f.get(j) {
            Some(fc) if fc.eq_ignore_ascii_case(pc) => {}
            _ => return false,
        }
        i = i.saturating_add(1);
        j = j.saturating_add(1);
    }
    f.get(j..)
        .is_some_and(|tail| tail.is_empty() || tail.starts_with(b"."))
}

/// If `bytes[pos..]` is `.`, optional blanks, then `[`, return the offset of
/// that `[`; otherwise `pos`.
fn skip_dot_before_bracket(bytes: &[u8], pos: usize) -> usize {
    if bytes.get(pos) != Some(&b'.') {
        return pos;
    }
    let mut next = pos.saturating_add(1);
    while bytes.get(next).is_some_and(u8::is_ascii_whitespace) {
        next = next.saturating_add(1);
    }
    if bytes.get(next) == Some(&b'[') {
        next
    } else {
        pos
    }
}

/// Join an outer count prefix and an inner collection path (relative to the
/// outer element) into the inner count's binding prefix: `a` + `b` →
/// `a[*].b`, `a` + `['b']` → `a[*]['b']`.
pub(super) fn join_count_prefix(outer: &str, inner: &str) -> String {
    if inner.starts_with('[') {
        alloc::format!("{outer}[*]{inner}")
    } else {
        alloc::format!("{outer}[*].{inner}")
    }
}

/// Navigate bound suffixes using the same quoted-key grammar as the matcher.
pub(super) fn split_bound_path(path: &str) -> Result<Vec<PathSegment>> {
    parse_binding_path(path)
        .ok_or_else(|| anyhow!("invalid bound field path: {path}"))?
        .into_iter()
        .map(|part| match part.segment {
            Segment::Key(key) => Ok(PathSegment::Key(key)),
            Segment::Index(index) => Ok(PathSegment::Index(index)),
            Segment::Wildcard => Err(anyhow!("unexpected wildcard in bound field path: {path}")),
        })
        .collect()
}

/// Parse a field path, possibly containing `[*]`, into segments.
///
/// Bracket contents are quote-aware: a subscript that opens with `'` or `"`
/// runs to the first matching quote that is followed (after optional
/// whitespace) by `]`, so `['a[*]']` and `['a].b']` are single keys.  A
/// subscript with no such closing quote is read up to the next `]` as an
/// unquoted literal, mirroring `split_path_without_wildcards`.  Unquoted
/// `*` is a wildcard and unquoted ASCII digits are an index; anything else
/// is a key.  A blank dotted segment before a bracket (`a. ['b']`) is
/// skipped, as `split_path_without_wildcards` does.  Returns `None` for
/// malformed paths.
fn parse_binding_path(path: &str) -> Option<Vec<ParsedSegment>> {
    let bytes = path.as_bytes();
    let mut segments = Vec::new();
    let mut pos = 0_usize;
    let mut quotes = ClosingQuotes::default();

    loop {
        let start = pos;
        let (segment, next) = if bytes.get(pos) == Some(&b'[') {
            parse_bracket(path, pos, &mut quotes)?
        } else {
            let end = path
                .get(pos..)?
                .find(['.', '['])
                .map_or(path.len(), |i| pos.saturating_add(i));
            let raw = path.get(pos..end)?;
            let token = raw.trim();
            if token.is_empty() && !raw.is_empty() && bytes.get(end) == Some(&b'[') {
                pos = end;
                continue;
            }
            if token.is_empty() || token.contains(']') {
                return None;
            }
            (Segment::Key(token.to_ascii_lowercase()), end)
        };
        segments.push(ParsedSegment { segment, start });
        pos = next;

        match bytes.get(pos).copied() {
            None => return Some(segments),
            Some(b'.') => {
                pos = pos.saturating_add(1);
                if pos >= bytes.len() {
                    return None;
                }
            }
            Some(b'[') => {}
            Some(_) => return None,
        }
    }
}

/// Memoized closing-quote searches for one path, so that a run of subscripts
/// with unclosed quotes (`a['x]['x]…`) is parsed in linear time.
///
/// For each quote character it records the last search: where it started
/// and the closing quote it found (or that there was none).  The first
/// closing quote at or after a position only moves forward as the position
/// does, so a later search starting inside the recorded range has the same
/// answer.
#[derive(Default)]
struct ClosingQuotes {
    single: Option<(usize, Option<usize>)>,
    double: Option<(usize, Option<usize>)>,
}

impl ClosingQuotes {
    /// The first `quote` at or after `from` that is followed (after optional
    /// whitespace) by `]`.
    fn find(&mut self, path: &str, quote: u8, from: usize) -> Option<usize> {
        let slot = if quote == b'"' {
            &mut self.double
        } else {
            &mut self.single
        };
        if let Some((searched_from, found)) = *slot {
            if searched_from <= from && found.is_none_or(|close| close >= from) {
                return found;
            }
        }
        let found = find_closing_quote(path, quote, from);
        *slot = Some((from, found));
        found
    }
}

fn find_closing_quote(path: &str, quote: u8, from: usize) -> Option<usize> {
    let mut search = from;
    while let Some(rel) = path.get(search..)?.find(char::from(quote)) {
        let close = search.saturating_add(rel);
        let after = path.get(close.saturating_add(1)..)?;
        if after.trim_start().starts_with(']') {
            return Some(close);
        }
        search = close.saturating_add(1);
    }
    None
}

/// Parse a bracket subscript starting at `open` (which holds `[`).  Returns
/// the segment and the byte offset just past the closing `]`.
fn parse_bracket(path: &str, open: usize, quotes: &mut ClosingQuotes) -> Option<(Segment, usize)> {
    let body_start = open.saturating_add(1);
    let body = path.get(body_start..)?;
    let lead = body.len().saturating_sub(body.trim_start().len());
    let quote_at = body_start.saturating_add(lead);

    if let Some(quote) = path
        .as_bytes()
        .get(quote_at)
        .copied()
        .filter(|b| *b == b'\'' || *b == b'"')
    {
        let content_start = quote_at.saturating_add(1);
        if let Some(close) = quotes.find(path, quote, content_start) {
            let key = path.get(content_start..close)?;
            if key.is_empty() {
                return None;
            }
            let after = path.get(close.saturating_add(1)..)?;
            let blanks = after.len().saturating_sub(after.trim_start().len());
            let bracket_end = close
                .saturating_add(1)
                .saturating_add(blanks)
                .saturating_add(1);
            return Some((Segment::Key(key.to_ascii_lowercase()), bracket_end));
        }
    }

    let rel_close = body.find(']')?;
    let raw_body = body.get(..rel_close)?;
    let raw = raw_body.trim();
    if raw.is_empty() || raw.contains('[') {
        return None;
    }
    let segment = if raw_body == "*" {
        Segment::Wildcard
    } else if raw.bytes().all(|b| b.is_ascii_digit()) {
        Segment::Index(raw.parse::<u64>().unwrap_or(u64::MAX))
    } else {
        Segment::Key(raw.to_ascii_lowercase())
    };
    Some((
        segment,
        body_start.saturating_add(rel_close).saturating_add(1),
    ))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing)]
mod tests {
    use alloc::string::ToString as _;
    use alloc::vec;

    use super::*;

    impl Segment {
        fn key(s: &str) -> Self {
            Self::Key(s.to_string())
        }
    }

    fn segments(path: &str) -> Vec<Segment> {
        parse_binding_path(path)
            .unwrap()
            .into_iter()
            .map(|s| s.segment)
            .collect()
    }

    fn below(rest: &str, rest_has_wildcard: bool, via_wildcard: bool) -> CountPrefixMatch<'_> {
        CountPrefixMatch::BelowElement {
            rest,
            rest_has_wildcard,
            via_wildcard,
        }
    }

    // -- parse_binding_path ---------------------------------------------------

    #[test]
    fn parse_dotted_and_bracket_spellings_are_equal() {
        let expected = vec![
            Segment::key("a"),
            Segment::key("b"),
            Segment::Wildcard,
            Segment::key("c"),
        ];
        for path in [
            "a.b[*].c",
            "a['b'][*]['c']",
            "a[\"b\"][*].c",
            "A.B[*].C",
            "a[ 'b' ][*].c",
            "a.['b'][*].c",
        ] {
            assert_eq!(segments(path), expected, "{path}");
        }
    }

    #[test]
    fn parse_quoted_key_is_one_literal_segment() {
        assert_eq!(
            segments("m['a.b'][*]"),
            vec![Segment::key("m"), Segment::key("a.b"), Segment::Wildcard]
        );
        assert_eq!(
            segments("m['a[*]'][*]"),
            vec![Segment::key("m"), Segment::key("a[*]"), Segment::Wildcard]
        );
        assert_eq!(segments("m[\"a[*]\"][*]"), segments("m['a[*]'][*]"));
        assert_eq!(
            segments("p['a][*].x[b']"),
            vec![Segment::key("p"), Segment::key("a][*].x[b")]
        );
        assert_eq!(
            segments("m[\"it's\"]"),
            vec![Segment::key("m"), Segment::key("it's")]
        );
    }

    #[test]
    fn parse_index_and_quoted_digits_differ() {
        assert_eq!(segments("a[0]"), vec![Segment::key("a"), Segment::Index(0)]);
        assert_eq!(
            segments("a['0']"),
            vec![Segment::key("a"), Segment::key("0")]
        );
        assert_eq!(segments("a.0"), vec![Segment::key("a"), Segment::key("0")]);
    }

    #[test]
    fn parse_unclosed_quote_falls_back_to_literal() {
        assert_eq!(segments("a[']"), vec![Segment::key("a"), Segment::key("'")]);
        assert_eq!(
            segments("a[\"1']"),
            vec![Segment::key("a"), Segment::key("\"1'")]
        );
    }

    #[test]
    fn parse_rejects_malformed_paths() {
        for path in [
            "", ".a", "a.", "a..b", "a[]", "a['']", "a[0]b", "a[0", "a]b", "a[[0]]",
        ] {
            assert!(parse_binding_path(path).is_none(), "{path}");
        }
    }

    // -- match_count_prefix ---------------------------------------------------

    #[test]
    fn match_current_element() {
        for path in ["items", "items[*]", "ITEMS[*]", "['items'][*]"] {
            assert_eq!(
                match_count_prefix("items", path),
                Some(CountPrefixMatch::CurrentElement),
                "{path}"
            );
        }
    }

    #[test]
    fn preserve_legacy_no_wildcard_spelling() {
        assert_eq!(
            match_count_prefix("items[*].subs", "items[*].subs"),
            Some(CountPrefixMatch::CurrentElement)
        );
        assert_eq!(
            match_count_prefix("items[*].subs", "items[*]['subs']"),
            None
        );
        assert_eq!(match_count_prefix("props.rules", "props['rules']"), None);
        assert_eq!(match_count_prefix("items", "items['state']"), None);
        assert_eq!(
            match_count_prefix("props.rules", "props['rules'].state"),
            None
        );
    }

    #[test]
    fn padded_star_is_literal_not_counted_wildcard() {
        assert_eq!(match_count_prefix("items", "items[ * ].state"), None);
        assert_eq!(
            segments("items[ * ]"),
            vec![Segment::key("items"), Segment::key("*")]
        );
    }

    #[test]
    fn match_bracket_suffix_forms() {
        assert_eq!(
            match_count_prefix("items", "items[*].state"),
            Some(below("state", false, true))
        );
        assert_eq!(
            match_count_prefix("items", "items[*]['state']"),
            Some(below("['state']", false, true))
        );
        assert_eq!(
            match_count_prefix("items", "items[*][\"state\"].x"),
            Some(below("[\"state\"].x", false, true))
        );
        assert_eq!(
            match_count_prefix("items", "items[*][0]"),
            Some(below("[0]", false, true))
        );
        assert_eq!(
            match_count_prefix("items", "items[*]['subs'][*]"),
            Some(below("['subs'][*]", true, true))
        );
        assert_eq!(
            match_count_prefix("items", "items[*]['a[*]']"),
            Some(below("['a[*]']", false, true))
        );
    }

    #[test]
    fn match_legacy_form_without_wildcard() {
        assert_eq!(
            match_count_prefix("items", "items.state"),
            Some(below("state", false, false))
        );
        assert_eq!(match_count_prefix("items", "items['state']"), None);
    }

    #[test]
    fn match_prefix_spelling_equivalence() {
        assert_eq!(
            match_count_prefix("a.b", "a['b'][*].c"),
            Some(below("c", false, true))
        );
        assert_eq!(
            match_count_prefix("a['b']", "a.b[*].c"),
            Some(below("c", false, true))
        );
        assert_eq!(
            match_count_prefix("items[*].subs", "items[*]['subs'][*]['v']"),
            Some(below("['v']", false, true))
        );
        assert_eq!(
            match_count_prefix("items[*]['subs']", "items[*].subs[*].v"),
            Some(below("v", false, true))
        );
    }

    #[test]
    fn match_quoted_wildcard_keys() {
        assert_eq!(
            match_count_prefix("m['a[*]']", "m[\"a[*]\"][*].x"),
            Some(below("x", false, true))
        );
        assert_eq!(
            match_count_prefix("m[\"a[*]\"]", "m['a[*]'][*]"),
            Some(CountPrefixMatch::CurrentElement)
        );
        // The quoted `[*]` is a literal key, not the counted wildcard.
        assert_eq!(match_count_prefix("m['a']", "m['a[*]'][*].x"), None);
        assert_eq!(match_count_prefix("m", "m['a[*]'].x"), None);
        assert_eq!(match_count_prefix("m['a[*]']", "m.a[*].x"), None);
    }

    #[test]
    fn match_different_quoted_keys_do_not_collide() {
        assert_eq!(match_count_prefix("m['a']", "m['b'][*].x"), None);
        assert_eq!(match_count_prefix("m['a.b']", "m.a.b[*].x"), None);
        assert_eq!(match_count_prefix("m.a.b", "m['a.b'][*].x"), None);
        assert_eq!(match_count_prefix("m['a.b']", "m['a']['b'][*]"), None);
        assert_eq!(match_count_prefix("a[0]", "a['0'][*].x"), None);
    }

    #[test]
    fn match_unrelated_paths() {
        assert_eq!(match_count_prefix("items", "itemsold[*].state"), None);
        assert_eq!(match_count_prefix("items", "other[*]"), None);
        assert_eq!(match_count_prefix("items.x", "items"), None);
        // A fixed index straight after the prefix is not the current element.
        assert_eq!(match_count_prefix("items", "items[0].state"), None);
        // Consecutive wildcards are left unbound (conservative).
        assert_eq!(match_count_prefix("items", "items[*][*]"), None);
        // Malformed paths never bind.
        assert_eq!(match_count_prefix("items", "items[*]..x"), None);
        assert_eq!(match_count_prefix("items[", "items[*]"), None);
    }

    #[test]
    fn join_prefix() {
        assert_eq!(join_count_prefix("a", "b"), "a[*].b");
        assert_eq!(join_count_prefix("a", "['b']"), "a[*]['b']");
        assert_eq!(join_count_prefix("a[*].x", "[0]"), "a[*].x[*][0]");
    }

    #[test]
    fn bound_navigation_preserves_quoted_delimiters() {
        assert_eq!(
            split_bound_path("['a][b']").unwrap(),
            vec![PathSegment::Key("a][b".to_string())]
        );
        assert_eq!(
            split_bound_path("['a[*]'][0]").unwrap(),
            vec![PathSegment::Key("a[*]".to_string()), PathSegment::Index(0)]
        );
        split_bound_path("subs[*]").unwrap_err();
    }

    #[test]
    fn legacy_dotted_index_binds_current_element() {
        assert_eq!(
            match_count_prefix("items", "items.[0]"),
            Some(below("[0]", false, false))
        );
        assert_eq!(
            match_count_prefix("ITEMS", "items.[0].state"),
            Some(below("[0].state", false, false))
        );
        assert_eq!(match_count_prefix("items", "items[0]"), None);
    }

    #[test]
    fn legacy_prefix_ignores_dot_before_bracket() {
        assert_eq!(
            match_count_prefix("a[*]['b']", "a[*].['b'].c"),
            Some(below("c", false, false))
        );
        assert_eq!(
            match_count_prefix("a[*].['b']", "a[*]['b'].c"),
            Some(below("c", false, false))
        );
        assert_eq!(
            match_count_prefix("a[*]['b']", "A[*].['B']"),
            Some(CountPrefixMatch::CurrentElement)
        );
        assert_eq!(match_count_prefix("a[*]['b']", "a[*].['b']['c']"), None);
        assert_eq!(match_count_prefix("a.b", "a.['b'].c"), None);
    }

    #[test]
    fn blank_segment_before_bracket_is_skipped() {
        assert_eq!(
            segments("a. ['b']"),
            vec![Segment::key("a"), Segment::key("b")]
        );
        assert_eq!(segments(" ['b']"), vec![Segment::key("b")]);
        assert_eq!(
            split_bound_path(" ['b']").unwrap(),
            vec![PathSegment::Key("b".to_string())]
        );
        assert_eq!(
            match_count_prefix("items", "items[*]. ['b']"),
            Some(below("['b']", false, true))
        );
        assert_eq!(
            match_count_prefix("a. ['b']", "a. ['b'][*].c"),
            Some(below("c", false, true))
        );
        assert_eq!(
            match_count_prefix("a. ['b']", "a['b'][*].c"),
            Some(below("c", false, true))
        );
        for path in ["a. ", "a. .b", "a. b. ", "a['b'] ['c']"] {
            assert!(parse_binding_path(path).is_none(), "{path}");
        }
    }

    #[test]
    fn quoted_key_continues_past_quote_not_before_bracket() {
        assert_eq!(
            segments("m['it's']"),
            vec![Segment::key("m"), Segment::key("it's")]
        );
        assert_eq!(
            segments("m['a'b' ][*]"),
            vec![Segment::key("m"), Segment::key("a'b"), Segment::Wildcard]
        );
    }

    #[test]
    fn unclosed_quotes_parse_in_linear_time() {
        let single = "a".to_string() + &"['x]".repeat(50_000);
        let single_parsed = segments(&single);
        assert_eq!(single_parsed.len(), 50_001);
        assert!(single_parsed[1..].iter().all(|s| *s == Segment::key("'x")));

        let double = "a".to_string() + &"[\"x]".repeat(50_000) + "['y']";
        let double_parsed = segments(&double);
        assert_eq!(double_parsed.len(), 50_002);
        assert_eq!(double_parsed[50_001], Segment::key("y"));
    }

    #[test]
    fn overflowing_index_saturates() {
        assert_eq!(
            segments("a[99999999999999999999]"),
            vec![Segment::key("a"), Segment::Index(u64::MAX)]
        );
        assert_eq!(
            match_count_prefix("items", "items[*][99999999999999999999]"),
            Some(below("[99999999999999999999]", false, true))
        );
    }

    #[test]
    fn bound_navigation_agrees_with_plain_splitter() {
        use super::super::utils::split_path_without_wildcards;
        for path in [
            "a.b.c",
            "tags['key']",
            "a[0].b",
            "tags['123']",
            "tags[\"123\"]",
            "tags.123",
            "a[ '1' ]",
            "a[ 1 ]",
            "a[007]",
            "a[+1]",
            "a[']",
            "a[\"1']",
            "config[\"'123'\"]",
            "a['b.c'].d",
            "a.['b']",
            "a[ * ].b",
            " ['b']",
            "a. ['b']",
            "a. ['b'].c",
            "a[99999999999999999999]",
        ] {
            assert_eq!(
                split_bound_path(path).unwrap(),
                split_path_without_wildcards(path).unwrap(),
                "{path}"
            );
        }
    }
}
