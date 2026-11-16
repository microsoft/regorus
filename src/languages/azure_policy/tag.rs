// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Shared classification for Azure Policy tag field paths.

use alloc::string::String;

/// How a field path refers to resource tags.
#[derive(Debug, PartialEq, Eq)]
pub enum TagField {
    /// `tags`: the whole tag collection.
    Collection,
    /// One tag, named by `tags.<name>` or `tags[<name>]`. Holds the decoded
    /// name: in a single-quoted bracket name each `''` is decoded to `'`.
    Key(String),
    /// An unquoted bracket path containing the literal text `[*]`, such as
    /// `tags[*]`.
    Wildcard,
    /// `tags.` or a bracket whose name is empty after normalization.
    Empty,
}

/// The key named by a `[...]` path segment.
pub struct BracketTag<'a> {
    /// The key, after normalization by [`normalize_bracket_tag`].
    pub name: &'a str,
    /// The outer quote character (`'` or `"`) removed, if any.
    pub quote: Option<char>,
}

/// Normalize the contents of a `[...]` path segment to the key it names.
///
/// Surrounding whitespace is trimmed (as [`str::trim`] does, using the
/// Unicode `White_Space` property), then one matching pair of outer `'` or
/// `"` quotes is removed. Whitespace inside the quotes is kept, so `[ env ]`
/// and `[ 'env' ]` name `env` while `[' env ']` names ` env `. Escapes are
/// not decoded here; see [`classify_tag_field`] for tag names.
pub fn normalize_bracket_tag(contents: &str) -> BracketTag<'_> {
    let trimmed = contents.trim();
    strip_matching_outer_quotes(trimmed).map_or(
        BracketTag {
            name: trimmed,
            quote: None,
        },
        |(quote, name)| BracketTag {
            name,
            quote: Some(quote),
        },
    )
}

/// Classify a field path that may refer to resource tags.
///
/// The `tags` prefix is matched ASCII-case-insensitively; any other path
/// returns `None`.
///
/// - `tags` is [`TagField::Collection`].
/// - `tags.<name>` is [`TagField::Key`] with everything after the first `.`
///   as the name, so `tags.Dept.Name` names the tag `Dept.Name`. An empty
///   name is [`TagField::Empty`].
/// - `tags[<contents>]` takes everything up to the final `]` and normalizes
///   it with [`normalize_bracket_tag`], so `tags[Dept.Name]]` names
///   `Dept.Name]`. In a single-quoted name, each `''` stands for one `'`
///   (`tags['''x''']` names `'x'`, `tags['a''b']` names `a'b`); a `'` that
///   is not part of such a pair is kept as is, and double-quoted or unquoted
///   names are taken verbatim. An empty name is [`TagField::Empty`] and a
///   quoted name is always [`TagField::Key`]. An unquoted path containing the literal text
///   `[*]` anywhere (`tags[*]`, `tags[env][*]`) is [`TagField::Wildcard`];
///   any other name is [`TagField::Key`], so a padded `tags[ * ]` names the
///   tag `*`.
///
/// Callers decide what a wildcard means in their context.
pub fn classify_tag_field(text: &str) -> Option<TagField> {
    let prefix = text.get(.."tags".len())?;
    if !prefix.eq_ignore_ascii_case("tags") {
        return None;
    }
    let rest = text.get("tags".len()..).unwrap_or_default();

    if rest.is_empty() {
        Some(TagField::Collection)
    } else if let Some(tag) = rest.strip_prefix('.') {
        if tag.is_empty() {
            Some(TagField::Empty)
        } else {
            Some(TagField::Key(tag.into()))
        }
    } else if let Some(contents) = rest.strip_prefix('[').and_then(|r| r.strip_suffix(']')) {
        let bracket_tag = normalize_bracket_tag(contents);
        let tag = bracket_tag.name;

        if tag.is_empty() {
            Some(TagField::Empty)
        } else if bracket_tag.quote == Some('\'') {
            Some(TagField::Key(tag.replace("''", "'")))
        } else if bracket_tag.quote.is_some() {
            Some(TagField::Key(tag.into()))
        } else if text.contains("[*]") {
            Some(TagField::Wildcard)
        } else {
            Some(TagField::Key(tag.into()))
        }
    } else {
        None
    }
}

fn strip_matching_outer_quotes(s: &str) -> Option<(char, &str)> {
    ['\'', '"'].into_iter().find_map(|quote| {
        s.strip_prefix(quote)
            .and_then(|inner| inner.strip_suffix(quote))
            .map(|inner| (quote, inner))
    })
}

#[cfg(test)]
mod tests {
    use super::{classify_tag_field, TagField};

    #[test]
    fn classify_tag_field_requires_tags_segment() {
        for path in ["tagsBackup", "tagsExtra.env", "tagsExtra[env]"] {
            assert_eq!(classify_tag_field(path), None, "{path}");
        }
    }

    #[test]
    fn classify_tag_field_unescapes_doubled_apostrophes_in_single_quotes() {
        for (path, expected) in [
            ("tags['''x''']", "'x'"),
            ("tags['a''b']", "a'b"),
            ("tags[ '''x''' ]", "'x'"),
            ("tags['''']", "'"),
            ("tags['''''']", "''"),
            ("tags['a'''b']", "a''b"),
            ("tags['a''''b']", "a''b"),
            ("tags['a'b']", "a'b"),
            ("tags[''x'']", "'x'"),
            ("tags['''a[*]''']", "'a[*]'"),
            ("tags[\"a''b\"]", "a''b"),
            ("tags[a''b]", "a''b"),
            ("tags.a''b", "a''b"),
        ] {
            assert_eq!(
                classify_tag_field(path),
                Some(TagField::Key(expected.into())),
                "{path}"
            );
        }
    }
}
