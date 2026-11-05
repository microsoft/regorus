// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Shared classification for Azure Policy tag field paths.

use alloc::string::String;

/// How a field path refers to resource tags.
#[derive(Debug, PartialEq, Eq)]
pub enum TagField {
    /// `tags`: the whole tag collection.
    Collection,
    /// One tag, named by `tags.<name>` or `tags[<name>]`.
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
    /// Whether a matching pair of outer quotes was removed.
    pub quoted: bool,
}

/// Normalize the contents of a `[...]` path segment to the key it names.
///
/// Surrounding whitespace is trimmed (as [`str::trim`] does, using the
/// Unicode `White_Space` property), then one matching pair of outer `'` or
/// `"` quotes is removed. Whitespace inside the quotes is kept, so `[ env ]`
/// and `[ 'env' ]` name `env` while `[' env ']` names ` env `.
pub fn normalize_bracket_tag(contents: &str) -> BracketTag<'_> {
    let trimmed = contents.trim();
    strip_matching_outer_quotes(trimmed).map_or(
        BracketTag {
            name: trimmed,
            quoted: false,
        },
        |name| BracketTag { name, quoted: true },
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
///   `Dept.Name]`. An empty name is [`TagField::Empty`] and a quoted name is
///   always [`TagField::Key`]. An unquoted path containing the literal text
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
        } else if bracket_tag.quoted {
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

fn strip_matching_outer_quotes(s: &str) -> Option<&str> {
    s.strip_prefix('\'')
        .and_then(|inner| inner.strip_suffix('\''))
        .or_else(|| {
            s.strip_prefix('"')
                .and_then(|inner| inner.strip_suffix('"'))
        })
}

#[cfg(test)]
mod tests {
    use super::classify_tag_field;

    #[test]
    fn classify_tag_field_requires_tags_segment() {
        for path in ["tagsBackup", "tagsExtra.env", "tagsExtra[env]"] {
            assert_eq!(classify_tag_field(path), None, "{path}");
        }
    }
}
