// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Alias-local path grammar. Quotes have no escapes and close only before
//! optional whitespace and `]`; delimiters inside quoted keys are literal.
//!
//! Unquoted brackets follow the policy compiler's non-wildcard field paths
//! (`split_path_without_wildcards`): only the exact text `[*]` is a wildcard
//! (`[ * ]` is the key `*`), trimmed digits are an index (`[ 0 ]`), and a dot
//! before a bracket is accepted (`a.[0]`). Whitespace before a bracket
//! (`a. [0]`, ` [0]`) and after a trailing dot (`a. `) is ignored; unlike
//! wildcard binding paths, whitespace after a bracket (`a[*] [0]`, `a[*] `) is
//! rejected. Paths longer than [`MAX_SEGMENTS`] are rejected.

use alloc::string::String;
use alloc::vec::Vec;

use crate::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Segment {
    Key(Rc<str>),
    Index(usize),
    Wildcard,
}

/// Largest accepted array index, bounding sparse arrays built from catalog paths.
pub const MAX_INDEX: usize = 4095;

/// Bound path depth so hostile catalogs cannot drive deep recursion.
pub const MAX_SEGMENTS: usize = 64;

pub struct Path {
    pub segments: Vec<Segment>,
    /// Parallel to `segments`: whether each key was written as a quoted subscript.
    pub quoted: Vec<bool>,
}

/// Segments between unquoted wildcards.
pub struct Part<'a> {
    pub segments: &'a [Segment],
    quoted: &'a [bool],
}

impl Path {
    /// Split at wildcards. A trailing wildcard yields a final empty part.
    pub fn parts(&self) -> Vec<Part<'_>> {
        let mut parts = Vec::new();
        let mut start = 0;
        for (index, segment) in self.segments.iter().enumerate() {
            if *segment == Segment::Wildcard {
                parts.push(self.part(start, index));
                start = index.saturating_add(1);
            }
        }
        parts.push(self.part(start, self.segments.len()));
        parts
    }

    /// [`Path::parts`] without the empty part left by a trailing `[*]`, which
    /// addresses the array itself rather than an element field.
    pub fn element_parts(&self) -> Vec<Part<'_>> {
        let mut parts = self.parts();
        if parts.len() > 1 && parts.last().is_some_and(|part| part.segments.is_empty()) {
            parts.pop();
        }
        parts
    }

    fn part(&self, start: usize, end: usize) -> Part<'_> {
        Part {
            segments: self.segments.get(start..end).unwrap_or_default(),
            quoted: self.quoted.get(start..end).unwrap_or_default(),
        }
    }
}

impl<'a> Part<'a> {
    /// Whether this part starts with an unquoted `properties` wrapper (any
    /// ASCII case) followed by a key; a standalone or indexed `properties` is
    /// an ordinary field.
    pub fn has_wrapper(&self) -> bool {
        self.quoted.first() == Some(&false) && self.has_flattened_wrapper()
    }

    /// Whether this part starts with a `properties` key (any ASCII case,
    /// quoted or not) followed by a key. Normalization lifts that object out
    /// of every element of a flattened sub-resource array, however the alias
    /// spells it.
    pub fn has_flattened_wrapper(&self) -> bool {
        matches!(self.segments.first(), Some(Segment::Key(key)) if key.eq_ignore_ascii_case("properties"))
            && matches!(self.segments.get(1), Some(Segment::Key(_)))
    }

    /// Whether this part starts with an unquoted `properties/...` key, which
    /// marks a sub-resource wrapper in ARM paths.
    pub fn has_slash_wrapper(&self) -> bool {
        self.quoted.first() == Some(&false)
            && matches!(self.segments.first(), Some(Segment::Key(key)) if key.starts_with("properties/"))
    }

    /// Strip a leading `properties` wrapper (see [`Part::has_wrapper`]).
    pub fn without_properties(&self) -> &'a [Segment] {
        if self.has_wrapper() {
            self.segments.get(1..).unwrap_or_default()
        } else {
            self.segments
        }
    }

    /// Strip a leading flattened wrapper (see [`Part::has_flattened_wrapper`]).
    pub fn without_flattened_wrapper(&self) -> &'a [Segment] {
        if self.has_flattened_wrapper() {
            self.segments.get(1..).unwrap_or_default()
        } else {
            self.segments
        }
    }
}

pub fn parse(path: &str) -> Option<Path> {
    let mut segments = Vec::new();
    let mut quoted = Vec::new();
    let mut pos = 0_usize;
    // Quote characters with no closing quote and `]` left in the path.
    let mut unclosed = [false; 2];
    loop {
        let (segment, end, is_quoted) = if path.as_bytes().get(pos) == Some(&b'[') {
            bracket(path, pos, &mut unclosed)?
        } else {
            let end = path
                .get(pos..)?
                .find(['.', '['])
                .map_or(path.len(), |offset| pos.saturating_add(offset));
            let key = path.get(pos..end)?.trim();
            if key.contains(']') {
                return None;
            }
            if key.is_empty() {
                // Like the compiler, skip blanks before a bracket and after a final dot.
                match path.as_bytes().get(end) {
                    Some(b'[') => {
                        pos = end;
                        continue;
                    }
                    None if !segments.is_empty() => return Some(Path { segments, quoted }),
                    _ => return None,
                }
            }
            (Segment::Key(Rc::from(key)), end, false)
        };
        segments.push(segment);
        quoted.push(is_quoted);
        if segments.len() > MAX_SEGMENTS {
            return None;
        }
        pos = end;
        match path.as_bytes().get(pos) {
            None => return Some(Path { segments, quoted }),
            Some(b'.') => {
                pos = pos.saturating_add(1);
                if pos == path.len() {
                    return None;
                }
            }
            Some(b'[') => {}
            _ => return None,
        }
    }
}

fn bracket(path: &str, open: usize, unclosed: &mut [bool; 2]) -> Option<(Segment, usize, bool)> {
    let body_start = open.saturating_add(1);
    let body = path.get(body_start..)?;
    let trimmed = body.trim_start();
    let quote = trimmed.as_bytes().first().copied();
    let slot = match quote {
        Some(b'\'') => unclosed.get_mut(0),
        Some(b'"') => unclosed.get_mut(1),
        _ => None,
    };
    if let (Some(quote), Some(slot)) = (quote, slot.filter(|slot| !**slot)) {
        let content_start = body_start
            .saturating_add(body.len().saturating_sub(trimmed.len()))
            .saturating_add(1);
        let mut search = content_start;
        while let Some(offset) = path.get(search..)?.find(char::from(quote)) {
            let close = search.saturating_add(offset);
            let after = path.get(close.saturating_add(1)..)?;
            let tail = after.trim_start();
            if tail.starts_with(']') {
                let key = path.get(content_start..close)?;
                if key.is_empty() {
                    return None;
                }
                let end = close
                    .saturating_add(1)
                    .saturating_add(after.len().saturating_sub(tail.len()))
                    .saturating_add(1);
                return Some((Segment::Key(Rc::from(key)), end, true));
            }
            search = close.saturating_add(1);
        }
        // No later bracket can close this quote either.
        *slot = true;
    }

    // Match field/binding paths: an unmatched opening quote is literal.
    let close = body.find(']')?;
    let raw = body.get(..close)?;
    let key = raw.trim();
    if key.is_empty() || key.contains('[') {
        return None;
    }
    let segment = if raw == "*" {
        Segment::Wildcard
    } else if key.bytes().all(|byte| byte.is_ascii_digit()) {
        let index = key.parse().ok()?;
        if index > MAX_INDEX {
            return None;
        }
        Segment::Index(index)
    } else {
        Segment::Key(Rc::from(key))
    };
    Some((
        segment,
        body_start.saturating_add(close).saturating_add(1),
        false,
    ))
}

pub fn equivalent(left: &[Segment], right: &[Segment]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| match (left, right) {
                (Segment::Key(left), Segment::Key(right)) => left.eq_ignore_ascii_case(right),
                _ => left == right,
            })
}

/// Whether [`render`] must spell this key as a quoted subscript. Quote
/// characters alone do not need one: they only open a quote after `[`.
fn needs_subscript(key: &str) -> bool {
    key.contains(['.', '[', ']']) || key.trim() != key
}

/// Whether [`render`] spells these segments as plain dotted keys, the only
/// form that dot-split runtime navigation (element remaps) can follow.
pub fn renders_dotted(segments: &[Segment]) -> bool {
    segments
        .iter()
        .all(|segment| matches!(segment, Segment::Key(key) if !needs_subscript(key)))
}

pub fn render(segments: &[Segment]) -> String {
    let mut result = String::new();
    for segment in segments {
        match segment {
            Segment::Key(key) => {
                if !needs_subscript(key) {
                    if !result.is_empty() {
                        result.push('.');
                    }
                    result.push_str(key);
                } else {
                    let quote = if key.match_indices('\'').any(|(offset, _)| {
                        key.get(offset.saturating_add(1)..)
                            .is_some_and(|tail| tail.trim_start().starts_with(']'))
                    }) {
                        '"'
                    } else {
                        '\''
                    };
                    result.push('[');
                    result.push(quote);
                    result.push_str(key);
                    result.push(quote);
                    result.push(']');
                }
            }
            Segment::Index(index) => result.push_str(&alloc::format!("[{index}]")),
            Segment::Wildcard => result.push_str("[*]"),
        }
    }
    result
}
