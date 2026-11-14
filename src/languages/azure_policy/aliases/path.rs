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
//!
//! The runtime operations ([`get`], [`set`], [`remove`], [`rename`],
//! [`can_set`]) navigate parsed segments, so a quoted key is one object key
//! and an index addresses one array element. Keys resolve to the exact key,
//! else the smallest case-insensitive match. Writes that meet an incompatible
//! shape do nothing; [`remove`] prunes containers it empties and arrays it
//! leaves all-null. The normalizer and denormalizer do not call these yet,
//! hence the `dead_code` allowances.

use alloc::string::String;
use alloc::vec::Vec;

use crate::{value::Object, Rc, Value};

use super::obj_map::{make_array, make_value, new_map, ObjMap};

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

#[derive(Debug, Clone)]
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

    /// The whole path as one part, or `None` if it has a wildcard.
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn scalar_part(&self) -> Option<Part<'_>> {
        (!self.segments.contains(&Segment::Wildcard)).then(|| self.part(0, self.segments.len()))
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

/// Segments of a path without wildcards; `None` if it does not parse.
#[cfg_attr(not(test), allow(dead_code))]
pub fn scalar_segments(path: &str) -> Option<Vec<Segment>> {
    let parsed = parse(path)?;
    (!parsed.segments.contains(&Segment::Wildcard)).then_some(parsed.segments)
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

#[cfg_attr(not(test), allow(dead_code))]
pub fn get<'a>(
    mut value: &'a Value,
    segments: &[Segment],
    case_insensitive: bool,
) -> Option<&'a Value> {
    for segment in segments {
        value = match segment {
            Segment::Key(key) => {
                let object = value.as_object().ok()?;
                object.get(&Value::String(Rc::clone(key))).or_else(|| {
                    case_insensitive
                        .then(|| {
                            object.iter_sorted().find_map(|(candidate, child)| {
                                candidate
                                    .as_string()
                                    .ok()
                                    .filter(|s| s.eq_ignore_ascii_case(key))
                                    .map(|_| child)
                            })
                        })
                        .flatten()
                })?
            }
            Segment::Index(index) => value.as_array().ok()?.get(*index)?,
            Segment::Wildcard => return None,
        };
    }
    Some(value)
}

pub fn get_map<'a>(map: &'a ObjMap, segments: &[Segment]) -> Option<&'a Value> {
    let (Segment::Key(first), rest) = segments.split_first()? else {
        return None;
    };
    let value = map.get(&map_key(map, first)?)?;
    get(value, rest, true)
}

/// The exact key, else the smallest case-insensitive match, so the choice
/// does not depend on hash order.
fn map_key(map: &ObjMap, key: &str) -> Option<Rc<str>> {
    map.get_key_value(key)
        .map(|(actual, _)| actual)
        .or_else(|| {
            map.keys()
                .filter(|candidate| candidate.eq_ignore_ascii_case(key))
                .min()
        })
        .cloned()
}

fn object_key(object: &Object, key: &Rc<str>) -> Option<Value> {
    let exact = Value::String(Rc::clone(key));
    if object.contains_key(&exact) {
        return Some(exact);
    }
    object
        .keys_sorted()
        .find(|candidate| {
            candidate
                .as_string()
                .is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key))
        })
        .cloned()
}

fn object_child<'a>(object: &'a Object, key: &Rc<str>) -> Option<&'a Value> {
    object.get(&Value::String(Rc::clone(key))).or_else(|| {
        object.iter_sorted().find_map(|(candidate, child)| {
            candidate
                .as_string()
                .is_ok_and(|candidate| candidate.eq_ignore_ascii_case(key))
                .then_some(child)
        })
    })
}

#[cfg_attr(not(test), allow(dead_code))]
pub fn rename(map: &mut ObjMap, source: &str, target: &str, lowercase: bool) {
    let (Some(source), Some(target)) = (scalar_segments(source), scalar_segments(target)) else {
        return;
    };
    if equivalent(&source, &target) || get_map(map, &target).is_some() || !can_set(map, &target) {
        return;
    }
    if let Some(value) = get_map(map, &source).cloned() {
        remove(map, &source);
        set(map, &target, value, lowercase);
    }
}

fn empty_for(segment: &Segment) -> Value {
    if matches!(segment, Segment::Index(_)) {
        make_array(Vec::new())
    } else {
        make_value(new_map())
    }
}

fn key_case(key: &Rc<str>, lowercase: bool) -> Rc<str> {
    if lowercase && key.bytes().any(|byte| byte.is_ascii_uppercase()) {
        Rc::from(key.to_ascii_lowercase())
    } else {
        Rc::clone(key)
    }
}

/// Writes need wildcard-free paths with indices within [`MAX_INDEX`].
fn settable(segments: &[Segment]) -> bool {
    segments.iter().all(|segment| match segment {
        Segment::Key(_) => true,
        Segment::Index(index) => *index <= MAX_INDEX,
        Segment::Wildcard => false,
    })
}

#[cfg_attr(not(test), allow(dead_code))]
pub fn set(map: &mut ObjMap, segments: &[Segment], value: Value, lowercase: bool) {
    if !settable(segments) {
        return;
    }
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let key = map_key(map, key).unwrap_or_else(|| key_case(key, lowercase));
    if let Some(next) = rest.first() {
        let child = map.entry(key).or_insert_with(|| empty_for(next));
        set_value(child, rest, value, lowercase);
    } else {
        map.insert(key, value);
    }
}

fn set_value(current: &mut Value, segments: &[Segment], value: Value, lowercase: bool) {
    let Some((segment, rest)) = segments.split_first() else {
        *current = value;
        return;
    };
    if matches!(current, Value::Null) {
        *current = empty_for(segment);
    }
    match (current, segment) {
        (Value::Object(object), Segment::Key(_)) => {
            set_object(Rc::make_mut(object), segments, value, lowercase);
        }
        (Value::Array(array), Segment::Index(index)) => {
            if *index > MAX_INDEX {
                return;
            }
            let array = Rc::make_mut(array);
            if *index >= array.len() {
                let Some(len) = index.checked_add(1) else {
                    return;
                };
                let mut values = array.to_vec();
                if values
                    .try_reserve(len.saturating_sub(values.len()))
                    .is_err()
                {
                    return;
                }
                values.resize(len, Value::Null);
                *array = values.into();
            }
            if let Some(child) = array.get_mut(*index) {
                if matches!(child, Value::Null) {
                    if let Some(next) = rest.first() {
                        *child = empty_for(next);
                    }
                }

                set_value(child, rest, value, lowercase);
            }
        }

        _ => {}
    }
}

#[cfg_attr(not(test), allow(dead_code))]
pub fn set_object(object: &mut Object, segments: &[Segment], value: Value, lowercase: bool) {
    if !settable(segments) {
        return;
    }
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let key = object_key(object, key).unwrap_or_else(|| Value::String(key_case(key, lowercase)));
    if let Some(next) = rest.first() {
        let child = object.get_or_insert_with(key, || empty_for(next));
        set_value(child, rest, value, lowercase);
    } else {
        object.insert(key, value);
    }
}

/// How removal treats containers it leaves empty.
#[derive(Clone, Copy)]
enum Prune {
    /// Keep emptied containers.
    Never,
    /// Remove emptied objects and arrays left all-null.
    Empty,
}

/// Remove a consumed alias leaf without discarding unrelated siblings.
#[cfg_attr(not(test), allow(dead_code))]
pub fn remove(map: &mut ObjMap, segments: &[Segment]) {
    remove_with(map, segments, Prune::Empty);
}

fn remove_with(map: &mut ObjMap, segments: &[Segment], prune: Prune) {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return;
    };
    let Some(actual) = map_key(map, key) else {
        return;
    };
    if rest.is_empty()
        || map
            .get_mut(&actual)
            .is_some_and(|value| remove_value(value, rest, prune))
    {
        map.remove(&actual);
    }
}

fn remove_value(value: &mut Value, segments: &[Segment], prune: Prune) -> bool {
    let Some((first, rest)) = segments.split_first() else {
        return false;
    };
    match (value, first) {
        (Value::Object(object), Segment::Key(_)) => {
            remove_in_object(Rc::make_mut(object), segments, prune)
        }
        (Value::Array(array), Segment::Index(index)) => {
            let array = Rc::make_mut(array);
            let Some(element) = array.get_mut(*index) else {
                return false;
            };
            if rest.is_empty() && matches!(element, Value::Null) {
                return false;
            }
            if !rest.is_empty() && !remove_value(element, rest, prune) {
                return false;
            }
            *element = Value::Null;
            match prune {
                Prune::Never => false,
                Prune::Empty => array.iter().all(|item| matches!(item, Value::Null)),
            }
        }
        _ => false,
    }
}

#[cfg_attr(not(test), allow(dead_code))]
pub fn remove_object(object: &mut Object, segments: &[Segment], prune: bool) -> bool {
    remove_in_object(
        object,
        segments,
        if prune { Prune::Empty } else { Prune::Never },
    )
}

fn remove_in_object(object: &mut Object, segments: &[Segment], prune: Prune) -> bool {
    let Some((Segment::Key(key_name), rest)) = segments.split_first() else {
        return false;
    };
    let Some(actual) = object_key(object, key_name) else {
        return false;
    };
    if rest.is_empty()
        || object
            .get_mut(&actual)
            .is_some_and(|value| remove_value(value, rest, prune))
    {
        object.remove(&actual);
        return matches!(prune, Prune::Empty) && object.is_empty();
    }
    false
}

/// Check shape compatibility before consuming the normalized source path.
#[cfg_attr(not(test), allow(dead_code))]
pub fn can_set(map: &ObjMap, segments: &[Segment]) -> bool {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return false;
    };
    can_set_value(map_key(map, key).and_then(|key| map.get(&key)), rest)
}

/// [`can_set`] for a path inside an array element object.
#[cfg_attr(not(test), allow(dead_code))]
pub fn can_set_object(object: &Object, segments: &[Segment]) -> bool {
    let Some((Segment::Key(key), rest)) = segments.split_first() else {
        return false;
    };
    can_set_value(object_child(object, key), rest)
}

fn can_set_value(current: Option<&Value>, segments: &[Segment]) -> bool {
    let Some((segment, rest)) = segments.split_first() else {
        return true;
    };
    match (current, segment) {
        (_, Segment::Wildcard) => false,
        (_, Segment::Index(index)) if *index > MAX_INDEX => false,
        (None, _) | (Some(Value::Null), _) => can_set_value(None, rest),
        (Some(Value::Object(object)), Segment::Key(key)) => {
            can_set_value(object_child(object, key), rest)
        }
        (Some(Value::Array(array)), Segment::Index(index)) => {
            can_set_value(array.get(*index), rest)
        }
        _ => false,
    }
}
