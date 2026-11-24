// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Sub-resource array re-wrapping during denormalization.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use crate::value::Object;
use crate::Value;

use super::super::obj_map::{make_value, new_map, obj_insert, obj_key_ci, val_str, ObjMap};
use super::super::path;
use super::super::types::ResolvedEntry;
use super::casing::restore_casing;

/// Sub-resource array element envelope fields that remain at the element root.
const ELEMENT_ENVELOPE_FIELDS: &[&str] = &["name", "type", "id", "etag"];

/// The fields of a sub-resource array's elements that stay at the element
/// root, from the aliases over the array.
#[derive(Clone, Debug, Default)]
struct Fields {
    /// Fields that stay at the element root.
    envelope: BTreeSet<String>,
    /// Fields that both a wrapped and an unwrapped alias give the same name,
    /// with the element-level short-name keys of the wrapped aliases. Such a
    /// field came from a wrapped alias, and is wrapped, when the element had
    /// one of them.
    shared: BTreeMap<String, BTreeSet<Vec<String>>>,
}

impl Fields {
    fn extend(&mut self, other: &Self) {
        self.envelope.extend(other.envelope.iter().cloned());
        for (field, names) in &other.shared {
            self.shared
                .entry(field.clone())
                .or_default()
                .extend(names.iter().cloned());
        }
    }

    /// Whether `field` stays at the root of an element whose normalized
    /// value was `input`.
    fn at_root(&self, field: &str, input: Option<&Value>) -> bool {
        let field = field.to_ascii_lowercase();
        if self.envelope.contains(&field) {
            return true;
        }
        let Some(names) = self.shared.get(&field) else {
            return false;
        };
        let Some(Value::Object(input)) = input else {
            return false;
        };
        !names.iter().any(|name| has_keys(input, name))
    }
}

/// The fields of each sub-resource short name that resolves to one array.
type Target<'a> = BTreeMap<&'a str, Fields>;

/// The denormalization state that re-wrapping reads.
pub struct Context<'a> {
    /// The resource type's resolved aliases, by lowercase short name.
    pub entries: &'a BTreeMap<String, ResolvedEntry>,
    /// The API version that selects each alias's ARM path.
    pub api_version: Option<&'a str>,
    /// What phases 2a, 2b and 2c wrote.
    pub writes: &'a Writes,
    /// Whether phase 2a put non-aliased keys at the ARM root.
    pub is_data_plane: bool,
    /// The key casing phases 2a and 2b restored.
    pub casing_map: &'a BTreeMap<String, String>,
    /// The normalized resource being denormalized.
    pub normalized: &'a Object,
}

/// The writes of phases 2a, 2b and 2c, in order.
#[derive(Debug, Default)]
pub struct Writes {
    /// The lowercase short names of the plain aliases phase 2b wrote.
    aliases: BTreeSet<String>,
    log: Vec<Write>,
}

/// One value written to the output.
#[derive(Debug)]
struct Write {
    /// Whether the write was at the ARM root rather than under `properties`.
    at_root: bool,
    /// The output keys written, as spelled there: keys differing only in
    /// case are distinct.
    keys: Vec<String>,
    /// The normalized name of the value, lowercase.
    source: String,
    /// The normalized key the value was read from, as it is spelled there.
    read: String,
}

/// The write that left a value in the output.
pub struct Origin<'a> {
    /// The value's normalized name: the write's source, followed by the keys
    /// below the write.
    pub name: String,
    /// The normalized key the write read.
    pub read: &'a str,
    /// How many output keys the write covered.
    pub depth: usize,
}

impl Writes {
    /// Record writing the value of normalized key `source`, read from the
    /// normalized key `read`, at the dotted path `keys`.
    pub fn record(&mut self, at_root: bool, keys: &str, source: &str, read: &str) {
        let keys = keys.split('.').map(String::from).collect();
        self.push(at_root, keys, source, read);
    }

    /// [`Self::record`] at the single, possibly dotted, key `key`.
    pub fn record_key(&mut self, at_root: bool, key: &str, source: &str, read: &str) {
        self.push(at_root, alloc::vec![String::from(key)], source, read);
    }

    /// Record phase 2b writing the plain alias `key`, read from the
    /// normalized key `read`, at `keys`.
    pub fn record_alias(&mut self, at_root: bool, keys: &str, key: &str, read: &str) {
        self.aliases.insert(String::from(key));
        self.record(at_root, keys, key, read);
    }

    fn push(&mut self, at_root: bool, keys: Vec<String>, source: &str, read: &str) {
        self.log.push(Write {
            at_root,
            keys,
            source: source.to_ascii_lowercase(),
            read: String::from(read),
        });
    }

    /// The normalized key read by the last write to exactly `key` under
    /// `properties`.
    pub fn read_at(&self, key: &str) -> Option<String> {
        self.log
            .iter()
            .rev()
            .find(|write| {
                !write.at_root
                    && write.keys.len() == 1
                    && write.keys.first().is_some_and(|k| k == key)
            })
            .map(|write| write.read.clone())
    }

    /// Whether a write of some other normalized name than `name` (dotted
    /// keys) left the value now at `keys`.
    pub fn replaced(&self, at_root: bool, keys: &[String], name: &[String]) -> bool {
        let keys: Vec<&str> = keys.iter().map(String::as_str).collect();
        self.origin(at_root, &keys)
            .is_some_and(|origin| origin.name != name.join(".").to_ascii_lowercase())
    }

    /// The write that left the value now at `keys`: the last write at or
    /// above `keys`. `None` if nothing was written there. Writes to exactly
    /// `keys` come first; keys from normalized names match the written keys
    /// in any case.
    pub fn origin(&self, at_root: bool, keys: &[&str]) -> Option<Origin<'_>> {
        let last_write = |same: fn(&str, &str) -> bool| {
            self.log.iter().rev().find(|write| {
                write.at_root == at_root
                    && write.keys.len() <= keys.len()
                    && write
                        .keys
                        .iter()
                        .zip(keys)
                        .all(|(dest, key)| same(dest, key))
            })
        };
        let write = last_write(|dest, key| dest == key)
            .or_else(|| last_write(|dest, key| dest.eq_ignore_ascii_case(key)))?;
        let below = keys.get(write.keys.len()..).unwrap_or_default();
        let name: Vec<&str> = core::iter::once(write.source.as_str())
            .chain(below.iter().copied())
            .collect();
        Some(Origin {
            name: name.join(".").to_ascii_lowercase(),
            read: &write.read,
            depth: write.keys.len(),
        })
    }
}

/// Re-wrap sub-resource array elements by moving non-envelope fields back
/// under each element's `properties` object.
pub fn rewrap_sub_resource_arrays(
    result: &mut ObjMap,
    properties: &mut ObjMap,
    sub_arrays: &BTreeSet<String>,
    cx: &Context<'_>,
) {
    if sub_arrays.is_empty() {
        return;
    }
    // Parse once per call; only wildcard aliases can address array elements.
    let parsed: Vec<(path::Path, path::Path)> = cx
        .entries
        .values()
        .filter(|entry| entry.is_wildcard)
        .filter_map(|entry| {
            Some((
                path::parse(&entry.short_name)?,
                path::parse(entry.select_path(cx.api_version))?,
            ))
        })
        .collect();

    // Several short names can resolve to the same array (two plain aliases
    // with one ARM path). Wrap each array once. Keys differing only in case
    // are different arrays, so group by the keys actually in the output.
    let mut targets: BTreeMap<(bool, Vec<String>), Target<'_>> = BTreeMap::new();
    for sub_array_path in sub_arrays {
        let fields = classify_envelope_fields(sub_array_path, &parsed);
        let (at_root, keys) = written_keys(sub_array_path, cx);
        let keys: Vec<&str> = keys.iter().map(String::as_str).collect();
        let map = if at_root { &*result } else { &*properties };
        targets
            .entry((at_root, output_keys(map, &keys)))
            .or_default()
            .insert(sub_array_path.as_str(), fields);
    }

    // Deepest first, so an outer array is wrapped after the arrays inside it.
    let mut sorted: Vec<_> = targets.into_iter().collect();
    sorted.sort_by_key(|((_, keys), _)| core::cmp::Reverse(keys.len()));

    for ((at_root, keys), by_name) in sorted {
        let keys: Vec<&str> = keys.iter().map(String::as_str).collect();
        // A later write may have replaced the flattened array with a value
        // the normalizer left wrapped (another plain alias with the same ARM
        // path, or one over the array's parent). Wrap only a flattened array.
        let origin = cx.writes.origin(at_root, &keys);
        if origin
            .as_ref()
            .is_some_and(|origin| !sub_arrays.contains(&origin.name))
        {
            continue;
        }
        // Classify by the name whose value is there. Otherwise keep a field
        // at the element root if any of the names leaves it there.
        let fields = origin
            .as_ref()
            .and_then(|origin| by_name.get(origin.name.as_str()))
            .map_or_else(
                || {
                    let mut all = Fields::default();
                    for fields in by_name.values() {
                        all.extend(fields);
                    }
                    all
                },
                Fields::clone,
            );
        // The normalized value the write read, for the fields whose origin
        // its elements decide. Below the write, the keys are the same.
        let (input, skip) = origin.as_ref().map_or((None, 0), |origin| {
            let read = Value::String(crate::Rc::from(origin.read));
            (cx.normalized.get(&read), origin.depth.saturating_sub(1))
        });
        let Some((first, rest)) = keys.split_first() else {
            continue;
        };
        let map = if at_root {
            &mut *result
        } else {
            &mut *properties
        };
        if let Some(value) = obj_key_ci(map, first).and_then(|key| map.get_mut(key.as_ref())) {
            rewrap_at(value, rest, &fields, input, skip);
        }
    }
}

/// The keys in `map` that `keys` lead to: each key as it is in the output
/// (exact match first, else the smallest that differs only in case, as
/// element remaps pick), as far as objects go. Keys inside arrays are matched
/// per element and kept as given.
pub fn output_keys(map: &ObjMap, keys: &[&str]) -> Vec<String> {
    let mut out = Vec::with_capacity(keys.len());
    let mut current: Option<&Value> = None;
    for (i, key) in keys.iter().enumerate() {
        let found = match current {
            None => {
                obj_key_ci(map, key).and_then(|k| Some((String::from(k.as_ref()), map.get(&k)?)))
            }
            Some(Value::Object(obj)) => find_key_ci_btree(obj, key).and_then(|k| {
                let name = String::from(val_str(&k)?);
                Some((name, obj.get(&k)?))
            }),
            Some(_) => None,
        };
        match found {
            Some((name, value)) => {
                out.push(name);
                current = Some(value);
            }
            None => {
                out.extend(
                    keys.get(i..)
                        .unwrap_or_default()
                        .iter()
                        .map(|k| String::from(*k)),
                );
                break;
            }
        }
    }
    out
}

/// Where a sub-resource array sits in the denormalized output: `true` for
/// the ARM root rather than `properties`, plus the keys leading to it. When
/// phase 2b wrote a plain alias for the first key, the array is under that
/// alias's ARM path (`x` -> `properties.items` puts `x.y` at `items.y`);
/// otherwise phase 2a wrote the key as is. Keys from the short name get the
/// casing those phases restored, so a sibling that differs only in case is
/// not taken for the array.
fn written_keys(sub_array_path: &str, cx: &Context<'_>) -> (bool, Vec<String>) {
    let names: Vec<&str> = sub_array_path.split('.').collect();
    let restore = |part: &[&str]| -> Vec<String> {
        part.iter()
            .map(|name| restore_casing(name, cx.casing_map))
            .collect()
    };
    let Some((first, rest)) = names.split_first() else {
        return (cx.is_data_plane, restore(&names));
    };
    match alias_location(first, cx.entries, cx.api_version, cx.writes) {
        Some((at_root, arm)) => {
            let mut keys: Vec<String> = arm.into_iter().map(String::from).collect();
            keys.extend(restore(rest));
            (at_root, keys)
        }
        None => (cx.is_data_plane, restore(&names)),
    }
}

/// Where phase 2b wrote the plain alias `key`: `true` for the ARM root
/// rather than `properties`, plus its ARM keys. `None` if it wrote nothing
/// for `key`.
fn alias_location<'a>(
    key: &str,
    entries: &'a BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    writes: &Writes,
) -> Option<(bool, Vec<&'a str>)> {
    if !writes.aliases.contains(key) {
        return None;
    }
    let arm = entries.get(key)?.select_path(api_version);
    let (at_root, arm) = arm
        .strip_prefix("properties.")
        .map_or((true, arm), |inner| (false, inner));
    Some((at_root, arm.split('.').collect()))
}

/// Point an element remap's array chain at where phase 2b wrote its outer
/// array: `true` for the ARM root rather than `properties`, plus the chain
/// with its first key replaced by the alias's ARM keys. `None` if phase 2b
/// did not write the first key.
pub fn redirect_chain(
    chain: &[Vec<String>],
    entries: &BTreeMap<String, ResolvedEntry>,
    api_version: Option<&str>,
    writes: &Writes,
) -> Option<(bool, Vec<Vec<String>>)> {
    let (outer, inner) = chain.split_first()?;
    let (first, rest) = outer.split_first()?;
    let (at_root, arm) = alias_location(first, entries, api_version, writes)?;
    let redirected = arm
        .into_iter()
        .map(String::from)
        .chain(rest.iter().cloned())
        .collect();
    Some((
        at_root,
        core::iter::once(redirected)
            .chain(inner.iter().cloned())
            .collect(),
    ))
}

/// Determine which element-level fields are envelope fields for a given
/// sub-resource array, from parsed `(short name, ARM path)` pairs. Entries
/// whose short name or selected ARM path does not parse are excluded.
fn classify_envelope_fields(sub_array_path: &str, parsed: &[(path::Path, path::Path)]) -> Fields {
    let mut envelope = BTreeSet::new();
    for &f in ELEMENT_ENVELOPE_FIELDS {
        envelope.insert(f.to_ascii_lowercase());
    }

    let array_keys: Vec<&str> = sub_array_path.split('.').collect();
    // ARM names of the element's root fields, and of the fields under its
    // `properties` wrapper.
    let mut unwrapped = BTreeSet::new();
    let mut wrapped: BTreeMap<String, BTreeSet<Vec<String>>> = BTreeMap::new();
    for (short, arm_path) in parsed {
        let parts = short.parts();
        let Some(level) = array_level(&array_keys, &parts) else {
            continue;
        };
        let Some(short_part) = parts.get(level) else {
            continue;
        };
        let Some(path::Segment::Key(first_segment)) = short_part.segments.first() else {
            continue;
        };
        // Classify by the ARM part at this array's element level, not by the
        // deepest part of a nested field. The array is flattened, so a quoted
        // `['properties']` there is the same wrapper.
        let arm_parts = arm_path.parts();
        let arm_part = arm_parts.get(level);
        if let Some(part) = arm_part.filter(|part| part.has_flattened_wrapper()) {
            if let Some(path::Segment::Key(key)) = part.segments.get(1) {
                let name = short_part
                    .segments
                    .iter()
                    .map_while(|segment| match segment {
                        path::Segment::Key(segment_key) => Some(segment_key.to_ascii_lowercase()),
                        _ => None,
                    })
                    .collect();
                wrapped
                    .entry(key.to_ascii_lowercase())
                    .or_default()
                    .insert(name);
            }
            continue;
        }
        // Phase 2d gives the field its ARM name when it finds the array, and
        // leaves the short name when it does not.
        envelope.insert(first_segment.to_ascii_lowercase());
        if let Some(path::Segment::Key(key)) = arm_part.and_then(|part| part.segments.first()) {
            unwrapped.insert(key.to_ascii_lowercase());
        }
    }
    // A name that is also a wrapped field's ARM name may have come from
    // either alias; the element decides. The standard envelope fields stay.
    envelope.extend(unwrapped);
    let mut shared = BTreeMap::new();
    envelope.retain(|field| match wrapped.get(field) {
        Some(names) if !ELEMENT_ENVELOPE_FIELDS.contains(&field.as_str()) => {
            shared.insert(field.clone(), names.clone());
            false
        }
        _ => true,
    });

    Fields { envelope, shared }
}

/// Whether `keys` lead somewhere in `object`, matching keys in any case.
fn has_keys(object: &Object, keys: &[String]) -> bool {
    let Some((first, rest)) = keys.split_first() else {
        return true;
    };
    let Some(child) = find_key_ci_btree(object, first).and_then(|key| object.get(&key)) else {
        return false;
    };
    match child {
        Value::Object(child) => has_keys(child, rest),
        _ => rest.is_empty(),
    }
}

/// Number of leading short-name parts whose keys spell `array_keys`, i.e.
/// the part index of the array's elements; `None` if the alias is outside
/// the array. A part may hold several keys (`a.b[*]`).
fn array_level(array_keys: &[&str], parts: &[path::Part<'_>]) -> Option<usize> {
    let mut remaining = array_keys;
    for (level, part) in parts.iter().enumerate() {
        if remaining.is_empty() {
            return Some(level);
        }
        for segment in part.segments {
            let path::Segment::Key(key) = segment else {
                return None;
            };
            let (name, rest) = remaining.split_first()?;
            if !key.eq_ignore_ascii_case(name) {
                return None;
            }
            remaining = rest;
        }
    }
    None
}

/// Follow `keys` from `value` and re-wrap the elements of the array there.
/// Like the normalizer's path tracking, arrays along the way are walked
/// element by element and objects by key, so a name such as `a.b.c` matches
/// `a.b[*].c[*]` and `a[*].b[*].c[*]` alike. `input` follows along in the
/// normalized value once the first `skip` keys, which have no counterpart
/// there, are passed.
fn rewrap_at(
    value: &mut Value,
    keys: &[&str],
    fields: &Fields,
    input: Option<&Value>,
    skip: usize,
) {
    match value {
        Value::Array(arr) => {
            let inner = crate::Rc::make_mut(arr);
            for (index, elem) in inner.iter_mut().enumerate() {
                let input = if skip == 0 {
                    input.and_then(|input| input.as_array().ok()?.get(index))
                } else {
                    input
                };
                if keys.is_empty() {
                    *elem = rewrap_element(elem, fields, input);
                } else {
                    rewrap_at(elem, keys, fields, input, skip);
                }
            }
        }
        Value::Object(obj) => {
            let Some((first, rest)) = keys.split_first() else {
                return;
            };
            let input = match skip.checked_sub(1) {
                Some(_) => input,
                None => input.and_then(|input| {
                    let input = input.as_object().ok()?;
                    input.get(&find_key_ci_btree(input, first)?)
                }),
            };
            let obj = crate::Rc::make_mut(obj);
            if let Some(key) = find_key_ci_btree(obj, first) {
                if let Some(child) = obj.get_mut(&key) {
                    rewrap_at(child, rest, fields, input, skip.saturating_sub(1));
                }
            }
        }
        _ => {}
    }
}

/// Find a key in a BTreeMap: the exact key, else any case-insensitive match.
fn find_key_ci_btree(btree: &Object, key: &str) -> Option<Value> {
    let exact = Value::String(crate::Rc::from(key));
    if btree.contains_key(&exact) {
        return Some(exact);
    }
    btree
        .keys()
        .find(|k| val_str(k).is_some_and(|s| s.eq_ignore_ascii_case(key)))
        .cloned()
}

/// Re-wrap a single sub-resource array element by moving non-envelope
/// fields back under a `properties` object.
fn rewrap_element(element: &Value, fields: &Fields, input: Option<&Value>) -> Value {
    let obj = match element.as_object() {
        Ok(o) => o,
        Err(_) => return element.clone(),
    };

    let mut envelope = new_map();
    let mut props = new_map();

    for (key, val) in obj.iter() {
        let key_s = match val_str(key) {
            Some(s) => s,
            None => continue,
        };
        if fields.at_root(key_s, input) {
            obj_insert(&mut envelope, key_s, val.clone());
        } else {
            obj_insert(&mut props, key_s, val.clone());
        }
    }

    if !props.is_empty() {
        obj_insert(&mut envelope, "properties", make_value(props));
    }

    make_value(envelope)
}
