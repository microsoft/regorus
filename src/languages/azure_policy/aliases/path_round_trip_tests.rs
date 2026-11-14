// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::unwrap_used)]

use super::obj_map::{make_value, new_map, ObjMap};
use super::path::{self, Segment};
use crate::Value;
use alloc::vec;
use serde_json::{json, Value as Json};

fn map_of(input: Json) -> ObjMap {
    let mut map = new_map();
    for (key, value) in input.as_object().unwrap() {
        map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
    }
    map
}

fn segments(path_text: &str) -> vec::Vec<Segment> {
    path::scalar_segments(path_text).unwrap()
}

#[test]
fn case_insensitive_set_reuses_keys() {
    let mut map = new_map();
    path::set(&mut map, &segments("Config.Child"), Value::from(1), false);
    path::set(&mut map, &segments("config.child"), Value::from(2), false);
    assert_eq!(
        make_value(map),
        Value::from(json!({"Config": {"Child": 2}}))
    );
    let mut lowered = new_map();
    path::set(
        &mut lowered,
        &segments("Config.Child"),
        Value::from(1),
        true,
    );
    assert_eq!(
        make_value(lowered),
        Value::from(json!({"config": {"child": 1}}))
    );
}

#[test]
fn get_follows_parsed_segments() {
    let value = Value::from(json!({"A": {"b.c": [10, {"D": 2}]}}));
    let get = |path_text: &str, case_insensitive| {
        path::get(&value, &segments(path_text), case_insensitive).cloned()
    };
    assert_eq!(get("A['b.c'][0]", false), Some(Value::from(10)));
    assert_eq!(get("a['b.c'][1].d", true), Some(Value::from(2)));
    assert_eq!(get("a['b.c'][1].d", false), None);
    assert_eq!(get("A.b.c", false), None);
    assert_eq!(get("A['b.c'][2]", false), None);
    let wildcard = path::parse("A['b.c'][*]").unwrap();
    assert!(wildcard.scalar_part().is_none());
    let scalar = path::parse("A['b.c'][0]").unwrap();
    assert_eq!(
        scalar.scalar_part().unwrap().segments,
        &segments("A['b.c'][0]")[..]
    );
    assert!(path::get(&value, &wildcard.segments, false).is_none());
    assert!(path::scalar_segments("A[*]").is_none());
}

#[test]
fn remove_prunes_only_emptied_containers() {
    for (input, path_text, expected) in [
        (json!({"a": {"b": 1}}), "a.b", json!({})),
        (
            json!({"a": {"b": 1, "c": 2}}),
            "A.B",
            json!({"a": {"c": 2}}),
        ),
        (json!({"a": [1]}), "a[0]", json!({})),
        (json!({"a": [1, 2]}), "a[0]", json!({"a": [null, 2]})),
        (json!({"a": [{"b": 1}]}), "a[0].b", json!({})),
        (json!({"a": 3}), "a.b", json!({"a": 3})),
        (json!({"a": {"b": 1}}), "a.x", json!({"a": {"b": 1}})),
        (json!({"a": {}}), "a.x", json!({"a": {}})),
        (json!({"a": [null]}), "a[0]", json!({"a": [null]})),
        (json!({"Ab": 1, "ab": 2}), "ab", json!({"Ab": 1})),
        (json!({"a": [{}]}), "a[0].x", json!({"a": [{}]})),
    ] {
        let mut map = map_of(input);
        path::remove(&mut map, &segments(path_text));
        assert_eq!(make_value(map), Value::from(expected), "{path_text}");
    }
    for (prune, expected) in [(true, json!({})), (false, json!({"a": {}}))] {
        let mut object = Value::from(json!({"a": {"b": 1}}));
        let emptied = path::remove_object(object.as_object_mut().unwrap(), &segments("a.b"), prune);
        assert_eq!(emptied, prune);
        assert_eq!(object, Value::from(expected));
    }
}

#[test]
fn can_set_requires_compatible_shapes() {
    let map = map_of(json!({"a": {"b": 1}, "n": null, "arr": [1]}));
    for (path_text, expected) in [
        ("x.y", true),
        ("A.c", true),
        ("a.b", true),
        ("a.b.c", false),
        ("n.x[0]", true),
        ("arr[3]", true),
        ("x[4095]", true),
        ("arr.x", false),
        ("a[0]", false),
        ("arr[0].x", false),
    ] {
        assert_eq!(
            path::can_set(&map, &segments(path_text)),
            expected,
            "{path_text}"
        );
    }
    let too_far = [
        Segment::Key(crate::Rc::from("x")),
        Segment::Index(path::MAX_INDEX + 1),
    ];
    assert!(!path::can_set(&map, &too_far));
    let wildcard = path::parse("x[*]").unwrap();
    assert!(!path::can_set(&map, &wildcard.segments));
    let object = Value::from(json!({"A": 1}));
    let object = object.as_object().unwrap();
    assert!(path::can_set_object(object, &segments("b.c")));
    assert!(!path::can_set_object(object, &segments("a.c")));
}

#[test]
fn set_object_writes_inside_element_objects() {
    let mut object = Value::from(json!({"Tags": {"x": 1}}));
    let inner = object.as_object_mut().unwrap();
    path::set_object(inner, &segments("tags.y"), Value::from(2), true);
    path::set_object(inner, &segments("New[1]"), Value::from(3), true);
    assert_eq!(
        object,
        Value::from(json!({"Tags": {"x": 1, "y": 2}, "new": [null, 3]}))
    );
}

#[test]
fn index_padding_is_bounded() {
    assert!(path::scalar_segments("a[1000000000]").is_none());
    assert!(path::scalar_segments("a[99999999999999999999999999999]").is_none());
    assert!(path::scalar_segments("a[2]").is_some());
    let segments = vec![
        path::Segment::Key(crate::Rc::from("a")),
        path::Segment::Index(1000000000),
    ];
    let mut map = new_map();
    path::set(&mut map, &segments, Value::from(1), false);
    assert_eq!(make_value(map), Value::from(json!({})));
}

#[test]
fn set_pads_indices_and_keeps_dotted_keys() {
    let mut map = new_map();
    path::set(
        &mut map,
        &path::scalar_segments("a[2]['Key.With.Dot']").unwrap(),
        Value::from(7),
        false,
    );
    assert_eq!(
        make_value(map),
        Value::from(json!({"a": [null, null, {"Key.With.Dot": 7}]}))
    );
}

#[test]
fn set_replaces_null_with_containers() {
    for (input, path_text, expected) in [
        (json!({"a": null}), "a.b", json!({"a": {"b": 1}})),
        (json!({"a": null}), "a[1]", json!({"a": [null, 1]})),
        (json!({"a": [null]}), "a[0].b", json!({"a": [{"b": 1}]})),
        (json!({"a": [null]}), "a[0][1]", json!({"a": [[null, 1]]})),
        (json!({"a": 3}), "a.b", json!({"a": 3})),
    ] {
        let mut map = new_map();
        for (key, value) in input.as_object().unwrap() {
            map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
        }
        path::set(
            &mut map,
            &path::scalar_segments(path_text).unwrap(),
            Value::from(1),
            false,
        );
        assert_eq!(make_value(map), Value::from(expected), "{path_text}");
    }
}

#[test]
fn rename_guards() {
    for (input, source, target, expected) in [
        (json!({"a": 1, "b": 2}), "a", "b", json!({"a": 1, "b": 2})),
        (json!({"a": 1}), "a", "A", json!({"a": 1})),
        (json!({"a": 1, "b": 2}), "a", "b.c", json!({"a": 1, "b": 2})),
        (json!({"b": 2}), "a", "c", json!({"b": 2})),
        (json!({"a": 1}), "a[*]", "c", json!({"a": 1})),
        (json!({"a": {"x": 1}}), "a.x", "b[0]", json!({"b": [1]})),
    ] {
        let mut map = new_map();
        for (key, value) in input.as_object().unwrap() {
            map.insert(crate::Rc::from(key.as_str()), Value::from(value.clone()));
        }
        path::rename(&mut map, source, target, false);
        assert_eq!(
            make_value(map),
            Value::from(expected),
            "{source} -> {target}"
        );
    }
}

#[test]
fn index_bound_is_inclusive_at_max() {
    assert!(path::scalar_segments("a[4095]").is_some());
    assert!(path::scalar_segments("a[4096]").is_none());
    let mut map = new_map();
    path::set(
        &mut map,
        &path::scalar_segments("a[4095]").unwrap(),
        Value::from(1),
        false,
    );
    let value = make_value(map);
    let array = value
        .as_object()
        .unwrap()
        .get(&Value::from("a"))
        .unwrap()
        .as_array()
        .unwrap();
    assert_eq!(array.len(), 4096);
}

#[test]
fn case_variant_keys_resolve_to_smallest_match() {
    for _ in 0..8 {
        let map = map_of(json!({"aB": 2, "Ab": 1}));
        assert_eq!(path::get_map(&map, &segments("ab")), Some(&Value::from(1)));
        let mut removed = map.clone();
        path::remove(&mut removed, &segments("AB"));
        assert_eq!(make_value(removed), Value::from(json!({"aB": 2})));
        let mut written = map;
        path::set(&mut written, &segments("ab"), Value::from(3), false);
        assert_eq!(make_value(written), Value::from(json!({"Ab": 3, "aB": 2})));
    }
}

#[test]
fn set_rejects_wildcards_without_writing() {
    let wildcard = path::parse("a[*].b").unwrap();
    let mut map = new_map();
    path::set(&mut map, &wildcard.segments, Value::from(1), false);
    assert_eq!(make_value(map), Value::from(json!({})));
    let mut object = Value::from(json!({}));
    path::set_object(
        object.as_object_mut().unwrap(),
        &wildcard.segments,
        Value::from(1),
        false,
    );
    assert_eq!(object, Value::from(json!({})));
}

#[test]
fn exact_key_wins_over_case_variant() {
    let map = map_of(json!({"Ab": 1, "ab": 2}));
    assert_eq!(path::get_map(&map, &segments("ab")), Some(&Value::from(2)));
    let mut written = map;
    path::set(&mut written, &segments("ab"), Value::from(3), false);
    assert_eq!(make_value(written), Value::from(json!({"Ab": 1, "ab": 3})));
    let mut object = Value::from(json!({"Ab": 1, "ab": 2}));
    assert_eq!(
        path::get(&object, &segments("ab"), true),
        Some(&Value::from(2))
    );
    let inner = object.as_object_mut().unwrap();
    path::set_object(inner, &segments("ab"), Value::from(3), false);
    path::remove_object(inner, &segments("Ab"), true);
    assert_eq!(object, Value::from(json!({"ab": 3})));
}

#[test]
fn unpruned_array_removal_keeps_nulls() {
    let mut object = Value::from(json!({"a": [1]}));
    assert!(!path::remove_object(
        object.as_object_mut().unwrap(),
        &segments("a[0]"),
        false
    ));
    assert_eq!(object, Value::from(json!({"a": [null]})));
}

#[test]
fn rename_lowercases_new_keys() {
    let mut map = map_of(json!({"a": 1}));
    path::rename(&mut map, "a", "New.Key", true);
    assert_eq!(make_value(map), Value::from(json!({"new": {"key": 1}})));
}
