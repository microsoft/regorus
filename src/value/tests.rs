// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::expect_used,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::arithmetic_side_effects,
    clippy::unseparated_literal_suffix,
    clippy::map_unwrap_or,
    clippy::option_if_let_else,
    clippy::pattern_type_mismatch
)]

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::vec::Vec;

use super::Object;
use crate::value::Value;

fn val(i: u64) -> Value {
    Value::from(i)
}

fn make_pairs(n: u64) -> Vec<(Value, Value)> {
    (0..n).map(|i| (val(i), val(i.saturating_mul(2)))).collect()
}

const SIZES: &[u64] = &[0, 1, 2, 4, 8, 64, 256, 1024];

/// `iter_sorted` must yield entries in the same order as a `BTreeMap` oracle.
#[test]
fn object_iter_sorted_matches_btreemap_oracle() {
    for &n in SIZES {
        let pairs = make_pairs(n);
        let oracle: BTreeMap<Value, Value> = pairs.iter().cloned().collect();
        let obj: Object = pairs.into_iter().collect();
        let actual: Vec<(&Value, &Value)> = obj.iter_sorted().collect();
        let expected: Vec<(&Value, &Value)> = oracle.iter().collect();
        assert_eq!(actual, expected, "size {n}");
    }
}

/// `iter` may be in any order, but as a multiset must equal the oracle's entries.
#[test]
fn object_iter_multiset_equality_with_oracle() {
    for &n in SIZES {
        let pairs = make_pairs(n);
        let oracle: BTreeMap<Value, Value> = pairs.iter().cloned().collect();
        let obj: Object = pairs.into_iter().collect();
        assert_eq!(obj.len(), oracle.len(), "size {n}");
        let mut a: Vec<(Value, Value)> = obj.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        let mut b: Vec<(Value, Value)> =
            oracle.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        a.sort();
        b.sort();
        assert_eq!(a, b);
    }
}

/// Serialize-then-deserialize must round-trip through JSON without loss.
#[test]
fn object_serde_roundtrip() {
    for &n in &[0_u64, 1, 8, 64] {
        let pairs: Vec<(Value, Value)> = (0..n)
            .map(|i| (Value::String(format!("k{i}").into()), val(i)))
            .collect();
        let obj: Object = pairs.into_iter().collect();
        let json = serde_json::to_string(&obj).expect("ser");
        let back: Object = serde_json::from_str(&json).expect("de");
        assert_eq!(obj, back, "size {n}");
    }
}

/// Equality depends only on contents, not the order keys were inserted.
#[test]
fn object_eq_invariant_to_insertion_order() {
    let mut a = Object::new();
    let mut b = Object::new();
    for i in 0..32_u64 {
        a.insert(val(i), val(i.saturating_add(1)));
    }
    for i in (0..32_u64).rev() {
        b.insert(val(i), val(i.saturating_add(1)));
    }
    assert_eq!(a, b);
}

/// `remove` returns the prior value (or `None`) and `retain` keeps only matching entries.
#[test]
fn object_remove_and_retain() {
    let mut obj: Object = make_pairs(16).into_iter().collect();
    assert_eq!(obj.remove(&val(0)), Some(val(0)));
    assert!(obj.remove(&val(100)).is_none());
    obj.retain(|_, v| {
        if let Value::Number(ref n) = *v {
            n.as_u64().is_some_and(|x| x % 4 == 0)
        } else {
            false
        }
    });
    for (_, v) in obj.iter_sorted() {
        if let Value::Number(ref n) = *v {
            assert_eq!(n.as_u64().expect("u64") % 4, 0);
        }
    }
}

/// `IntoIterator` for `Object` (by value) yields every entry exactly once.
#[test]
fn object_into_iterator_owned() {
    let obj: Object = make_pairs(8).into_iter().collect();
    let collected: Vec<(Value, Value)> = obj.into_iter().collect();
    assert_eq!(collected.len(), 8);
}

// ---- Duplicate-key semantics --------------------------------------------

/// `FromIterator` keeps the last value when the same key appears multiple times.
#[test]
fn object_from_iter_last_wins_on_duplicate_keys() {
    let obj = Object::from_iter([(val(0), val(1)), (val(0), val(2))]);
    assert_eq!(obj.get(&val(0)), Some(&val(2)));
    assert_eq!(obj.len(), 1);
}

/// `From<BTreeMap>` adopts `BTreeMap`'s own last-write-wins semantics for duplicates.
#[test]
fn object_from_btreemap_last_wins_on_duplicate_keys() {
    let mut bm: BTreeMap<Value, Value> = BTreeMap::new();
    bm.insert(val(0), val(1));
    bm.insert(val(0), val(2));
    let obj: Object = bm.into();
    assert_eq!(obj.get(&val(0)), Some(&val(2)));
    assert_eq!(obj.len(), 1);
}

// ---- get_or_insert_with --------------------------------------------------

/// `get_or_insert_with` inserts the default when the key is absent and returns a mutable ref to it.
#[test]
fn object_get_or_insert_with_inserts_when_absent() {
    let mut obj = Object::new();
    let v = obj.get_or_insert_with(val(7), || val(42));
    assert_eq!(*v, val(42));
    *v = val(43);
    assert_eq!(obj.get(&val(7)), Some(&val(43)));
}

/// `get_or_insert_with` returns the existing value and never invokes the default closure.
#[test]
fn object_get_or_insert_with_returns_existing_when_present() {
    let mut obj = Object::new();
    obj.insert(val(7), val(1));
    let mut closure_called = false;
    let v = obj.get_or_insert_with(val(7), || {
        closure_called = true;
        val(999)
    });
    assert_eq!(*v, val(1));
    assert!(!closure_called, "default closure must not run when present");
}

// ---- Accessor coverage ---------------------------------------------------

/// Smoke-test every accessor: `contains_key`/`get`/`get_mut`/`keys`/`values`/`iter`/`iter_mut`/`append`/`clear`.
#[test]
fn object_accessor_coverage() {
    let mut obj: Object = make_pairs(4).into_iter().collect();

    assert!(obj.contains_key(&val(0)));
    assert!(!obj.contains_key(&val(100)));

    assert_eq!(obj.get(&val(2)), Some(&val(4)));

    if let Some(v) = obj.get_mut(&val(1)) {
        *v = val(999);
    }
    assert_eq!(obj.get(&val(1)), Some(&val(999)));

    let keys: Vec<&Value> = obj.keys().collect();
    assert_eq!(keys.len(), 4);
    let values: Vec<&Value> = obj.values().collect();
    assert_eq!(values.len(), 4);

    for (_, v) in obj.iter_mut() {
        *v = val(0);
    }
    for (_, v) in obj.iter() {
        assert_eq!(*v, val(0));
    }

    let mut other = Object::new();
    other.insert(val(100), val(200));
    obj.append(&mut other);
    assert!(other.is_empty());
    assert!(obj.contains_key(&val(100)));

    obj.clear();
    assert!(obj.is_empty());
}

// ---- IntoIterator for references -----------------------------------------

/// `IntoIterator` for `&Object` yields shared refs to every entry.
#[test]
fn object_into_iterator_ref() {
    let obj: Object = make_pairs(4).into_iter().collect();
    let mut count = 0;
    for (_k, _v) in &obj {
        count += 1;
    }
    assert_eq!(count, 4);
}

/// `IntoIterator` for `&mut Object` exposes mutable refs to values; mutations persist.
#[test]
fn object_into_iterator_ref_mut() {
    let mut obj: Object = make_pairs(4).into_iter().collect();
    for (_k, v) in &mut obj {
        *v = val(0);
    }
    for (_, v) in obj.iter() {
        assert_eq!(*v, val(0));
    }
}

// ---- Cursor tests --------------------------------------------------------

/// Driving `cursor`+`next` to completion visits each entry exactly once.
#[test]
fn object_cursor_yields_every_entry_once() {
    for &n in SIZES {
        let pairs = make_pairs(n);
        let obj: Object = pairs.clone().into_iter().collect();
        let mut cursor = obj.cursor();
        let mut collected: Vec<(Value, Value)> = Vec::new();
        while let Some((k, v)) = obj.next(&mut cursor) {
            collected.push((k.clone(), v.clone()));
        }
        let mut a = collected;
        a.sort();
        let mut b = pairs;
        b.sort();
        assert_eq!(a, b, "size {n}");
    }
}

/// A freshly-constructed cursor restarts from the beginning, independent of any prior cursor's state.
#[test]
fn object_cursor_resumable_fresh_cursor_restarts() {
    let obj: Object = make_pairs(8).into_iter().collect();
    let mut c1 = obj.cursor();
    let _ = obj.next(&mut c1);
    let _ = obj.next(&mut c1);
    let mut c2 = obj.cursor();
    let first_again = obj.next(&mut c2);
    let first_original = obj.iter().next();
    assert_eq!(
        first_again.map(|(k, v)| (k.clone(), v.clone())),
        first_original.map(|(k, v)| (k.clone(), v.clone()))
    );
}

/// When `Object` is shared via `Rc`, `Rc::make_mut` clones — leaving an in-flight cursor on the original snapshot unaffected.
#[test]
fn object_cursor_snapshot_independence_via_rc() {
    use crate::Rc;
    let mut obj = Object::new();
    obj.insert(Value::from("a"), Value::from(1));
    obj.insert(Value::from("b"), Value::from(2));
    obj.insert(Value::from("c"), Value::from(3));
    let rc_obj = Rc::new(obj);

    let alias = Rc::clone(&rc_obj);
    let mut cursor = rc_obj.cursor();
    let _ = rc_obj.next(&mut cursor);

    let mut alias_for_mut = alias;
    Rc::make_mut(&mut alias_for_mut).insert(Value::from("d"), Value::from(4));
    Rc::make_mut(&mut alias_for_mut).remove(&Value::from("a"));

    assert_eq!(rc_obj.len(), 3);
    let mut remaining = 0;
    while rc_obj.next(&mut cursor).is_some() {
        remaining += 1;
    }
    assert_eq!(remaining, 2);
}

/// A cursor over an empty `Object` returns `None` on the first call.
#[test]
fn object_cursor_empty_returns_none_immediately() {
    let obj = Object::new();
    let mut cursor = obj.cursor();
    assert!(obj.next(&mut cursor).is_none());
}

/// Mutating an `Object` between `next()` calls is well-defined: the cursor
/// must not panic and must terminate. The visit order, and whether
/// inserted/removed keys appear, is intentionally unspecified — this test
/// only pins the safety + termination guarantees that callers (e.g. a
/// future RVM iteration frame) may rely on. It must NOT assert any
/// particular order or count, or future backend swaps will be forced to
/// honor an accidental contract.
#[test]
fn object_cursor_mutation_between_steps_is_safe_and_terminates() {
    let mut obj: Object = make_pairs(16).into_iter().collect();
    let mut cursor = obj.cursor();

    // Yield a few entries before mutating.
    for _ in 0..3 {
        let _ = obj.next(&mut cursor);
    }

    // Interleave mutations and steps. Each yielded entry must, at the
    // moment of yield, be a real entry in the map.
    obj.insert(val(100), val(100));
    if let Some((k, v)) = obj.next(&mut cursor) {
        assert_eq!(obj.get(k), Some(v));
    }
    obj.remove(&val(2));
    if let Some((k, v)) = obj.next(&mut cursor) {
        assert_eq!(obj.get(k), Some(v));
    }
    obj.clear();
    // After clear(), draining the cursor must terminate (not panic, not
    // loop) within a bounded number of calls.
    let mut terminated = false;
    for _ in 0..32 {
        if obj.next(&mut cursor).is_none() {
            terminated = true;
            break;
        }
    }
    assert!(terminated, "cursor failed to terminate after clear()");
}

// ---- Hand-written Ord consistency ---------------------------------------

/// `Ord` (built atop `iter_sorted`) is invariant to insertion order.
#[test]
fn object_ord_invariant_to_insertion_order() {
    let mut a = Object::new();
    let mut b = Object::new();
    for i in 0..16_u64 {
        a.insert(val(i), val(i.saturating_add(1)));
    }
    for i in (0..16_u64).rev() {
        b.insert(val(i), val(i.saturating_add(1)));
    }
    use core::cmp::Ordering;
    assert_eq!(a.cmp(&b), Ordering::Equal);
}

/// `Ord` agrees with lexicographic comparison of the sorted-entries view.
#[test]
fn object_ord_lexicographic_on_sorted_entries() {
    let a: Object = [(val(0), val(0)), (val(1), val(1))].into_iter().collect();
    let b: Object = [(val(0), val(0)), (val(2), val(2))].into_iter().collect();
    assert!(a < b);
}

/// `empty < non_empty` and a shorter prefix compares less than its extension.
#[test]
fn object_ord_empty_and_prefix() {
    use core::cmp::Ordering;
    let empty = Object::new();
    let one: Object = [(val(0), val(0))].into_iter().collect();
    let two: Object = [(val(0), val(0)), (val(1), val(1))].into_iter().collect();
    assert_eq!(empty.cmp(&one), Ordering::Less);
    assert_eq!(one.cmp(&two), Ordering::Less);
    assert_eq!(two.cmp(&empty), Ordering::Greater);
}

/// When keys match, `Ord` falls through to comparing values.
#[test]
fn object_ord_breaks_ties_on_values() {
    use core::cmp::Ordering;
    let a: Object = [(val(0), val(1))].into_iter().collect();
    let b: Object = [(val(0), val(2))].into_iter().collect();
    assert_eq!(a.cmp(&b), Ordering::Less);
}

/// `PartialOrd` must agree with `Ord` for every input pair.
#[test]
fn object_partial_cmp_matches_cmp() {
    let a: Object = [(val(0), val(0)), (val(1), val(1))].into_iter().collect();
    let b: Object = [(val(0), val(0)), (val(2), val(2))].into_iter().collect();
    assert_eq!(a.partial_cmp(&b), Some(a.cmp(&b)));
    assert_eq!(b.partial_cmp(&a), Some(b.cmp(&a)));
    assert_eq!(a.partial_cmp(&a), Some(core::cmp::Ordering::Equal));
}

// ---- Debug / keys_sorted determinism ------------------------------------

/// `Debug` output is byte-identical for equal Objects regardless of insertion order.
#[test]
fn object_debug_invariant_to_insertion_order() {
    let mut a = Object::new();
    let mut b = Object::new();
    for i in 0..8_u64 {
        a.insert(val(i), val(i));
    }
    for i in (0..8_u64).rev() {
        b.insert(val(i), val(i));
    }
    assert_eq!(format!("{a:?}"), format!("{b:?}"));
}

/// `keys_sorted` yields exactly `iter_sorted().map(|(k,_)| k)`.
#[test]
fn object_keys_sorted_matches_iter_sorted_keys() {
    let obj: Object = make_pairs(16).into_iter().collect();
    let from_keys: Vec<&Value> = obj.keys_sorted().collect();
    let from_iter: Vec<&Value> = obj.iter_sorted().map(|(k, _)| k).collect();
    assert_eq!(from_keys, from_iter);
}

// ---- Serde: non-string keys & determinism --------------------------------

/// `Serialize` stringifies non-string keys, and equal Objects produce identical JSON
/// regardless of insertion order.
#[test]
fn object_serialize_non_string_keys_and_deterministic() {
    let pairs = [
        (Value::from("alpha"), val(1)),
        (Value::Bool(true), val(2)),
        (val(7), val(3)),
    ];
    let a: Object = pairs.iter().cloned().collect();
    let mut b = Object::new();
    for (k, v) in pairs.iter().rev().cloned() {
        b.insert(k, v);
    }
    let ja = serde_json::to_string(&a).expect("ser a");
    let jb = serde_json::to_string(&b).expect("ser b");
    assert_eq!(ja, jb, "serialization must be deterministic");

    // Non-string keys appear as quoted strings in the resulting JSON.
    let v: serde_json::Value = serde_json::from_str(&ja).expect("parse");
    let obj = v.as_object().expect("json object");
    assert!(
        obj.contains_key("true"),
        "bool key was not stringified: {ja}"
    );
    assert!(
        obj.contains_key("7"),
        "number key was not stringified: {ja}"
    );
    assert!(obj.contains_key("alpha"));
}

// ---- Extend / append duplicate-key semantics -----------------------------

/// `extend` overwrites existing entries (last-write-wins) and preserves length when
/// only existing keys are touched.
#[test]
fn object_extend_last_wins_and_empty_noop() {
    let mut obj: Object = [(val(0), val(0)), (val(1), val(1))].into_iter().collect();
    obj.extend([(val(0), val(99))]);
    assert_eq!(obj.get(&val(0)), Some(&val(99)));
    assert_eq!(obj.len(), 2);

    let before = obj.len();
    obj.extend(core::iter::empty::<(Value, Value)>());
    assert_eq!(obj.len(), before, "empty extend is a no-op");
}

/// `append` drains `other` into `self`, overwriting on overlapping keys.
#[test]
fn object_append_overlapping_keys_drain_and_overwrite() {
    let mut a: Object = [(val(0), val(0)), (val(1), val(1))].into_iter().collect();
    let mut b: Object = [(val(1), val(99)), (val(2), val(2))].into_iter().collect();
    a.append(&mut b);
    assert!(b.is_empty(), "append must drain `other`");
    assert_eq!(a.len(), 3);
    assert_eq!(a.get(&val(1)), Some(&val(99)));
    assert_eq!(a.get(&val(2)), Some(&val(2)));
}

// ---- Iterator trait surface ---------------------------------------------

/// `DoubleEndedIterator`/`ExactSizeIterator`/`FusedIterator` and `size_hint` all
/// behave correctly across partial consumption from both ends.
#[test]
fn object_iter_sorted_double_ended_and_exact_size() {
    let obj: Object = make_pairs(4).into_iter().collect();
    let mut it = obj.iter_sorted();
    assert_eq!(it.len(), 4);
    assert_eq!(it.size_hint(), (4, Some(4)));

    let first = it.next().expect("front");
    let last = it.next_back().expect("back");
    assert_eq!(it.len(), 2);
    assert_eq!(it.size_hint(), (2, Some(2)));
    assert_ne!(first.0, last.0, "front and back must differ for n=4");

    // Drain remaining.
    while it.next().is_some() {}
    assert_eq!(it.len(), 0);
    // FusedIterator: stays None after exhaustion.
    assert!(it.next().is_none());
    assert!(it.next().is_none());
    assert!(it.next_back().is_none());
}

/// `IntoIter` also honors `DoubleEndedIterator` and `ExactSizeIterator`.
#[test]
fn object_into_iter_double_ended_and_exact_size() {
    let obj: Object = make_pairs(4).into_iter().collect();
    let mut it = obj.into_iter();
    assert_eq!(it.len(), 4);
    let _ = it.next().expect("front");
    let _ = it.next_back().expect("back");
    assert_eq!(it.len(), 2);
    let collected: Vec<_> = it.collect();
    assert_eq!(collected.len(), 2);
}

/// `IterMut` decrements its `len()` after consuming from the front.
#[test]
fn object_iter_mut_exact_size() {
    let mut obj: Object = make_pairs(3).into_iter().collect();
    let mut it = obj.iter_mut();
    assert_eq!(it.len(), 3);
    let _ = it.next().expect("front");
    assert_eq!(it.len(), 2);
}

/// `Iter` is `Clone`; the clone iterates independently from the same point.
#[test]
fn object_iter_sorted_clone_is_independent() {
    let obj: Object = make_pairs(4).into_iter().collect();
    let mut a = obj.iter_sorted();
    let _ = a.next();
    let b = a.clone();
    let rest_a: Vec<_> = a.collect();
    let rest_b: Vec<_> = b.collect();
    assert_eq!(rest_a, rest_b);
}

// ---- default / insert ---------------------------------------------------

/// `Object::default()` and `Object::new()` produce equal, empty Objects.
#[test]
fn object_default_equals_new_and_is_empty() {
    let a = Object::default();
    let b = Object::new();
    assert_eq!(a, b);
    assert!(a.is_empty());
    assert_eq!(a.len(), 0);
}

/// `insert` returns `None` for a fresh key and `Some(old)` when overwriting.
#[test]
fn object_insert_returns_previous_value() {
    let mut obj = Object::new();
    assert_eq!(obj.insert(val(0), val(1)), None);
    assert_eq!(obj.insert(val(0), val(2)), Some(val(1)));
    assert_eq!(obj.get(&val(0)), Some(&val(2)));
}
