// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Representation-independent mathematical values for history correctness.
//! Collection-private shallow views live in their owning modules.

use super::value_numeric::numeric_of;
use super::value_numeric::Numeric;
use crate::value::{Array, Object, Set as ValueSet};
use crate::{Rc, Value};
use vstd::prelude::*;

verus! {

pub enum Data {
    Null,
    Bool(bool),
    Number(Numeric),
    String(Seq<char>),
    Array(Seq<Data>),
    Set(Set<Data>),
    Object(Map<Data, Data>),
    Undefined,
}

impl vstd::std_specs::cmp::PartialEqSpecImpl for Value {
    open spec fn obeys_eq_spec() -> bool { true }
    open spec fn eq_spec(&self, other: &Self) -> bool {
        value_view(*self) == value_view(*other)
    }
}

pub open spec fn value_view(v: Value) -> Data decreases v, 1nat, 0nat {
    match v {
        Value::Null => Data::Null,
        Value::Bool(b) => Data::Bool(b),
        Value::Number(n) => Data::Number(numeric_of(n@)),
        Value::String(s) => Data::String(s@),
        Value::Array(a) => Data::Array(values_view(v, a@)),
        Value::Set(s) => Data::Set(set_view(v, s@)),
        Value::Object(o) => Data::Object(object_view(v, o@, o@.dom())),
        Value::Undefined => Data::Undefined,
    }
}

pub open spec fn values_view(bound: Value, s: Seq<Value>) -> Seq<Data>
    decreases bound, 0nat, s.len(),
    when forall|i: int| 0 <= i < s.len() ==> is_smaller_than(s[i], bound)
{
    if s.len() == 0 { Seq::empty() }
    else { values_view(bound, s.drop_last()).push(value_view(s.last())) }
}

pub open spec fn set_view(bound: Value, s: Set<Value>) -> Set<Data>
    decreases bound, 0nat, s.len(),
    when forall|x: Value| s.contains(x) ==> is_smaller_than(x, bound)
{
    if s.is_empty() { Set::empty() }
    else {
        let x = s.choose();
        set_view(bound, s.remove(x)).insert(value_view(x))
    }
}

pub open spec fn object_view(bound: Value, m: Map<Value, Value>, keys: Set<Value>) -> Map<Data, Data>
    decreases bound, 0nat, keys.len(),
    when keys.subset_of(m.dom()) && forall|k: Value| m.dom().contains(k)
        ==> is_smaller_than(k, bound) && is_smaller_than(m[k], bound)
{
    if keys.is_empty() { Map::empty() }
    else {
        let k = keys.choose();
        object_view(bound, m, keys.remove(k)).insert(value_view(k), value_view(m[k]))
    }
}

pub proof fn lemma_array_elems_smaller(a: Rc<Array>)
    ensures forall|i: int| 0 <= i < a@.len()
        ==> is_smaller_than(a@[i], Value::Array(a)),
{
    Array::lemma_elems_smaller(a);
}

pub proof fn lemma_set_elems_smaller(s: Rc<ValueSet>)
    ensures forall|x: Value| s@.contains(x) ==> is_smaller_than(x, Value::Set(s)),
{
    ValueSet::lemma_elems_smaller(s);
}

pub proof fn lemma_object_entries_smaller(o: Rc<Object>)
    ensures forall|k: Value| o@.contains_key(k)
        ==> is_smaller_than(k, Value::Object(o)) && is_smaller_than(o@[k], Value::Object(o)),
{
    Object::lemma_entries_smaller(o);
}

pub proof fn lemma_values_view(bound: Value, s: Seq<Value>)
    requires forall|i: int| 0 <= i < s.len() ==> is_smaller_than(s[i], bound),
    ensures
        values_view(bound, s).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> values_view(bound, s)[i] == value_view(s[i]),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_values_view(bound, s.drop_last());
        assert forall|i: int| 0 <= i < s.len()
            implies values_view(bound, s)[i] == value_view(s[i]) by {
            if i < s.len() - 1 { assert(s.drop_last()[i] == s[i]); }
        }
    }
}

pub proof fn lemma_value_view_array(a: Rc<Array>)
    ensures
        value_view(Value::Array(a)) is Array,
        (match value_view(Value::Array(a)) {
            Data::Array(xs) => xs.len() == a@.len()
                && forall|i: int| 0 <= i < xs.len() ==> xs[i] == value_view(a@[i]),
            _ => false,
        }),
{
    lemma_array_elems_smaller(a);
    lemma_values_view(Value::Array(a), a@);
}

pub proof fn lemma_set_view(bound: Value, s: Set<Value>)
    requires
        forall|x: Value| s.contains(x) ==> is_smaller_than(x, bound),
    ensures forall|d: Data| set_view(bound, s).contains(d)
        <==> exists|x: Value| s.contains(x) && value_view(x) == d,
    decreases s.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    if !s.is_empty() {
        let x = s.choose();
        lemma_set_view(bound, s.remove(x));
        assert forall|d: Data| set_view(bound, s).contains(d)
            <==> (exists|v: Value| s.contains(v) && value_view(v) == d) by {
            if set_view(bound, s).contains(d) {
                if d == value_view(x) {
                    assert(s.contains(x) && value_view(x) == d);
                } else {
                    assert(set_view(bound, s.remove(x)).contains(d));
                    let v = choose|v: Value| s.remove(x).contains(v) && value_view(v) == d;
                    assert(s.contains(v) && value_view(v) == d);
                }
            }
            if exists|v: Value| s.contains(v) && value_view(v) == d {
                let v = choose|v: Value| s.contains(v) && value_view(v) == d;
                if v != x { assert(s.remove(x).contains(v)); }
            }
        }
    }
}

pub proof fn lemma_value_view_set(s: Rc<ValueSet>)
    ensures match value_view(Value::Set(s)) {
        Data::Set(ds) => forall|d: Data| ds.contains(d)
            <==> exists|x: Value| s@.contains(x) && value_view(x) == d,
        _ => false,
    },
{
    lemma_set_elems_smaller(s);
    lemma_set_view(Value::Set(s), s@);
    assert(value_view(Value::Set(s)) == Data::Set(set_view(Value::Set(s), s@)));
    assert forall|d: Data| set_view(Value::Set(s), s@).contains(d)
        <==> (exists|x: Value| s@.contains(x) && value_view(x) == d) by {
    }
}

pub proof fn lemma_object_view_domain(bound: Value, m: Map<Value, Value>, keys: Set<Value>)
    requires
        keys.subset_of(m.dom()),
        forall|k: Value| m.dom().contains(k)
            ==> is_smaller_than(k, bound) && is_smaller_than(m[k], bound),
    ensures forall|dk: Data| object_view(bound, m, keys).contains_key(dk)
        <==> exists|k: Value| keys.contains(k) && value_view(k) == dk,
    decreases keys.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    if !keys.is_empty() {
        let k = keys.choose();
        lemma_object_view_domain(bound, m, keys.remove(k));
        assert forall|dk: Data| object_view(bound, m, keys).contains_key(dk)
            <==> (exists|v: Value| keys.contains(v) && value_view(v) == dk) by {
            if object_view(bound, m, keys).contains_key(dk) {
                if dk == value_view(k) {
                    assert(keys.contains(k) && value_view(k) == dk);
                } else {
                    assert(object_view(bound, m, keys.remove(k)).contains_key(dk));
                    let v = choose|v: Value| keys.remove(k).contains(v) && value_view(v) == dk;
                    assert(keys.contains(v) && value_view(v) == dk);
                }
            }
            if exists|v: Value| keys.contains(v) && value_view(v) == dk {
                let v = choose|v: Value| keys.contains(v) && value_view(v) == dk;
                if v != k {
                    assert(keys.remove(k).contains(v));
                    assert(object_view(bound, m, keys.remove(k)).contains_key(value_view(v)));
                }
            }
        }
    }
}

pub proof fn lemma_object_view_entries(bound: Value, m: Map<Value, Value>, keys: Set<Value>)
    requires
        keys.subset_of(m.dom()),
        forall|k: Value| m.dom().contains(k)
            ==> is_smaller_than(k, bound) && is_smaller_than(m[k], bound),
        forall|k1: Value, k2: Value| keys.contains(k1) && keys.contains(k2)
            && value_view(k1) == value_view(k2) ==> k1 == k2,
    ensures forall|k: Value| keys.contains(k)
        ==> object_view(bound, m, keys)[value_view(k)] == value_view(m[k]),
    decreases keys.len(),
{
    broadcast use vstd::set::group_set_lemmas;
    if !keys.is_empty() {
        let k = keys.choose();
        lemma_object_view_entries(bound, m, keys.remove(k));
        assert forall|v: Value| keys.contains(v)
            implies object_view(bound, m, keys)[value_view(v)] == value_view(m[v]) by {
            if v != k {
                assert(value_view(v) != value_view(k));
                assert(keys.remove(k).contains(v));
            }
        }
    }
}

pub proof fn lemma_value_view_object(o: Rc<Object>)
    ensures match value_view(Value::Object(o)) {
        Data::Object(m) =>
            (forall|dk: Data| m.contains_key(dk)
                <==> exists|k: Value| o@.contains_key(k) && value_view(k) == dk)
            && ((forall|k1: Value, k2: Value| o@.contains_key(k1) && o@.contains_key(k2)
                && value_view(k1) == value_view(k2) ==> k1 == k2)
                ==> forall|k: Value| o@.contains_key(k)
                    ==> m[value_view(k)] == value_view(o@[k])),
        _ => false,
    },
{
    lemma_object_entries_smaller(o);
    lemma_object_view_domain(Value::Object(o), o@, o@.dom());
    if forall|k1: Value, k2: Value| o@.contains_key(k1) && o@.contains_key(k2)
        && value_view(k1) == value_view(k2) ==> k1 == k2 {
        lemma_object_view_entries(Value::Object(o), o@, o@.dom());
    }
}

pub open spec fn history_view(h: Rc<Array>) -> Seq<Data> {
    match value_view(Value::Array(h)) {
        Data::Array(xs) => xs,
        _ => Seq::empty(),
    }
}

}
