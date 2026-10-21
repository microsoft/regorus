// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Trusted value boundary: semantic Value equality and cloning; Array reads;
//! Object reads and sorted iteration; Set lookup; crate::Rc<Array> cloning and
//! pointer equality; Rc<str> and string operations not already specified by vstd.
//! BTree collections compare Value keys semantically, unlike vstd's structural
//! collection model. No history compilation or evaluation belongs here.

use super::value_specs::*;
use crate::value::{Array, Iter, Object, Set as ValueSet};
use crate::{Rc, Value};
use vstd::float::FloatBitsProperties;
use vstd::prelude::*;

verus! {

pub assume_specification[ <Value as PartialEq>::eq ](a: &Value, b: &Value) -> (r: bool)
    ensures r == (value_view(*a) == value_view(*b));

pub assume_specification[ <Value as Clone>::clone ](a: &Value) -> (r: Value)
    ensures value_view(r) == value_view(*a);

pub assume_specification[ Array::len ](a: &Array) -> (n: usize)
    ensures n == a@.len();

pub assume_specification[ Array::get ](a: &Array, i: usize) -> (r: Option<&Value>)
    ensures
        r is Some <==> i < a@.len(),
        r matches Some(v) ==> *v == a@[i as int];

pub assume_specification<'a>[ Array::as_slice ](a: &'a Array) -> (s: &'a [Value])
    ensures s@ == a@;

pub assume_specification[ Object::len ](o: &Object) -> (n: usize)
    ensures n == o@.dom().len();

pub assume_specification<'a>[ Object::get ](o: &'a Object, key: &Value) -> (r: Option<&'a Value>)
    ensures
        r is Some <==> exists|k: Value| o@.contains_key(k) && value_view(k) == value_view(*key),
        r matches Some(v) ==> exists|k: Value| o@.contains_key(k)
            && value_view(k) == value_view(*key) && *v == o@[k],
        forall|k1: Value, k2: Value| o@.contains_key(k1) && o@.contains_key(k2)
            && value_view(k1) == value_view(k2) ==> k1 == k2;

pub assume_specification<'a>[ ValueSet::get ](s: &'a ValueSet, key: &Value) -> (r: Option<&'a Value>)
    ensures
        r is Some <==> exists|x: Value| s@.contains(x) && value_view(x) == value_view(*key),
        r matches Some(v) ==> s@.contains(*v) && value_view(*v) == value_view(*key);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExObjectIter<'a>(Iter<'a>);

pub uninterp spec fn object_iter_remaining(it: Iter<'_>) -> Seq<(Value, Value)>;

pub assume_specification<'a>[ Object::iter_sorted ](o: &'a Object) -> (it: Iter<'a>)
    ensures
        object_iter_remaining(it).len() == o@.dom().len(),
        forall|i: int| 0 <= i < object_iter_remaining(it).len() ==> {
            let entry = #[trigger] object_iter_remaining(it)[i];
            o@.contains_key(entry.0) && o@[entry.0] == entry.1
        },
        forall|i: int, j: int| 0 <= i < object_iter_remaining(it).len()
            && 0 <= j < object_iter_remaining(it).len() && i != j
            ==> object_iter_remaining(it)[i].0 != object_iter_remaining(it)[j].0,
        // The same semantic-key uniqueness invariant used by Object::get.
        forall|k1: Value, k2: Value| o@.contains_key(k1) && o@.contains_key(k2)
            && value_view(k1) == value_view(k2) ==> k1 == k2,
        forall|k: Value| o@.contains_key(k) ==> exists|i: int|
            0 <= i < object_iter_remaining(it).len() && object_iter_remaining(it)[i].0 == k;

pub assume_specification<'a>[ <Iter<'a> as Iterator>::next ](it: &mut Iter<'a>)
    -> (r: Option<<Iter<'a> as Iterator>::Item>)
    ensures
        if object_iter_remaining(*old(it)).len() == 0 {
            r is None && object_iter_remaining(*final(it)) == Seq::<(Value, Value)>::empty()
        } else {
            r matches Some((k, v)) && (*k, *v) == object_iter_remaining(*old(it))[0]
                && object_iter_remaining(*final(it)) == object_iter_remaining(*old(it)).drop_first()
        };

pub assume_specification<T: ?Sized, A: core::alloc::Allocator>[ Rc::<T, A>::ptr_eq ](
    a: &Rc<T, A>, b: &Rc<T, A>,
) -> (r: bool)
    ensures r ==> *a == *b;

pub assume_specification<T: ?Sized, A: core::alloc::Allocator + Clone>[
    <Rc<T, A> as Clone>::clone
](a: &Rc<T, A>) -> (r: Rc<T, A>)
    ensures r == *a;

// Native bit projection; the payload includes the sign and every NaN payload bit.
pub assume_specification [ f64::to_bits ](f: f64) -> (res: u64)
    ensures res == f.to_bits_spec();

}
