// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::BTreeSet;
use core::cmp::Ordering;

use super::Array;
use crate::{Rc, Value};

/// One structural comparison, including arrays reached through objects or sets.
#[derive(Default)]
pub(super) struct Comparison {
    // Addresses identify completed comparisons, never equality by themselves.
    // All pointees remain borrowed and immutable until this context is dropped.
    equal_arrays: BTreeSet<(*const Array, *const Array)>,
    shared_ancestor: bool,
    equality: bool,
    #[cfg(test)]
    visits: usize,
}

impl Comparison {
    pub(super) fn equality() -> Self {
        Self {
            equality: true,
            ..Self::default()
        }
    }

    pub(super) fn arrays(&mut self, left: &Array, right: &Array) -> Ordering {
        if self.equality && left.len() != right.len() {
            return Ordering::Less;
        }
        self.sequence(left.iter(), right.iter())
    }

    fn values(&mut self, left: &Value, right: &Value) -> Ordering {
        #[cfg(test)]
        {
            self.visits = self.visits.saturating_add(1);
        }
        match (left, right) {
            (Value::Array(a), Value::Array(b)) => {
                if self.equality && Rc::ptr_eq(a, b) {
                    return Ordering::Equal;
                }
                // Sharing on either side can be inherited through ancestors,
                // even when a descendant allocation has just one direct owner.
                // Ordinary trees and flat arrays need no cache allocations.
                let shared =
                    self.shared_ancestor || Rc::strong_count(a) > 1 || Rc::strong_count(b) > 1;
                let pair = (Rc::as_ptr(a), Rc::as_ptr(b));
                if shared && self.equal_arrays.contains(&pair) {
                    return Ordering::Equal;
                }
                let previous = self.shared_ancestor;
                self.shared_ancestor = shared;
                let result = self.arrays(a, b);
                self.shared_ancestor = previous;
                if shared && result.is_eq() {
                    self.equal_arrays.insert(pair);
                }
                result
            }
            (Value::Object(a), Value::Object(b)) => {
                if self.equality && Rc::ptr_eq(a, b) {
                    return Ordering::Equal;
                }
                if self.equality && a.len() != b.len() {
                    return Ordering::Less;
                }
                let previous = self.shared_ancestor;
                self.shared_ancestor |= Rc::strong_count(a) > 1 || Rc::strong_count(b) > 1;
                let result = self.sequence(
                    a.iter_sorted().flat_map(|(key, value)| [key, value]),
                    b.iter_sorted().flat_map(|(key, value)| [key, value]),
                );
                self.shared_ancestor = previous;
                result
            }
            (Value::Set(a), Value::Set(b)) => {
                if self.equality && Rc::ptr_eq(a, b) {
                    return Ordering::Equal;
                }
                if self.equality && a.len() != b.len() {
                    return Ordering::Less;
                }
                let previous = self.shared_ancestor;
                self.shared_ancestor |= Rc::strong_count(a) > 1 || Rc::strong_count(b) > 1;
                let result = self.sequence(a.iter_sorted(), b.iter_sorted());
                self.shared_ancestor = previous;
                result
            }
            // Equality keeps length-aware scalar comparisons and uses Less
            // only as an internal "unequal" sentinel, never as an ordering.
            _ if self.equality => {
                if left == right {
                    Ordering::Equal
                } else {
                    Ordering::Less
                }
            }
            _ => left.cmp(right),
        }
    }

    fn sequence<'a, 'b>(
        &mut self,
        mut left: impl Iterator<Item = &'a Value>,
        mut right: impl Iterator<Item = &'b Value>,
    ) -> Ordering {
        loop {
            match (left.next(), right.next()) {
                (Some(a), Some(b)) => {
                    let result = self.values(a, b);
                    if !result.is_eq() {
                        return result;
                    }
                }
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (None, None) => return Ordering::Equal,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::arithmetic_side_effects, clippy::unwrap_used)]

    use super::*;
    use crate::value::{Object, Set};
    use alloc::vec;
    use alloc::vec::Vec;

    fn dag(depth: usize, leaf: Value, wrap: fn(Value) -> Value) -> Value {
        (0..depth).fold(leaf, |child, _| {
            let child = wrap(child);
            Value::from(vec![child.clone(), child])
        })
    }

    fn object(value: Value) -> Value {
        Object::from_iter([(Value::from("key"), value)]).into()
    }

    fn set(value: Value) -> Value {
        Set::from_iter([value]).into_value()
    }

    // The old iterator comparison expands every shared edge into a tree.
    fn tree_cmp(left: &Value, right: &Value, visits: &mut usize) -> Ordering {
        *visits += 1;
        match (left, right) {
            (Value::Array(a), Value::Array(b)) => tree_sequence(a.iter(), b.iter(), visits),
            (Value::Object(a), Value::Object(b)) => tree_sequence(
                a.iter_sorted().flat_map(|(key, value)| [key, value]),
                b.iter_sorted().flat_map(|(key, value)| [key, value]),
                visits,
            ),
            (Value::Set(a), Value::Set(b)) => {
                tree_sequence(a.iter_sorted(), b.iter_sorted(), visits)
            }
            _ => left.cmp(right),
        }
    }

    fn tree_sequence<'a, 'b>(
        mut left: impl Iterator<Item = &'a Value>,
        mut right: impl Iterator<Item = &'b Value>,
        visits: &mut usize,
    ) -> Ordering {
        loop {
            match (left.next(), right.next()) {
                (Some(a), Some(b)) => {
                    let result = tree_cmp(a, b, visits);
                    if !result.is_eq() {
                        return result;
                    }
                }
                (Some(_), None) => return Ordering::Greater,
                (None, Some(_)) => return Ordering::Less,
                (None, None) => return Ordering::Equal,
            }
        }
    }

    #[test]
    fn shared_array_comparison_work_scales_with_dag_not_expanded_tree() {
        for depth in [4, 8, 12] {
            let left = dag(depth, Value::Bool(true), core::convert::identity);
            let right = dag(depth, Value::Bool(true), core::convert::identity);
            assert!(!core::ptr::eq(
                left.as_array().unwrap(),
                right.as_array().unwrap()
            ));
            let mut old_visits = 0;
            assert_eq!(tree_cmp(&left, &right, &mut old_visits), Ordering::Equal);
            assert_eq!(old_visits, (1_usize << (depth + 1)) - 1);
            for mut comparison in [Comparison::default(), Comparison::equality()] {
                assert_eq!(comparison.values(&left, &right), Ordering::Equal);
                assert_eq!(comparison.visits, 2 * depth + 1);
                assert_eq!(comparison.equal_arrays.len(), depth - 1);
            }
            assert!(left == right);
            assert_eq!(left.cmp(&right), Ordering::Equal);
        }
    }

    #[test]
    fn shared_array_comparison_bounds_asymmetric_sharing() {
        fn alternating_dag(depth: usize, phase: usize) -> Value {
            let mut roots = [Value::Bool(true), Value::Bool(true)];
            for level in 0..depth {
                let make_array = || Value::from(roots.to_vec());
                roots = if level % 2 == phase {
                    let root = make_array();
                    [root.clone(), root]
                } else {
                    [make_array(), make_array()]
                };
            }
            let [root, _] = roots;
            root
        }

        for depth in [4, 8, 12] {
            let left = alternating_dag(depth, 0);
            let right = alternating_dag(depth, 1);
            for mut comparison in [Comparison::default(), Comparison::equality()] {
                assert_eq!(comparison.values(&left, &right), Ordering::Equal);
                assert!(
                    comparison.visits <= 8 * depth + 1,
                    "depth {depth}: {} visits",
                    comparison.visits
                );
            }
            assert!(left == right);
            assert_eq!(left.cmp(&right), Ordering::Equal);
        }
    }

    #[test]
    fn shared_array_cache_survives_object_and_set_boundaries() {
        let wrappers: [fn(Value) -> Value; 2] = [object, set];
        for wrap in wrappers {
            for depth in [4, 8, 12] {
                let left = dag(depth, Value::Undefined, wrap);
                let right = dag(depth, Value::Undefined, wrap);
                let mut comparison = Comparison::default();
                assert_eq!(comparison.values(&left, &right), Ordering::Equal);
                assert!(comparison.visits <= 6 * depth + 1);
                assert_eq!(comparison.equal_arrays.len(), depth - 1);
                assert!(left == right);
            }
        }
    }

    #[test]
    fn array_comparison_preserves_internal_undefined_values() {
        let wrappers: [fn(Value) -> Value; 3] = [core::convert::identity, object, set];
        for wrap in wrappers {
            let left = dag(4, Value::Undefined, wrap);
            let equal = dag(4, Value::Undefined, wrap);
            let null = dag(4, Value::Null, wrap);
            assert!(left == equal);
            assert_eq!(left.cmp(&equal), Ordering::Equal);
            assert!(left != null);
            assert_eq!(left.cmp(&null), Ordering::Greater);
            assert_eq!(left.partial_cmp(&null), Some(Ordering::Greater));
        }
    }

    #[test]
    fn ordinary_array_trees_do_not_populate_cache() {
        fn tree() -> Value {
            Value::from(vec![
                Value::from(vec![Value::Null]),
                Value::from(vec![Value::Bool(true)]),
            ])
        }
        let mut comparison = Comparison::default();
        assert_eq!(comparison.values(&tree(), &tree()), Ordering::Equal);
        assert!(comparison.equal_arrays.is_empty());
        let left: Vec<_> = (0..128).map(Value::from).collect();
        let right: Vec<_> = (0..128).map(Value::from).collect();
        let mut comparison = Comparison::default();
        assert_eq!(
            comparison.values(&Value::from(left), &Value::from(right)),
            Ordering::Equal
        );
        assert!(comparison.equal_arrays.is_empty());
    }

    #[test]
    fn array_equality_keeps_nested_length_short_circuits() {
        let left = Value::from(vec![Value::from(vec![Value::Null; 128])]);
        let right = Value::from(vec![Value::from(vec![Value::Null; 129])]);
        let mut comparison = Comparison::equality();
        assert!(!comparison.values(&left, &right).is_eq());
        assert_eq!(comparison.visits, 2);
    }

    #[test]
    fn array_equality_does_not_descend_into_identical_collection_allocations() {
        for depth in [4, 8, 12] {
            let array = (0..depth).fold(Value::Null, |child, _| Value::from(vec![child]));
            let object = (0..depth).fold(Value::Null, |child, _| {
                Object::from_iter([(Value::from("a"), child.clone()), (Value::from("b"), child)])
                    .into()
            });
            let set = Set::from_iter([object.clone()]).into_value();

            for child in [array, object, set] {
                let left = Array::from(vec![child.clone()]);
                let right = Array::from(vec![child]);
                let mut comparison = Comparison::equality();
                assert_eq!(comparison.arrays(&left, &right), Ordering::Equal);
                assert_eq!(comparison.visits, 1, "depth {depth}");
                assert!(comparison.equal_arrays.is_empty());
                assert!(left == right);
            }
        }
    }

    #[test]
    fn shared_array_comparison_is_local_and_collection_keys_remain_structural() {
        let left = dag(6, Value::Bool(true), core::convert::identity);
        let mut right = dag(6, Value::Bool(true), core::convert::identity);
        assert!(left == right);
        let mut keys = Set::new();
        assert!(keys.insert(left.clone()));
        assert!(!keys.insert(right.clone()));
        assert!(keys.contains(&right));
        let mut object = Object::new();
        object.insert(left.clone(), Value::Null);
        assert_eq!(object.get(&right), Some(&Value::Null));

        right.as_array_mut().unwrap().push(Value::Null);
        assert!(left != right);
        assert!(left < right);
        assert!(!keys.contains(&right));
        assert_eq!(object.get(&right), None);
        assert!(left == dag(6, Value::Bool(true), core::convert::identity));
    }
}
