// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! See [`Array`].

mod iter;
mod serde;

use alloc::vec::Vec;
use core::cmp::Ordering;
use core::fmt;

use crate::value::Value;

pub use iter::{ArrayIntoIter, ArrayIter, ArrayIterMut};

/// Opaque, ordered sequence of [`Value`]s.
///
/// The current backing storage is `Vec<Value>`. The inner field is private so
/// the representation can change without touching call sites.
#[derive(Default, Clone, Eq, PartialEq)]
pub struct Array {
    inner: Vec<Value>,
}

impl Array {
    /// Create an empty `Array`.
    #[inline]
    pub const fn new() -> Self {
        Self { inner: Vec::new() }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.inner.get(index)
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut Value> {
        self.inner.get_mut(index)
    }

    #[inline]
    pub fn first(&self) -> Option<&Value> {
        self.inner.first()
    }

    #[inline]
    pub fn last(&self) -> Option<&Value> {
        self.inner.last()
    }

    #[inline]
    pub fn contains(&self, value: &Value) -> bool {
        self.inner.contains(value)
    }

    #[inline]
    pub fn as_slice(&self) -> &[Value] {
        self.inner.as_slice()
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [Value] {
        self.inner.as_mut_slice()
    }

    /// Iteration in element order. Non-resumable.
    #[inline]
    pub fn iter(&self) -> ArrayIter<'_> {
        ArrayIter {
            inner: self.inner.iter(),
        }
    }

    #[inline]
    pub fn iter_mut(&mut self) -> ArrayIterMut<'_> {
        ArrayIterMut {
            inner: self.inner.iter_mut(),
        }
    }

    #[inline]
    pub fn push(&mut self, value: Value) {
        self.inner.push(value);
    }

    #[inline]
    pub fn append(&mut self, other: &mut Array) {
        self.inner.append(&mut other.inner);
    }

    #[inline]
    pub fn extend<I: IntoIterator<Item = Value>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }

    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&Value) -> bool,
    {
        self.inner.retain(f);
    }

    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
    }

    #[inline]
    pub fn reverse(&mut self) {
        self.inner.reverse();
    }

    #[inline]
    pub fn sort(&mut self) {
        self.inner.sort();
    }

    #[inline]
    pub fn to_vec(&self) -> Vec<Value> {
        self.inner.clone()
    }

    #[inline]
    pub fn into_vec(self) -> Vec<Value> {
        self.inner
    }

    /// Create a resumable cursor over elements in order. O(1).
    #[inline]
    pub const fn cursor(&self) -> ArrayCursor {
        ArrayCursor { index: 0 }
    }

    /// Advance `cursor` and yield the next element.
    pub fn next<'a>(&'a self, cursor: &mut ArrayCursor) -> Option<&'a Value> {
        let value = self.inner.get(cursor.index)?;
        cursor.index = cursor.index.saturating_add(1);
        Some(value)
    }
}

/// Opaque resumable cursor over an [`Array`]'s elements.
#[derive(Debug, Clone)]
pub struct ArrayCursor {
    index: usize,
}

impl Ord for Array {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl PartialOrd for Array {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Array {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl Extend<Value> for Array {
    fn extend<I: IntoIterator<Item = Value>>(&mut self, iter: I) {
        self.inner.extend(iter);
    }
}

impl FromIterator<Value> for Array {
    fn from_iter<I: IntoIterator<Item = Value>>(iter: I) -> Self {
        Self {
            inner: Vec::from_iter(iter),
        }
    }
}

impl From<Vec<Value>> for Array {
    #[inline]
    fn from(values: Vec<Value>) -> Self {
        Self { inner: values }
    }
}
