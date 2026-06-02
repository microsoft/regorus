// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Opaque iterator types for [`Set`].
//!
//! These newtypes wrap the storage backend's iterators so the backend can be
//! swapped without changing any iterator type signatures observed by callers.

use alloc::collections::btree_set;
use core::iter::FusedIterator;

use super::Set;
use crate::value::Value;

/// Owned iterator over `Value` elements.
#[derive(Debug)]
pub struct IntoIter {
    pub(super) inner: btree_set::IntoIter<Value>,
}

impl Iterator for IntoIter {
    type Item = Value;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl DoubleEndedIterator for IntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl ExactSizeIterator for IntoIter {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl FusedIterator for IntoIter {}

/// Borrowed iterator over `&Value` elements.
#[derive(Debug, Clone)]
pub struct Iter<'a> {
    pub(super) inner: btree_set::Iter<'a, Value>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Value;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a> ExactSizeIterator for Iter<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> FusedIterator for Iter<'a> {}

impl IntoIterator for Set {
    type Item = Value;
    type IntoIter = IntoIter;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<'a> IntoIterator for &'a Set {
    type Item = &'a Value;
    type IntoIter = Iter<'a>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        Iter {
            inner: self.inner.iter(),
        }
    }
}
