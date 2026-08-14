// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Opaque iterator types for [`Array`].

use alloc::vec;
use core::iter::FusedIterator;
use core::slice;

use super::Array;
use crate::value::Value;

/// Owned iterator over `Value` elements.
#[derive(Debug)]
pub struct ArrayIntoIter {
    pub(super) inner: vec::IntoIter<Value>,
}

impl Iterator for ArrayIntoIter {
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

impl DoubleEndedIterator for ArrayIntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl ExactSizeIterator for ArrayIntoIter {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl FusedIterator for ArrayIntoIter {}

/// Borrowed iterator over `&Value` elements.
#[derive(Debug, Clone)]
pub struct ArrayIter<'a> {
    pub(super) inner: slice::Iter<'a, Value>,
}

impl<'a> Iterator for ArrayIter<'a> {
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

impl<'a> DoubleEndedIterator for ArrayIter<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a> ExactSizeIterator for ArrayIter<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> FusedIterator for ArrayIter<'a> {}

/// Borrowed iterator over `&mut Value` elements.
#[derive(Debug)]
pub struct ArrayIterMut<'a> {
    pub(super) inner: slice::IterMut<'a, Value>,
}

impl<'a> Iterator for ArrayIterMut<'a> {
    type Item = &'a mut Value;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<'a> DoubleEndedIterator for ArrayIterMut<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back()
    }
}

impl<'a> ExactSizeIterator for ArrayIterMut<'a> {
    #[inline]
    fn len(&self) -> usize {
        self.inner.len()
    }
}

impl<'a> FusedIterator for ArrayIterMut<'a> {}

impl IntoIterator for Array {
    type Item = Value;
    type IntoIter = ArrayIntoIter;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        ArrayIntoIter {
            inner: self.inner.into_iter(),
        }
    }
}

impl<'a> IntoIterator for &'a Array {
    type Item = &'a Value;
    type IntoIter = ArrayIter<'a>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> IntoIterator for &'a mut Array {
    type Item = &'a mut Value;
    type IntoIter = ArrayIterMut<'a>;
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}
