// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::std_instead_of_core,
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
    clippy::missing_const_for_fn,
    clippy::if_then_some_else_none,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

//! Lookup table for associating data structures with AST nodes.
//!
//! This module provides efficient lookup tables for associating custom data
//! with expressions, queries, and statements using their respective indices.

use crate::*;
use core::fmt;

/// Error indicating that lookup indices are out of bounds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LookupIndexError {
    /// The requested module index exceeds the available modules.
    ModuleOutOfBounds { module_idx: u32, modules: usize },
    /// The requested node index exceeds the available nodes for the module.
    NodeOutOfBounds {
        module_idx: u32,
        node_idx: u32,
        nodes: usize,
    },
}

impl fmt::Display for LookupIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LookupIndexError::ModuleOutOfBounds {
                module_idx,
                modules,
            } => {
                write!(
                    f,
                    "module_idx {module_idx} out of bounds (modules={modules})"
                )
            }
            LookupIndexError::NodeOutOfBounds {
                module_idx,
                node_idx,
                nodes,
            } => write!(
                f,
                "node_idx {node_idx} out of bounds for module {module_idx} (nodes={nodes})"
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for LookupIndexError {}

pub type LookupResult<T> = core::result::Result<T, LookupIndexError>;

/// Generic lookup table that stores data indexed by module and node indices.
#[derive(Debug, Clone)]
pub struct Lookup<T: Clone> {
    /// Array of slots indexed by node index within each module
    slots: Vec<Vec<Option<T>>>,
}

impl<T: Clone> Default for Lookup<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Lookup<T> {
    /// Create a new lookup table.
    pub fn new() -> Self {
        Self { slots: Vec::new() }
    }

    /// Ensure the lookup table has capacity for the given module and node index.
    pub fn ensure_capacity(&mut self, module_idx: u32, node_idx: u32) {
        let module_idx = module_idx as usize;
        let node_idx = node_idx as usize;

        // Ensure we have enough modules
        if self.slots.len() <= module_idx {
            self.slots.resize(module_idx + 1, Vec::new());
        }

        // Ensure the module has enough capacity for this node index
        if self.slots[module_idx].len() <= node_idx {
            self.slots[module_idx].resize(node_idx + 1, None);
        }
    }

    /// Set data using direct indices with bounds checking.
    /// Returns Ok(()) if written, Err if either index is out of bounds.
    pub fn set_checked(&mut self, module_idx: u32, node_idx: u32, value: T) -> LookupResult<()> {
        let (m, n) = self.validate_indices(module_idx, node_idx)?;
        self.slots[m][n] = Some(value);
        Ok(())
    }

    /// Get data using direct indices with bounds checking.
    /// Returns Ok(None) if the entry is unset, Err if indices are out of range.
    pub fn get_checked(&self, module_idx: u32, node_idx: u32) -> LookupResult<Option<&T>> {
        let (m, n) = self.validate_indices(module_idx, node_idx)?;
        Ok(self.slots[m][n].as_ref())
    }

    /// Clear data at the given indices by setting it to None.
    pub fn clear(&mut self, module_idx: u32, node_idx: u32) {
        if (module_idx as usize) < self.slots.len()
            && (node_idx as usize) < self.slots[module_idx as usize].len()
        {
            self.slots[module_idx as usize][node_idx as usize] = None;
        }
    }

    pub fn truncate_modules(&mut self, module_count: usize) {
        self.slots.truncate(module_count);
    }

    pub fn module_len(&self) -> usize {
        self.slots.len()
    }

    pub fn push_module(&mut self, module: Vec<Option<T>>) {
        self.slots.push(module);
    }

    pub fn remove_module(&mut self, module_idx: usize) -> Option<Vec<Option<T>>> {
        if module_idx < self.slots.len() {
            Some(self.slots.remove(module_idx))
        } else {
            None
        }
    }

    /// Validate indices and return them as usize on success.
    fn validate_indices(&self, module_idx: u32, node_idx: u32) -> LookupResult<(usize, usize)> {
        let m = module_idx as usize;
        if m >= self.slots.len() {
            debug_assert!(
                m < self.slots.len(),
                "module_idx {m} out of bounds (modules={})",
                self.slots.len()
            );
            return Err(LookupIndexError::ModuleOutOfBounds {
                module_idx,
                modules: self.slots.len(),
            });
        }

        let n = node_idx as usize;
        if n >= self.slots[m].len() {
            debug_assert!(
                n < self.slots[m].len(),
                "node_idx {n} out of bounds for module {m} (nodes={})",
                self.slots[m].len()
            );
            return Err(LookupIndexError::NodeOutOfBounds {
                module_idx,
                node_idx,
                nodes: self.slots[m].len(),
            });
        }

        Ok((m, n))
    }
}
