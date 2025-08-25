// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Lookup table for associating data structures with AST nodes.
//!
//! This module provides efficient lookup tables for associating custom data
//! with expressions, queries, and statements using their respective indices.

use crate::*;

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

    /// Set data using direct indices (bounds assumed to be ensured).
    pub fn set(&mut self, module_idx: u32, node_idx: u32, value: T) {
        *self.get_mut(module_idx, node_idx) = Some(value);
    }

    /// Get data using direct indices (bounds assumed to be ensured).
    pub fn get(&self, module_idx: u32, node_idx: u32) -> Option<&T> {
        self.slots[module_idx as usize][node_idx as usize].as_ref()
    }

    /// Get mutable reference to data using direct indices (bounds assumed to be ensured).
    pub fn get_mut(&mut self, module_idx: u32, node_idx: u32) -> &mut Option<T> {
        &mut self.slots[module_idx as usize][node_idx as usize]
    }

    /// Clear data at the given indices by setting it to None.
    pub fn clear(&mut self, module_idx: u32, node_idx: u32) {
        if (module_idx as usize) < self.slots.len()
            && (node_idx as usize) < self.slots[module_idx as usize].len()
        {
            self.slots[module_idx as usize][node_idx as usize] = None;
        }
    }
}
