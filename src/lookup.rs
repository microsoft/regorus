// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Lookup table for associating data structures with AST nodes.
//!
//! This module provides efficient lookup tables for associating custom data
//! with expressions, queries, and statements using their respective indices.

use crate::*;
use core::convert::TryFrom as _;
use core::fmt;

#[inline]
fn usize_from_u32(value: u32) -> Option<usize> {
    usize::try_from(value).ok()
}

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
        match *self {
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

impl core::error::Error for LookupIndexError {}

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
    pub(crate) const fn new() -> Self {
        Self { slots: Vec::new() }
    }

    /// Ensure the lookup table has capacity for the given module and node index.
    pub(crate) fn ensure_capacity(&mut self, module_idx: u32, node_idx: u32) {
        let Some(module_idx) = usize_from_u32(module_idx) else {
            debug_assert!(false, "module_idx does not fit in usize");
            return;
        };
        let Some(node_idx) = usize_from_u32(node_idx) else {
            debug_assert!(false, "node_idx does not fit in usize");
            return;
        };

        // Ensure we have enough modules
        if self.slots.len() <= module_idx {
            let needed = module_idx.saturating_add(1);
            self.slots.resize(needed, Vec::new());
        }

        // Ensure the module has enough capacity for this node index
        if let Some(module) = self.slots.get_mut(module_idx) {
            if module.len() <= node_idx {
                let needed = node_idx.saturating_add(1);
                module.resize(needed, None);
            }
        }
    }

    /// Set data using direct indices with bounds checking.
    /// Returns Ok(()) if written, Err if either index is out of bounds.
    pub(crate) fn set_checked(
        &mut self,
        module_idx: u32,
        node_idx: u32,
        value: T,
    ) -> LookupResult<()> {
        let slot = self.slot_mut(module_idx, node_idx)?;
        *slot = Some(value);
        Ok(())
    }

    /// Get data using direct indices with bounds checking.
    /// Returns Ok(None) if the entry is unset, Err if indices are out of range.
    pub(crate) fn get_checked(&self, module_idx: u32, node_idx: u32) -> LookupResult<Option<&T>> {
        self.slot_ref(module_idx, node_idx)
    }

    /// Clear data at the given indices by setting it to None.
    pub(crate) fn clear(&mut self, module_idx: u32, node_idx: u32) {
        if let Ok(slot) = self.slot_mut(module_idx, node_idx) {
            *slot = None;
        }
    }

    pub(crate) fn truncate_modules(&mut self, module_count: usize) {
        self.slots.truncate(module_count);
    }

    pub(crate) const fn module_len(&self) -> usize {
        self.slots.len()
    }

    pub(crate) fn push_module(&mut self, module: Vec<Option<T>>) {
        self.slots.push(module);
    }

    pub(crate) fn remove_module(&mut self, module_idx: usize) -> Option<Vec<Option<T>>> {
        (module_idx < self.slots.len()).then(|| self.slots.remove(module_idx))
    }

    /// Validate indices and return them as usize on success.
    fn validate_indices(&self, module_idx: u32, node_idx: u32) -> LookupResult<(usize, usize)> {
        let m = usize_from_u32(module_idx).ok_or(LookupIndexError::ModuleOutOfBounds {
            module_idx,
            modules: self.slots.len(),
        })?;
        let module = match self.slots.get(m) {
            Some(module) => module,
            None => {
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
        };

        let n = usize_from_u32(node_idx).ok_or(LookupIndexError::NodeOutOfBounds {
            module_idx,
            node_idx,
            nodes: module.len(),
        })?;
        if n >= module.len() {
            debug_assert!(
                n < module.len(),
                "node_idx {n} out of bounds for module {m} (nodes={})",
                module.len()
            );
            return Err(LookupIndexError::NodeOutOfBounds {
                module_idx,
                node_idx,
                nodes: module.len(),
            });
        }

        Ok((m, n))
    }

    fn slot_ref(&self, module_idx: u32, node_idx: u32) -> LookupResult<Option<&T>> {
        let (m, n) = self.validate_indices(module_idx, node_idx)?;
        let slot = self.slots.get(m).and_then(|module| module.get(n));
        Ok(slot.and_then(|value| value.as_ref()))
    }

    fn slot_mut(&mut self, module_idx: u32, node_idx: u32) -> LookupResult<&mut Option<T>> {
        let (m, n) = self.validate_indices(module_idx, node_idx)?;
        let nodes = self.slots.get(m).map_or(0, |module| module.len());
        if let Some(slot) = self.slots.get_mut(m).and_then(|module| module.get_mut(n)) {
            return Ok(slot);
        }

        // Should be unreachable because validate_indices guarantees bounds.
        debug_assert!(false, "validated indices should be in-bounds");
        Err(LookupIndexError::NodeOutOfBounds {
            module_idx,
            node_idx,
            nodes,
        })
    }
}
