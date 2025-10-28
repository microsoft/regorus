// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use crate::{lookup::Lookup, value::Value};

/// Constant facts are stored alongside type information so that other tooling
/// (for example the VS Code extension) can query them quickly without having
/// to recompute constants or evaluate expressions.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ConstantFact {
    pub value: Option<Value>,
}

/// Lightweight wrapper around a [`Lookup`] to store constants per expression.
#[derive(Clone, Default, Debug)]
pub struct ConstantStore {
    table: Lookup<ConstantFact>,
}

impl ConstantStore {
    pub fn new() -> Self {
        ConstantStore {
            table: Lookup::new(),
        }
    }

    pub fn ensure_capacity(&mut self, module_idx: u32, expr_idx: u32) {
        self.table.ensure_capacity(module_idx, expr_idx);
    }

    pub fn record(&mut self, module_idx: u32, expr_idx: u32, value: Option<Value>) {
        self.table.set(module_idx, expr_idx, ConstantFact { value });
    }

    pub fn get(&self, module_idx: u32, expr_idx: u32) -> Option<&ConstantFact> {
        self.table.get(module_idx, expr_idx)
    }

    pub fn into_lookup(self) -> Lookup<ConstantFact> {
        self.table
    }
}
