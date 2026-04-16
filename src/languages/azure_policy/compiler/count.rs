// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code, clippy::pattern_type_mismatch)]

//! `count` / `count.where` loop compilation.
//!
//! Stub — real implementation added in a later commit.

use anyhow::{bail, Result};

use crate::languages::azure_policy::ast::{Condition, CountNode};

use super::core::Compiler;

impl Compiler {
    pub(super) fn compile_count(&mut self, count_node: &CountNode) -> Result<u8> {
        let _ = self;
        let span = match count_node {
            CountNode::Field { span, .. } | CountNode::Value { span, .. } => span,
        };
        bail!(span.error("count compilation not yet implemented"))
    }

    pub(super) const fn try_compile_count_as_any(
        &mut self,
        _count_node: &CountNode,
        _condition: &Condition,
    ) -> Result<Option<u8>> {
        _ = self.register_counter;
        Ok(None)
    }
}
