// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]

//! Count-binding resolution and `current()` references.
//!
//! Stub — real implementation added in a later commit.

use anyhow::{bail, Result};

use super::core::{Compiler, CountBinding};

impl Compiler {
    pub(super) const fn resolve_count_binding(
        &self,
        _field_path: &str,
    ) -> Result<Option<CountBinding>> {
        _ = self.register_counter;
        Ok(None)
    }

    pub(super) fn compile_from_binding(
        &mut self,
        _binding: CountBinding,
        _field_path: &str,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("count binding compilation not yet implemented")
    }

    pub(super) fn compile_current_reference(
        &mut self,
        _key: &str,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("current() reference not yet implemented")
    }
}
