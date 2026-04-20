// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]

//! Effect compilation (dispatch + cross-resource).
//!
//! Stub — real implementation added in a later commit.

use anyhow::{bail, Result};

use crate::languages::azure_policy::ast::PolicyRule;

use super::core::Compiler;

impl Compiler {
    pub(super) fn compile_effect(&mut self, _rule: &PolicyRule) -> Result<u8> {
        let _ = self;
        bail!("effect compilation not yet implemented")
    }

    pub(super) fn wrap_effect_result(
        &mut self,
        _effect_name_reg: u8,
        _details_reg: Option<u8>,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("wrap_effect_result not yet implemented")
    }
}
