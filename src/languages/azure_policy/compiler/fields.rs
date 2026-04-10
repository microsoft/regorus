// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]

//! Field-kind and resource-path compilation.
//!
//! Stub — real implementation added in a later commit.

use anyhow::{bail, Result};

use crate::languages::azure_policy::ast::FieldKind;

use super::core::Compiler;

impl Compiler {
    pub(super) fn compile_field_kind(
        &mut self,
        _kind: &FieldKind,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("field compilation not yet implemented")
    }

    pub(super) fn compile_field_path_expression(
        &mut self,
        _field_path: &str,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("field path compilation not yet implemented")
    }

    pub(super) fn compile_resource_path_value(
        &mut self,
        _field_path: &str,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("resource path compilation not yet implemented")
    }

    pub(super) fn compile_resource_root(&mut self, _span: &crate::lexer::Span) -> Result<u8> {
        let _ = self;
        bail!("resource root compilation not yet implemented")
    }

    pub(super) fn compile_field_wildcard_collect(
        &mut self,
        _field_path: &str,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("wildcard collect not yet implemented")
    }
}
