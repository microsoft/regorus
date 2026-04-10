// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(dead_code)]

//! Template-expression and call-expression compilation.
//!
//! Stub — real implementation added in a later commit.

use anyhow::{bail, Result};

use crate::languages::azure_policy::ast::{Expr, JsonValue, ValueOrExpr};

use super::core::Compiler;

impl Compiler {
    pub(super) fn compile_value_or_expr(
        &mut self,
        _voe: &ValueOrExpr,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("expression compilation not yet implemented")
    }

    pub(super) fn compile_json_value(
        &mut self,
        _value: &JsonValue,
        _span: &crate::lexer::Span,
    ) -> Result<u8> {
        let _ = self;
        bail!("JSON value compilation not yet implemented")
    }

    pub(super) fn compile_expr(&mut self, _expr: &Expr) -> Result<u8> {
        let _ = self;
        bail!("expression compilation not yet implemented")
    }

    pub(super) fn compile_call_expr(
        &mut self,
        _span: &crate::lexer::Span,
        _func: &str,
        _args: &[Expr],
    ) -> Result<u8> {
        let _ = self;
        bail!("call expression compilation not yet implemented")
    }

    pub(super) fn compile_call_args(&mut self, _args: &[Expr]) -> Result<alloc::vec::Vec<u8>> {
        let _ = self;
        bail!("call args compilation not yet implemented")
    }
}
