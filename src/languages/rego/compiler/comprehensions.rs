// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::as_conversions)]

use super::{CompilationContext, Compiler, ComprehensionType, ContextType, Register, Result};
use crate::ast::{ExprRef, Query};
use crate::lexer::Span;
use crate::rvm::instructions::{ComprehensionBeginParams, ComprehensionMode};
use crate::rvm::Instruction;

impl<'a> Compiler<'a> {
    fn compile_comprehension(
        &mut self,
        mode: ComprehensionMode,
        context_type: ComprehensionType,
        key_expr: Option<&ExprRef>,
        value_expr: Option<&ExprRef>,
        query: &Query,
        span: &Span,
    ) -> Result<Register> {
        let result_reg = self.alloc_register();
        let key_reg = self.alloc_register();
        let value_reg = self.alloc_register();

        let params_index = self
            .program
            .add_comprehension_begin_params(ComprehensionBeginParams {
                mode,
                collection_reg: result_reg,
                result_reg,
                key_reg,
                value_reg,
                body_start: 0,
                comprehension_end: 0,
            });

        self.emit_instruction(Instruction::ComprehensionBegin { params_index }, span);

        let body_start = self.program.instructions.len() as u16;

        let context = CompilationContext {
            context_type: ContextType::Comprehension(context_type),
            dest_register: result_reg,
            key_expr: key_expr.cloned(),
            value_expr: value_expr.cloned(),
            span: span.clone(),
            key_value_loops_hoisted: false,
        };
        self.push_context(context);
        self.compile_query(query)?;
        self.pop_context();

        self.emit_instruction(Instruction::ComprehensionEnd {}, span);
        let comprehension_end = self.program.instructions.len() as u16;

        self.program
            .update_comprehension_begin_params(params_index, |params| {
                params.body_start = body_start;
                params.comprehension_end = comprehension_end;
            });

        Ok(result_reg)
    }

    pub(super) fn compile_array_comprehension(
        &mut self,
        term: &ExprRef,
        query: &Query,
        span: &Span,
    ) -> Result<Register> {
        self.compile_comprehension(
            ComprehensionMode::Array,
            ComprehensionType::Array,
            None,
            Some(term),
            query,
            span,
        )
    }

    pub(super) fn compile_set_comprehension(
        &mut self,
        term: &ExprRef,
        query: &Query,
        span: &Span,
    ) -> Result<Register> {
        self.compile_comprehension(
            ComprehensionMode::Set,
            ComprehensionType::Set,
            None,
            Some(term),
            query,
            span,
        )
    }

    pub(super) fn compile_object_comprehension(
        &mut self,
        key: &ExprRef,
        value: &ExprRef,
        query: &Query,
        span: &Span,
    ) -> Result<Register> {
        self.compile_comprehension(
            ComprehensionMode::Object,
            ComprehensionType::Object,
            Some(key),
            Some(value),
            query,
            span,
        )
    }
}
