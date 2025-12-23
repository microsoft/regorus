// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

use super::{Compiler, Register, Result};
use crate::ast::ExprRef;
use crate::lexer::Span;
use crate::rvm::instructions::{ArrayCreateParams, ObjectCreateParams, SetCreateParams};
use crate::rvm::Instruction;
use crate::{Rc, Value};
use alloc::collections::BTreeMap;
use alloc::vec::Vec;

impl<'a> Compiler<'a> {
    pub(super) fn compile_array_literal(
        &mut self,
        items: &[ExprRef],
        span: &Span,
    ) -> Result<Register> {
        let mut element_registers = Vec::with_capacity(items.len());
        for item in items {
            let item_reg = self.compile_rego_expr_with_span(item, item.span(), false)?;
            element_registers.push(item_reg);
        }

        let dest = self.alloc_register();
        let params = ArrayCreateParams {
            dest,
            elements: element_registers,
        };
        let params_index = self
            .program
            .instruction_data
            .add_array_create_params(params);
        self.emit_instruction(Instruction::ArrayCreate { params_index }, span);
        Ok(dest)
    }

    pub(super) fn compile_set_literal(
        &mut self,
        items: &[ExprRef],
        span: &Span,
    ) -> Result<Register> {
        let mut element_registers = Vec::with_capacity(items.len());
        for item in items {
            let item_reg = self.compile_rego_expr_with_span(item, item.span(), false)?;
            element_registers.push(item_reg);
        }

        let dest = self.alloc_register();
        let params = SetCreateParams {
            dest,
            elements: element_registers,
        };
        let params_index = self.program.instruction_data.add_set_create_params(params);
        self.emit_instruction(Instruction::SetCreate { params_index }, span);
        Ok(dest)
    }

    pub(super) fn compile_object_literal(
        &mut self,
        fields: &[(crate::lexer::Span, ExprRef, ExprRef)],
        span: &Span,
    ) -> Result<Register> {
        let dest = self.alloc_register();

        let mut value_regs = Vec::with_capacity(fields.len());
        for (_, _key_expr, value_expr) in fields {
            let value_reg =
                self.compile_rego_expr_with_span(value_expr, value_expr.span(), false)?;
            value_regs.push(value_reg);
        }

        let mut literal_key_fields = Vec::new();
        let mut non_literal_key_fields = Vec::new();
        let mut literal_keys: Vec<Value> = Vec::new();

        for (field_idx, (_, key_expr, _value_expr)) in fields.iter().enumerate() {
            let value_reg = value_regs[field_idx];
            let key_literal = match key_expr.as_ref() {
                crate::ast::Expr::String { value, .. }
                | crate::ast::Expr::RawString { value, .. }
                | crate::ast::Expr::Number { value, .. }
                | crate::ast::Expr::Bool { value, .. }
                | crate::ast::Expr::Null { value, .. } => Some(value.clone()),
                _ => None,
            };

            if let Some(key_value) = key_literal {
                let literal_idx = self.add_literal(key_value.clone());
                literal_key_fields.push((literal_idx, value_reg));
                literal_keys.push(key_value);
            } else {
                let key_reg = self.compile_rego_expr_with_span(key_expr, key_expr.span(), false)?;
                non_literal_key_fields.push((key_reg, value_reg));
            }
        }

        let template_literal_idx = {
            let mut template_keys = literal_keys.clone();
            template_keys.sort();

            let mut template_obj = BTreeMap::new();
            for key in &template_keys {
                template_obj.insert(key.clone(), Value::Undefined);
            }

            let template_value = Value::Object(Rc::new(template_obj));
            self.add_literal(template_value)
        };

        literal_key_fields.sort_by(|a, b| {
            let key_a = &self.program.literals[a.0 as usize];
            let key_b = &self.program.literals[b.0 as usize];
            key_a.cmp(key_b)
        });

        let params = ObjectCreateParams {
            dest,
            template_literal_idx,
            literal_key_fields,
            fields: non_literal_key_fields,
        };
        let params_index = self
            .program
            .instruction_data
            .add_object_create_params(params);
        self.emit_instruction(Instruction::ObjectCreate { params_index }, span);
        Ok(dest)
    }
}
