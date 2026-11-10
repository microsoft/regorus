// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

use super::{Compiler, CompilerError, Register, Result};
use crate::ast::{Expr, ExprRef};
use crate::lexer::Span;
use crate::rvm::instructions::{ArrayCreateParams, ObjectCreateParams, SetCreateParams};
use crate::rvm::Instruction;
use crate::value::Object;
use crate::{Rc, Value};
use alloc::collections::BTreeSet;
use alloc::vec::Vec;

/// Try to evaluate an expression as a compile-time constant.
pub(in crate::languages::rego::compiler) fn try_eval_const(expr: &Expr) -> Option<Value> {
    match expr {
        Expr::Number { value, .. }
        | Expr::String { value, .. }
        | Expr::RawString { value, .. }
        | Expr::Bool { value, .. }
        | Expr::Null { value, .. } => Some(value.clone()),
        Expr::UnaryExpr { expr, .. } => match expr.as_ref() {
            Expr::Number {
                value: Value::Number(n),
                ..
            } => Some(Value::Number(n.neg()?)),
            _ => None,
        },
        Expr::Array { items, .. } => items
            .iter()
            .map(|i| try_eval_const(i.as_ref()))
            .collect::<Option<Vec<_>>>()
            .map(Value::from_array),
        Expr::Set { items, .. } => items
            .iter()
            .map(|i| try_eval_const(i.as_ref()))
            .collect::<Option<BTreeSet<_>>>()
            .map(Value::from_set),
        Expr::Object { fields, .. } => fields
            .iter()
            .map(|(_, k, v)| Some((try_eval_const(k.as_ref())?, try_eval_const(v.as_ref())?)))
            .collect::<Option<Object>>()
            .map(|m| Value::Object(Rc::new(m))),
        _ => None,
    }
}

fn literal_round_trips(value: &Value) -> bool {
    match value {
        Value::Array(values) => values.iter().all(literal_round_trips),
        Value::Set(_) | Value::Undefined => false,
        // JSON object literals stringify non-string keys. Construct those
        // objects at runtime, even when nested in a constant collection.
        Value::Object(fields) => fields.iter().all(|(key, field_value)| {
            matches!(key, Value::String(_)) && literal_round_trips(field_value)
        }),
        _ => true,
    }
}

pub(in crate::languages::rego::compiler) fn try_eval_literal(expr: &Expr) -> Option<Value> {
    try_eval_const(expr).filter(literal_round_trips)
}

impl<'a> Compiler<'a> {
    fn constant_scratch_register(&mut self, depth: usize) -> Result<Register> {
        while self.constant_scratch_registers.len() <= depth {
            let register = self.alloc_register()?;
            self.constant_scratch_registers.push(register);
        }
        Ok(self.constant_scratch_registers[depth])
    }

    pub(in crate::languages::rego::compiler) fn compile_constant_value(
        &mut self,
        value: &Value,
        span: &Span,
    ) -> Result<Register> {
        let dest = self.alloc_register()?;
        self.emit_constant_value(value, dest, 0, span)?;
        Ok(dest)
    }

    fn emit_constant_value(
        &mut self,
        value: &Value,
        dest: Register,
        depth: usize,
        span: &Span,
    ) -> Result<()> {
        if literal_round_trips(value) {
            let literal_idx = self.add_literal(value.clone());
            self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
            return Ok(());
        }

        // Only constant construction uses this pool: children have no effects,
        // bindings or root caches. Their temporaries die after each insertion.
        match value {
            Value::Array(values) => {
                self.emit_instruction(Instruction::ArrayNew { dest }, span);
                for child in values.iter() {
                    let element = self.constant_scratch_register(depth)?;
                    self.emit_constant_value(child, element, depth.saturating_add(1), span)?;
                    self.emit_instruction(
                        Instruction::ArrayPush {
                            arr: dest,
                            value: element,
                        },
                        span,
                    );
                }
            }
            Value::Set(values) => {
                self.emit_instruction(Instruction::SetNew { dest }, span);
                for child in values.iter() {
                    let element = self.constant_scratch_register(depth)?;
                    self.emit_constant_value(child, element, depth.saturating_add(1), span)?;
                    self.emit_instruction(
                        Instruction::SetAdd {
                            set: dest,
                            value: element,
                        },
                        span,
                    );
                }
            }
            Value::Object(fields) => {
                let literal_idx = self.add_literal(Value::new_object());
                self.emit_instruction(Instruction::Load { dest, literal_idx }, span);
                for (field_key, field_value) in fields.iter() {
                    let key_register = self.constant_scratch_register(depth)?;
                    let value_register = self.constant_scratch_register(depth.saturating_add(1))?;
                    let child_depth = depth.saturating_add(2);
                    self.emit_constant_value(field_key, key_register, child_depth, span)?;
                    self.emit_constant_value(field_value, value_register, child_depth, span)?;
                    self.emit_instruction(
                        Instruction::ObjectSet {
                            obj: dest,
                            key: key_register,
                            value: value_register,
                        },
                        span,
                    );
                }
            }
            _ => {
                return Err(CompilerError::General {
                    message: "constant is not representable as a typed literal".into(),
                }
                .into());
            }
        }
        Ok(())
    }

    pub(super) fn compile_array_literal(
        &mut self,
        items: &[ExprRef],
        span: &Span,
    ) -> Result<Register> {
        let all_const: Option<Vec<_>> = items.iter().map(|i| try_eval_const(i.as_ref())).collect();
        if let Some(values) = all_const {
            return self.compile_constant_value(&Value::from_array(values), span);
        }

        let mut element_registers = Vec::with_capacity(items.len());
        for item in items {
            let item_reg = self.compile_rego_expr_with_span(item, item.span(), false)?;
            element_registers.push(item_reg);
        }

        let dest = self.alloc_register()?;
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
        let all_const: Option<BTreeSet<_>> =
            items.iter().map(|i| try_eval_const(i.as_ref())).collect();
        if let Some(values) = all_const {
            return self.compile_constant_value(&Value::from_set(values), span);
        }

        let mut element_registers = Vec::with_capacity(items.len());
        for item in items {
            let item_reg = self.compile_rego_expr_with_span(item, item.span(), false)?;
            element_registers.push(item_reg);
        }

        let dest = self.alloc_register()?;
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
        let all_const: Option<Object> = fields
            .iter()
            .map(|(_, k, v)| Some((try_eval_const(k.as_ref())?, try_eval_const(v.as_ref())?)))
            .collect();
        if let Some(obj) = all_const {
            return self.compile_constant_value(&Value::Object(Rc::new(obj)), span);
        }

        let dest = self.alloc_register()?;

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
            template_keys.retain(|key| matches!(key, Value::String(_)));
            template_keys.sort();

            let mut template_obj = Object::new();
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
