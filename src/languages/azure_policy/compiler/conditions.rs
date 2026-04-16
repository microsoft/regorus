// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Constraint / condition / LHS compilation.

use alloc::vec::Vec;

use anyhow::Result;

use crate::languages::azure_policy::ast::{Condition, Constraint, Lhs, OperatorKind};
use crate::rvm::instructions::{LogicalBlockMode, PolicyOp};
use crate::rvm::Instruction;

use super::core::Compiler;

impl Compiler {
    pub(super) fn compile_constraint(&mut self, constraint: &Constraint) -> Result<u8> {
        match constraint {
            Constraint::AllOf { span, constraints } => self.compile_allof(constraints, span),
            Constraint::AnyOf { span, constraints } => self.compile_anyof(constraints, span),
            Constraint::Not { span, constraint } => {
                let inner = self.compile_constraint(constraint)?;
                self.emit_coalesce_undefined_to_null(inner, span);
                let dest = self.alloc_register()?;
                self.emit(
                    Instruction::PolicyCondition {
                        dest,
                        left: inner,
                        right: 0,
                        op: PolicyOp::Not,
                    },
                    span,
                );
                Ok(dest)
            }
            Constraint::Condition(condition) => self.compile_condition(condition),
        }
    }

    // -- allOf with short-circuit ------------------------------------------

    fn compile_allof(
        &mut self,
        constraints: &[Constraint],
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let result_reg = self.alloc_register()?;

        let mut patch_pcs = Vec::with_capacity(constraints.len().saturating_add(1));

        patch_pcs.push(self.current_pc()?);
        self.emit(
            Instruction::LogicalBlockStart {
                mode: LogicalBlockMode::AllOf,
                result: result_reg,
                end_pc: 0,
            },
            span,
        );

        for child in constraints {
            let saved_counter = self.register_counter;
            let child_reg = self.compile_constraint(child)?;
            self.emit_coalesce_undefined_to_null(child_reg, span);
            patch_pcs.push(self.current_pc()?);
            self.emit(
                Instruction::AllOfNext {
                    check: child_reg,
                    result: result_reg,
                    end_pc: 0,
                },
                span,
            );
            self.restore_register_counter(saved_counter);
        }

        let end_pc = self.current_pc()?;
        self.emit(
            Instruction::LogicalBlockEnd {
                mode: LogicalBlockMode::AllOf,
                result: result_reg,
            },
            span,
        );

        self.patch_end_pc(&patch_pcs, end_pc)?;

        Ok(result_reg)
    }

    // -- anyOf with short-circuit ------------------------------------------

    fn compile_anyof(
        &mut self,
        constraints: &[Constraint],
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let result_reg = self.alloc_register()?;

        let mut patch_pcs = Vec::with_capacity(constraints.len().saturating_add(1));

        patch_pcs.push(self.current_pc()?);
        self.emit(
            Instruction::LogicalBlockStart {
                mode: LogicalBlockMode::AnyOf,
                result: result_reg,
                end_pc: 0,
            },
            span,
        );

        for child in constraints {
            let saved_counter = self.register_counter;
            let child_reg = self.compile_constraint(child)?;
            self.emit_coalesce_undefined_to_null(child_reg, span);
            patch_pcs.push(self.current_pc()?);
            self.emit(
                Instruction::AnyOfNext {
                    check: child_reg,
                    result: result_reg,
                    end_pc: 0,
                },
                span,
            );
            self.restore_register_counter(saved_counter);
        }

        let end_pc = self.current_pc()?;
        self.emit(
            Instruction::LogicalBlockEnd {
                mode: LogicalBlockMode::AnyOf,
                result: result_reg,
            },
            span,
        );

        self.patch_end_pc(&patch_pcs, end_pc)?;

        Ok(result_reg)
    }

    // -- operator condition compilation ------------------------------------

    pub(super) fn compile_condition(&mut self, condition: &Condition) -> Result<u8> {
        self.record_resource_type_from_condition(condition);

        // Implicit allOf: field with [*] outside count -> every element must match.
        if let Some(field_path) = self.has_unbound_wildcard_field(&condition.lhs)? {
            return self.compile_condition_wildcard_allof(&field_path, condition);
        }

        // Inner unbound [*] within count where clause.
        if let Some((binding, inner_path)) =
            self.has_inner_unbound_wildcard_field(&condition.lhs)?
        {
            let span = &condition.span;
            let rhs_reg = self.compile_value_or_expr(&condition.rhs, span)?;
            return self.compile_allof_loop_inner(
                Some(binding.current_reg),
                &inner_path,
                rhs_reg,
                condition,
            );
        }

        // Count existence optimization.
        if let Lhs::Count(count_node) = &condition.lhs {
            if let Some(result) = self.try_compile_count_as_any(count_node, condition)? {
                return Ok(result);
            }
        }

        let lhs = self.compile_lhs(&condition.lhs, &condition.span)?;

        // In Azure Policy, a missing field is semantically null.  Coalesce
        // undefined → null for field-based LHS so the behaviour matches the
        // `field()` template-expression path.  `exists` deliberately needs to
        // distinguish undefined from null, so we skip coalescing for it.
        if matches!(condition.lhs, Lhs::Field(..))
            && !matches!(condition.operator.kind, OperatorKind::Exists)
        {
            self.emit_coalesce_undefined_to_null(lhs, &condition.span);
        }

        let rhs = self.compile_value_or_expr(&condition.rhs, &condition.span)?;
        let op_result = self.emit_policy_operator(
            &condition.operator.kind,
            lhs,
            rhs,
            &condition.operator.span,
        )?;

        // For `value:` conditions, guard against undefined LHS.
        if matches!(condition.lhs, Lhs::Value { .. }) {
            let guarded = self.alloc_register()?;
            self.emit(
                Instruction::PolicyCondition {
                    dest: guarded,
                    left: lhs,
                    right: op_result,
                    op: PolicyOp::ValueConditionGuard,
                },
                &condition.span,
            );
            return Ok(guarded);
        }

        Ok(op_result)
    }

    pub(super) fn compile_lhs(&mut self, lhs: &Lhs, span: &crate::lexer::Span) -> Result<u8> {
        match lhs {
            Lhs::Field(field) => self.compile_field_kind(&field.kind, &field.span),
            Lhs::Value { value, .. } => self.compile_value_or_expr(value, span),
            Lhs::Count(count_node) => self.compile_count(count_node),
        }
    }

    /// Emit a native policy operator instruction.
    pub(super) fn emit_policy_operator(
        &mut self,
        kind: &OperatorKind,
        left: u8,
        right: u8,
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        self.record_operator(kind);
        let dest = self.alloc_register()?;
        let op = match kind {
            OperatorKind::Equals => PolicyOp::Equals,
            OperatorKind::NotEquals => PolicyOp::NotEquals,
            OperatorKind::Greater => PolicyOp::Greater,
            OperatorKind::GreaterOrEquals => PolicyOp::GreaterOrEquals,
            OperatorKind::Less => PolicyOp::Less,
            OperatorKind::LessOrEquals => PolicyOp::LessOrEquals,
            OperatorKind::In => PolicyOp::In,
            OperatorKind::NotIn => PolicyOp::NotIn,
            OperatorKind::Contains => PolicyOp::Contains,
            OperatorKind::NotContains => PolicyOp::NotContains,
            OperatorKind::ContainsKey => PolicyOp::ContainsKey,
            OperatorKind::NotContainsKey => PolicyOp::NotContainsKey,
            OperatorKind::Like => PolicyOp::Like,
            OperatorKind::NotLike => PolicyOp::NotLike,
            OperatorKind::Match => PolicyOp::Match,
            OperatorKind::NotMatch => PolicyOp::NotMatch,
            OperatorKind::MatchInsensitively => PolicyOp::MatchInsensitively,
            OperatorKind::NotMatchInsensitively => PolicyOp::NotMatchInsensitively,
            OperatorKind::Exists => PolicyOp::Exists,
        };
        self.emit(
            Instruction::PolicyCondition {
                dest,
                left,
                right,
                op,
            },
            span,
        );
        Ok(dest)
    }
}
