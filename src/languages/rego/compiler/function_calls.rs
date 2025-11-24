// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::{Compiler, CompilerError, Register, Result};
use crate::ast::ExprRef;
use crate::lexer::Span;
use crate::rvm::instructions::{BuiltinCallParams, FunctionCallParams};
use crate::rvm::Instruction;
use crate::utils::get_path_string;
use alloc::vec::Vec;

impl<'a> Compiler<'a> {
    pub(super) fn compile_function_call(
        &mut self,
        fcn: &ExprRef,
        params: &[ExprRef],
        span: Span,
    ) -> Result<Register> {
        let fcn_path =
            get_path_string(fcn, None).map_err(|_| CompilerError::InvalidFunctionExpression)?;

        let original_fcn_path = fcn_path.clone();
        let full_fcn_path = if self.policy.inner.rules.contains_key(&fcn_path) {
            fcn_path
        } else {
            get_path_string(fcn, Some(&self.current_package))
                .map_err(|_| CompilerError::InvalidFunctionExpressionWithPackage)?
        };

        let mut arg_regs = Vec::new();
        for param in params.iter() {
            let param_reg = self.compile_rego_expr_with_span(param, param.span(), false)?;
            arg_regs.push(param_reg);
        }

        let dest = self.alloc_register();

        if self.is_user_defined_function(&full_fcn_path) {
            let rule_index = self.get_or_assign_rule_index(&full_fcn_path)?;
            let mut args_array = [0u8; 8];
            let num_args = arg_regs.len().min(8) as u8;
            for (i, &reg) in arg_regs.iter().take(8).enumerate() {
                args_array[i] = reg;
            }

            let params_index = self.program.add_function_call_params(FunctionCallParams {
                func_rule_index: rule_index,
                dest,
                num_args,
                args: args_array,
            });
            self.emit_instruction(Instruction::FunctionCall { params_index }, &span);
        } else if self.is_builtin(&original_fcn_path) {
            let builtin_index = self.get_builtin_index(&original_fcn_path)?;
            let mut args_array = [0u8; 8];
            let num_args = arg_regs.len().min(8) as u8;
            for (i, &reg) in arg_regs.iter().take(8).enumerate() {
                args_array[i] = reg;
            }

            let params_index = self.program.add_builtin_call_params(BuiltinCallParams {
                dest,
                builtin_index,
                num_args,
                args: args_array,
            });
            self.emit_instruction(Instruction::BuiltinCall { params_index }, &span);
        } else {
            return Err(CompilerError::UnknownFunction {
                name: original_fcn_path,
            });
        }

        Ok(dest)
    }
}
