// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::expect_used,
    clippy::as_conversions,
    clippy::unused_trait_names
)]

use super::{CompilationContext, Compiler, CompilerError, Register, Result, Scope};
use crate::ast::ExprRef;
use crate::builtins;
use crate::compiler::destructuring_planner::plans::BindingPlan;
use crate::lexer::Span;
use crate::rvm::program::{BuiltinInfo, SpanInfo};
use crate::rvm::Instruction;
use crate::Value;
use alloc::format;
use alloc::string::{String, ToString};

impl<'a> Compiler<'a> {
    /// Check if a function path is a builtin function (similar to interpreter's is_builtin)
    pub(super) fn is_builtin(&self, path: &str) -> bool {
        path == "print" || builtins::BUILTINS.contains_key(path)
    }

    /// Check if a function path is a user-defined function rule
    pub(super) fn is_user_defined_function(&self, rule_path: &str) -> bool {
        self.policy.inner.rules.contains_key(rule_path)
    }

    /// Get builtin index for a builtin function
    pub(super) fn get_builtin_index(&mut self, builtin_name: &str) -> Result<u16> {
        if !self.is_builtin(builtin_name) {
            return Err(CompilerError::NotBuiltinFunction {
                name: builtin_name.to_string(),
            }
            .into());
        }

        // Check if we already have an index for this builtin
        if let Some(&index) = self.builtin_index_map.get(builtin_name) {
            return Ok(index);
        }

        // Get the builtin function info to determine number of arguments
        let num_args = if builtin_name == "print" {
            2 // Special case for print
        } else if let Some(builtin_fcn) = builtins::BUILTINS.get(builtin_name) {
            builtin_fcn.1 as u16 // Second element is the number of arguments
        } else {
            return Err(CompilerError::UnknownBuiltinFunction {
                name: builtin_name.to_string(),
            }
            .into());
        };

        // Create builtin info and add it to the program
        let builtin_info = BuiltinInfo {
            name: builtin_name.to_string(),
            num_args,
        };
        let index = self.program.add_builtin_info(builtin_info);

        // Store in our mapping
        self.builtin_index_map
            .insert(builtin_name.to_string(), index);

        Ok(index)
    }

    pub fn alloc_register(&mut self) -> Register {
        // Assert that we don't exceed 256 registers (u8::MAX + 1)
        assert!(
            self.register_counter < 255,
            "Register overflow: attempted to allocate register {}, but maximum is 255. \
			 Consider using register windowing or spill handling.",
            self.register_counter
        );

        let reg = self.register_counter;
        self.register_counter += 1;

        reg
    }

    /// Add a literal value to the literal table, returning its index
    pub fn add_literal(&mut self, value: Value) -> u16 {
        // Check if literal already exists to avoid duplication
        // TODO: Optimize lookup
        for (idx, existing) in self.program.literals.iter().enumerate() {
            if existing == &value {
                return idx as u16;
            }
        }

        let idx = self.program.literals.len() as u16;
        self.program.literals.push(value);
        idx
    }

    /// Push a new variable scope (like the interpreter)
    pub fn push_scope(&mut self) {
        self.scopes.push(Scope::default());
    }

    /// Pop the current variable scope (like the interpreter)
    pub fn pop_scope(&mut self) {
        if self.scopes.len() > 1 {
            self.scopes.pop();
        }
    }

    /// Reset input/data registers for a new rule definition
    /// This ensures input and data are loaded only once per rule definition
    pub fn reset_rule_definition_registers(&mut self) {
        self.current_input_register = None;
        self.current_data_register = None;
    }

    /// Push a new compilation context onto the context stack
    pub fn push_context(&mut self, context: CompilationContext) {
        self.context_stack.push(context);
    }

    /// Pop the current compilation context from the context stack
    pub fn pop_context(&mut self) -> Option<CompilationContext> {
        // Don't pop the last context (default RegularRule)
        if self.context_stack.len() > 1 {
            self.context_stack.pop()
        } else {
            None
        }
    }

    /// Get the current scope mutably
    fn current_scope_mut(&mut self) -> &mut Scope {
        self.scopes.last_mut().expect("No active scope")
    }

    /// Add a variable to the current scope (like interpreter's add_variable)
    pub fn add_variable(&mut self, var_name: &str, register: Register) {
        if var_name != "_" {
            // Don't store anonymous variables
            self.current_scope_mut()
                .bound_vars
                .insert(var_name.to_string(), register);
        }
    }

    /// Returns true when a variable is already bound in the innermost scope
    pub fn is_var_bound_in_current_scope(&self, var_name: &str) -> bool {
        self.scopes
            .last()
            .map(|scope| scope.bound_vars.contains_key(var_name))
            .unwrap_or(false)
    }

    /// Look up a variable in all scopes starting from innermost (like interpreter's lookup_local_var)
    pub fn lookup_local_var(&self, var_name: &str) -> Option<Register> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.bound_vars.get(var_name).copied())
    }

    pub fn add_unbound_variable(&mut self, var_name: &str) {
        self.current_scope_mut()
            .unbound_vars
            .insert(var_name.to_string());
    }

    pub fn is_unbound_var(&self, var_name: &str) -> bool {
        self.lookup_local_var(var_name).is_none()
            && self
                .scopes
                .iter()
                .rev()
                .any(|scope| scope.unbound_vars.contains(var_name))
    }

    pub fn bind_unbound_variable(&mut self, var_name: &str) {
        self.current_scope_mut().unbound_vars.remove(var_name);
    }

    pub(super) fn store_variable(&mut self, var_name: String, register: Register) {
        self.add_variable(&var_name, register);
    }

    /// Look up a variable register (backward compatibility)
    pub(super) fn lookup_variable(&self, var_name: &str) -> Option<Register> {
        self.lookup_local_var(var_name)
    }

    pub(super) fn get_binding_plan_for_expr(&self, expr: &ExprRef) -> Result<Option<BindingPlan>> {
        let module_idx = self.current_module_index;
        let expr_idx = expr.as_ref().eidx();
        self.policy
            .inner
            .loop_hoisting_table
            .get_expr_binding_plan(module_idx, expr_idx)
            .map_err(|err| {
                CompilerError::General {
                    message: format!("loop hoisting table out of bounds: {err}"),
                }
                .at(expr.span())
            })
            .map(|plan: Option<&BindingPlan>| plan.cloned())
    }

    pub(super) fn expect_binding_plan_for_expr(
        &self,
        expr: &ExprRef,
        context: &str,
    ) -> Result<BindingPlan> {
        self.get_binding_plan_for_expr(expr)?.ok_or_else(|| {
            CompilerError::MissingBindingPlan {
                context: context.to_string(),
            }
            .at(expr.span())
        })
    }

    pub(super) fn resolve_variable(&mut self, var_name: &str, span: &Span) -> Result<Register> {
        match var_name {
            "input" => {
                if let Some(register) = self.current_input_register {
                    return Ok(register);
                }

                let dest = self.alloc_register();
                self.emit_instruction(Instruction::LoadInput { dest }, span);
                self.current_input_register = Some(dest);
                return Ok(dest);
            }
            "data" => {
                if let Some(register) = self.current_data_register {
                    return Ok(register);
                }

                let dest = self.alloc_register();
                self.emit_instruction(Instruction::LoadData { dest }, span);
                self.current_data_register = Some(dest);
                return Ok(dest);
            }
            _ => {}
        }

        if let Some(var_reg) = self.lookup_variable(var_name) {
            return Ok(var_reg);
        }

        let rule_path = format!("{}.{}", &self.current_package, var_name);
        let rule_index = self.get_or_assign_rule_index(&rule_path)?;
        let dest = self.alloc_register();

        self.emit_instruction(Instruction::CallRule { dest, rule_index }, span);
        Ok(dest)
    }

    pub fn emit_instruction(&mut self, instruction: Instruction, span: &Span) {
        self.program.instructions.push(instruction);

        let source_path = span.source.get_path().to_string();
        let source_index = self.get_or_create_source_index(&source_path);

        self.spans
            .push(SpanInfo::from_lexer_span(span, source_index));
    }

    fn get_or_create_source_index(&mut self, source_path: &str) -> usize {
        if let Some(&index) = self.source_to_index.get(source_path) {
            index
        } else {
            let index = self.source_to_index.len();
            self.source_to_index.insert(source_path.to_string(), index);
            index
        }
    }
}
