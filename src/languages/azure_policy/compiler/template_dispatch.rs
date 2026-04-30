// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! ARM template function dispatch — maps lowercased function names to
//! builtin calls or native instructions.

use alloc::vec::Vec;

use anyhow::{bail, Result};

use crate::languages::azure_policy::ast::Expr;
use crate::rvm::instructions::PolicyOp;
use crate::rvm::Instruction;

use super::core::Compiler;

impl Compiler {
    /// Dispatch an ARM template function call by lowercased name.
    ///
    /// Returns `Ok(Some(dest))` if the function was handled, `Ok(None)` if
    /// the name is not an ARM template function.
    pub(super) fn compile_arm_template_function(
        &mut self,
        function_name: &str,
        span: &crate::lexer::Span,
        args: &[Expr],
    ) -> Result<Option<u8>> {
        let dest = match function_name {
            // -- Core ARM template functions --
            "concat" => {
                let mut element_regs = Vec::with_capacity(args.len());
                for arg in args {
                    element_regs.push(self.compile_expr(arg)?);
                }
                let array_dest = self.alloc_register()?;
                let array_params = self.program.instruction_data.add_array_create_params(
                    crate::rvm::instructions::ArrayCreateParams {
                        dest: array_dest,
                        elements: element_regs,
                    },
                );
                self.emit(
                    Instruction::ArrayCreate {
                        params_index: array_params,
                    },
                    span,
                );
                let delimiter_reg = self.load_literal(crate::Value::from(""), span)?;
                self.emit_builtin_call("concat", &[delimiter_reg, array_dest], span)?
            }
            "if" => {
                let [cond_arg, true_arg, false_arg] = args else {
                    bail!(span.error("if() requires three arguments"));
                };
                let cond = self.compile_expr(cond_arg)?;
                let when_true = self.compile_expr(true_arg)?;
                let when_false = self.compile_expr(false_arg)?;
                self.emit_builtin_call("azure.policy.if", &[cond, when_true, when_false], span)?
            }
            "and" => {
                let regs = self.compile_call_args(args)?;
                self.emit_builtin_call("azure.policy.logic_all", &regs, span)?
            }
            "not" => {
                let [inner_arg] = args else {
                    bail!(span.error("not() requires one argument"));
                };
                let inner = self.compile_expr(inner_arg)?;
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
                dest
            }
            "tolower" => {
                let regs = self.compile_call_args(args)?;
                self.emit_builtin_call("lower", &regs, span)?
            }
            "toupper" => {
                let regs = self.compile_call_args(args)?;
                self.emit_builtin_call("upper", &regs, span)?
            }
            "replace" => {
                let regs = self.compile_call_args(args)?;
                self.emit_builtin_call("replace", &regs, span)?
            }
            "substring" => {
                let regs = self.compile_call_args(args)?;
                self.emit_builtin_call("substring", &regs, span)?
            }
            "length" => {
                let regs = self.compile_call_args(args)?;
                self.emit_builtin_call("count", &regs, span)?
            }
            "add" => self.emit_binary_instruction(args, span, |dest, left, right| {
                Instruction::Add { dest, left, right }
            })?,
            "equals" => self.emit_binary_instruction(args, span, |dest, left, right| {
                Instruction::PolicyCondition {
                    dest,
                    left,
                    right,
                    op: PolicyOp::Equals,
                }
            })?,
            "greaterorequals" => {
                self.emit_binary_instruction(args, span, |dest, left, right| {
                    Instruction::PolicyCondition {
                        dest,
                        left,
                        right,
                        op: PolicyOp::GreaterOrEquals,
                    }
                })?
            }
            "lessorequals" => self.emit_binary_instruction(args, span, |dest, left, right| {
                Instruction::PolicyCondition {
                    dest,
                    left,
                    right,
                    op: PolicyOp::LessOrEquals,
                }
            })?,
            "contains" => self.emit_binary_instruction(args, span, |dest, left, right| {
                Instruction::PolicyCondition {
                    dest,
                    left,
                    right,
                    op: PolicyOp::Contains,
                }
            })?,
            "greater" => self.emit_binary_instruction(args, span, |dest, left, right| {
                Instruction::PolicyCondition {
                    dest,
                    left,
                    right,
                    op: PolicyOp::Greater,
                }
            })?,
            "less" => self.emit_binary_instruction(args, span, |dest, left, right| {
                Instruction::PolicyCondition {
                    dest,
                    left,
                    right,
                    op: PolicyOp::Less,
                }
            })?,

            // -- Logical functions --
            "or" => {
                let regs = self.compile_call_args(args)?;
                self.emit_builtin_call("azure.policy.logic_any", &regs, span)?
            }
            "true" => {
                if !args.is_empty() {
                    bail!(span.error("true() takes no arguments"));
                }
                self.load_literal(crate::Value::Bool(true), span)?
            }
            "false" => {
                if !args.is_empty() {
                    bail!(span.error("false() takes no arguments"));
                }
                self.load_literal(crate::Value::Bool(false), span)?
            }

            // -- Existing ARM template functions --
            "split" => self.emit_builtin_call_from_args("azure.policy.fn.split", args, span)?,
            "empty" => self.emit_builtin_call_from_args("azure.policy.fn.empty", args, span)?,
            "first" => self.emit_builtin_call_from_args("azure.policy.fn.first", args, span)?,
            "last" => self.emit_builtin_call_from_args("azure.policy.fn.last", args, span)?,
            "startswith" => {
                self.emit_builtin_call_from_args("azure.policy.fn.starts_with", args, span)?
            }
            "endswith" => {
                self.emit_builtin_call_from_args("azure.policy.fn.ends_with", args, span)?
            }
            "int" => self.emit_builtin_call_from_args("azure.policy.fn.int", args, span)?,
            "string" => self.emit_builtin_call_from_args("azure.policy.fn.string", args, span)?,
            "bool" => self.emit_builtin_call_from_args("azure.policy.fn.bool", args, span)?,
            "padleft" => {
                self.emit_builtin_call_from_args("azure.policy.fn.pad_left", args, span)?
            }
            "iprangecontains" => {
                self.emit_builtin_call_from_args("azure.policy.fn.ip_range_contains", args, span)?
            }
            "createarray" => {
                let mut element_regs = Vec::with_capacity(args.len());
                for arg in args {
                    element_regs.push(self.compile_expr(arg)?);
                }
                let array_dest = self.alloc_register()?;
                let array_params = self.program.instruction_data.add_array_create_params(
                    crate::rvm::instructions::ArrayCreateParams {
                        dest: array_dest,
                        elements: element_regs,
                    },
                );
                self.emit(
                    Instruction::ArrayCreate {
                        params_index: array_params,
                    },
                    span,
                );
                array_dest
            }

            // -- String functions --
            "indexof" => {
                self.emit_builtin_call_from_args("azure.policy.fn.index_of", args, span)?
            }
            "lastindexof" => {
                self.emit_builtin_call_from_args("azure.policy.fn.last_index_of", args, span)?
            }
            "trim" => self.emit_builtin_call_from_args("azure.policy.fn.trim", args, span)?,
            "format" => self.emit_builtin_call_from_args("azure.policy.fn.format", args, span)?,

            // -- Encoding functions --
            "base64" => self.emit_builtin_call_from_args("azure.policy.fn.base64", args, span)?,
            "base64tostring" => {
                self.emit_builtin_call_from_args("azure.policy.fn.base64_to_string", args, span)?
            }
            "base64tojson" => {
                self.emit_builtin_call_from_args("azure.policy.fn.base64_to_json", args, span)?
            }
            "uri" => self.emit_builtin_call_from_args("azure.policy.fn.uri", args, span)?,
            "uricomponent" => {
                self.emit_builtin_call_from_args("azure.policy.fn.uri_component", args, span)?
            }
            "uricomponenttostring" => self.emit_builtin_call_from_args(
                "azure.policy.fn.uri_component_to_string",
                args,
                span,
            )?,
            "datauri" => {
                self.emit_builtin_call_from_args("azure.policy.fn.data_uri", args, span)?
            }
            "datauritostring" => {
                self.emit_builtin_call_from_args("azure.policy.fn.data_uri_to_string", args, span)?
            }

            // -- Collection functions --
            "intersection" => {
                self.emit_builtin_call_from_args("azure.policy.fn.intersection", args, span)?
            }
            "union" => self.emit_builtin_call_from_args("azure.policy.fn.union", args, span)?,
            "take" => self.emit_builtin_call_from_args("azure.policy.fn.take", args, span)?,
            "skip" => self.emit_builtin_call_from_args("azure.policy.fn.skip", args, span)?,
            "range" => self.emit_builtin_call_from_args("azure.policy.fn.range", args, span)?,
            "array" => self.emit_builtin_call_from_args("azure.policy.fn.array", args, span)?,
            "coalesce" => {
                self.emit_builtin_call_from_args("azure.policy.fn.coalesce", args, span)?
            }
            "createobject" => {
                self.emit_builtin_call_from_args("azure.policy.fn.create_object", args, span)?
            }

            // -- Numeric functions --
            "sub" => {
                let [left_arg, right_arg] = args else {
                    bail!(span.error("sub() requires two arguments"));
                };
                let left = self.compile_expr(left_arg)?;
                let right = self.compile_expr(right_arg)?;
                let dest = self.alloc_register()?;
                self.emit(Instruction::Sub { dest, left, right }, span);
                dest
            }
            "mul" => {
                let [left_arg, right_arg] = args else {
                    bail!(span.error("mul() requires two arguments"));
                };
                let left = self.compile_expr(left_arg)?;
                let right = self.compile_expr(right_arg)?;
                let dest = self.alloc_register()?;
                self.emit(Instruction::Mul { dest, left, right }, span);
                dest
            }
            "div" => {
                let [_, _] = args else {
                    bail!(span.error("div() requires two arguments"));
                };
                self.emit_builtin_call_from_args("azure.policy.fn.int_div", args, span)?
            }
            "mod" => {
                let [_, _] = args else {
                    bail!(span.error("mod() requires two arguments"));
                };
                self.emit_builtin_call_from_args("azure.policy.fn.int_mod", args, span)?
            }
            "min" => self.emit_builtin_call_from_args("azure.policy.fn.min", args, span)?,
            "max" => self.emit_builtin_call_from_args("azure.policy.fn.max", args, span)?,
            "float" => self.emit_builtin_call_from_args("azure.policy.fn.float", args, span)?,

            // -- JSON / misc functions --
            "json" => self.emit_builtin_call_from_args("azure.policy.fn.json", args, span)?,
            "join" => self.emit_builtin_call_from_args("azure.policy.fn.join", args, span)?,
            "guid" | "uniquestring" => {
                bail!(span.error(&alloc::format!(
                    "unsupported template function '{function_name}' (deployment-template functions are not evaluated for compliance)"
                )));
            }
            "items" => self.emit_builtin_call_from_args("azure.policy.fn.items", args, span)?,
            "indexfromend" => {
                self.emit_builtin_call_from_args("azure.policy.fn.index_from_end", args, span)?
            }
            "tryget" => self.emit_builtin_call_from_args("azure.policy.fn.try_get", args, span)?,
            "tryindexfromend" => {
                self.emit_builtin_call_from_args("azure.policy.fn.try_index_from_end", args, span)?
            }

            // -- Date/Time functions --
            "datetimeadd" => {
                self.emit_builtin_call_from_args("azure.policy.fn.date_time_add", args, span)?
            }
            "datetimefromepoch" => self.emit_builtin_call_from_args(
                "azure.policy.fn.date_time_from_epoch",
                args,
                span,
            )?,
            "datetimetoepoch" => {
                self.emit_builtin_call_from_args("azure.policy.fn.date_time_to_epoch", args, span)?
            }
            "adddays" => {
                self.emit_builtin_call_from_args("azure.policy.fn.add_days", args, span)?
            }

            _ => return Ok(None),
        };
        Ok(Some(dest))
    }

    /// Compile arguments and emit a builtin call.
    fn emit_builtin_call_from_args(
        &mut self,
        name: &str,
        args: &[Expr],
        span: &crate::lexer::Span,
    ) -> Result<u8> {
        let regs = self.compile_call_args(args)?;
        self.emit_builtin_call(name, &regs, span)
    }

    /// Compile a binary (2-arg) call and emit a native instruction.
    fn emit_binary_instruction(
        &mut self,
        args: &[Expr],
        span: &crate::lexer::Span,
        make_instr: impl FnOnce(u8, u8, u8) -> Instruction,
    ) -> Result<u8> {
        let [left_arg, right_arg] = args else {
            bail!(span.error("expected exactly two arguments"));
        };
        let left = self.compile_expr(left_arg)?;
        let right = self.compile_expr(right_arg)?;
        let dest = self.alloc_register()?;
        self.emit(make_instr(dest, left, right), span);
        Ok(dest)
    }
}
