// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::indexing_slicing,
    clippy::arithmetic_side_effects,
    clippy::used_underscore_binding,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

use crate::rvm::instructions::{Instruction, LiteralOrRegister};
use crate::rvm::program::Program;
use crate::value::Value;
use alloc::collections::BTreeSet;
use alloc::vec::Vec;
use core::mem;

use super::errors::{Result, VmError};
use super::execution_model::{ExecutionMode, SuspendReason};
use super::loops::LoopParams;
use super::machine::RegoVM;

pub(super) enum InstructionOutcome {
    Continue,
    Return(Value),
    Break,
    Suspend { reason: SuspendReason },
}

impl RegoVM {
    pub(super) fn execute_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        self.execute_load_and_move(program, instruction)
    }

    fn execute_load_and_move(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Load { dest, literal_idx } => {
                if let Some(value) = program.literals.get(literal_idx as usize) {
                    self.registers[dest as usize] = value.clone();
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::LiteralIndexOutOfBounds {
                        index: literal_idx as usize,
                    })
                }
            }
            LoadTrue { dest } => {
                self.registers[dest as usize] = Value::Bool(true);
                Ok(InstructionOutcome::Continue)
            }
            LoadFalse { dest } => {
                self.registers[dest as usize] = Value::Bool(false);
                Ok(InstructionOutcome::Continue)
            }
            LoadNull { dest } => {
                self.registers[dest as usize] = Value::Null;
                Ok(InstructionOutcome::Continue)
            }
            LoadBool { dest, value } => {
                self.registers[dest as usize] = Value::Bool(value);
                Ok(InstructionOutcome::Continue)
            }
            LoadData { dest } => {
                self.registers[dest as usize] = self.data.clone();
                Ok(InstructionOutcome::Continue)
            }
            LoadInput { dest } => {
                self.registers[dest as usize] = self.input.clone();
                Ok(InstructionOutcome::Continue)
            }
            Move { dest, src } => {
                self.registers[dest as usize] = self.registers[src as usize].clone();
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_arithmetic_instruction(program, other),
        }
    }

    fn execute_arithmetic_instruction(
        &mut self,
        _program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Add { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.add_values(a, b)?;
                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            Sub { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.sub_values(a, b)?;
                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            Mul { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.mul_values(a, b)?;
                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            Div { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.div_values(a, b)?;
                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            Mod { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.mod_values(a, b)?;
                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_comparison_instruction(_program, other),
        }
    }

    fn execute_comparison_instruction(
        &mut self,
        _program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Eq { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                self.registers[dest as usize] = Value::Bool(a == b);
                Ok(InstructionOutcome::Continue)
            }
            Ne { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                self.registers[dest as usize] = Value::Bool(a != b);
                Ok(InstructionOutcome::Continue)
            }
            Lt { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError(alloc::format!(
                        "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                    )));
                }

                self.registers[dest as usize] = Value::Bool(a < b);
                Ok(InstructionOutcome::Continue)
            }
            Le { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError(alloc::format!(
                        "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                    )));
                }

                self.registers[dest as usize] = Value::Bool(a <= b);
                Ok(InstructionOutcome::Continue)
            }
            Gt { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError(alloc::format!(
                        "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                    )));
                }

                self.registers[dest as usize] = Value::Bool(a > b);
                Ok(InstructionOutcome::Continue)
            }
            Ge { dest, left, right } => {
                let a = &self.registers[left as usize];
                let b = &self.registers[right as usize];

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError(alloc::format!(
                        "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                    )));
                }

                self.registers[dest as usize] = Value::Bool(a >= b);
                Ok(InstructionOutcome::Continue)
            }
            And { dest, left, right } => {
                let left_value = &self.registers[left as usize];
                let right_value = &self.registers[right as usize];

                if left_value == &Value::Undefined || right_value == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                match (self.to_bool(left_value), self.to_bool(right_value)) {
                    (Some(a), Some(b)) => {
                        self.registers[dest as usize] = Value::Bool(a && b);
                        Ok(InstructionOutcome::Continue)
                    }
                    _ => Err(VmError::ArithmeticError(alloc::format!(
                        "#undefined: logical AND expects booleans (left={left_value:?}, right={right_value:?})"
                    ))),
                }
            }
            Or { dest, left, right } => {
                let left_value = &self.registers[left as usize];
                let right_value = &self.registers[right as usize];

                if left_value == &Value::Undefined || right_value == &Value::Undefined {
                    self.registers[dest as usize] = Value::Undefined;
                    return Ok(InstructionOutcome::Continue);
                }

                match (self.to_bool(left_value), self.to_bool(right_value)) {
                    (Some(a), Some(b)) => {
                        self.registers[dest as usize] = Value::Bool(a || b);
                        Ok(InstructionOutcome::Continue)
                    }
                    _ => Err(VmError::ArithmeticError(alloc::format!(
                        "#undefined: logical OR expects booleans (left={left_value:?}, right={right_value:?})"
                    ))),
                }
            }
            Not { dest, operand } => {
                let operand_value = &self.registers[operand as usize];

                if operand_value == &Value::Undefined {
                    // In Rego, `not expr` succeeds when `expr` has no results.
                    // When the operand evaluates to undefined we should treat it as
                    // a successful negation instead of propagating undefined.
                    self.registers[dest as usize] = Value::Bool(true);
                    return Ok(InstructionOutcome::Continue);
                }

                if let Some(value) = self.to_bool(operand_value) {
                    self.registers[dest as usize] = Value::Bool(!value);
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::ArithmeticError(alloc::format!(
                        "#undefined: logical NOT expects a boolean (operand={operand_value:?})"
                    )))
                }
            }
            AssertCondition { condition } => {
                let value = &self.registers[condition as usize];

                let condition_result = match value {
                    Value::Bool(b) => *b,
                    Value::Undefined => false,
                    _ => true,
                };

                self.handle_condition(condition_result)?;
                Ok(InstructionOutcome::Continue)
            }
            AssertNotUndefined { register } => {
                let value = &self.registers[register as usize];

                let is_undefined = matches!(value, Value::Undefined);
                self.handle_condition(!is_undefined)?;
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_call_instruction(_program, other),
        }
    }

    fn execute_call_instruction(
        &mut self,
        _program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            BuiltinCall { params_index } => {
                self.execute_builtin_call(params_index)?;
                Ok(InstructionOutcome::Continue)
            }
            HostAwait { dest, arg, id } => {
                let argument = self.registers[arg as usize].clone();
                let identifier = self
                    .registers
                    .get(id as usize)
                    .cloned()
                    .unwrap_or(Value::Undefined);
                match self.execution_mode {
                    ExecutionMode::RunToCompletion => {
                        let response = self.next_host_await_response(&identifier, dest)?;
                        if self.registers.len() <= dest as usize {
                            self.registers.resize(dest as usize + 1, Value::Undefined);
                        }
                        self.registers[dest as usize] = response;
                        Ok(InstructionOutcome::Continue)
                    }
                    ExecutionMode::Suspendable => Ok(InstructionOutcome::Suspend {
                        reason: SuspendReason::HostAwait {
                            dest,
                            argument,
                            identifier,
                        },
                    }),
                }
            }
            FunctionCall { params_index } => {
                self.execute_function_call(params_index)?;
                Ok(InstructionOutcome::Continue)
            }
            Return { value } => {
                let result = self.registers[value as usize].clone();
                Ok(InstructionOutcome::Return(result))
            }
            CallRule { dest, rule_index } => {
                self.execute_call_rule(dest, rule_index)?;
                Ok(InstructionOutcome::Continue)
            }
            RuleInit {
                result_reg,
                rule_index,
            } => {
                self.execute_rule_init(result_reg, rule_index)?;
                Ok(InstructionOutcome::Continue)
            }
            DestructuringSuccess {} => Ok(InstructionOutcome::Break),
            RuleReturn {} => {
                self.execute_rule_return()?;
                Ok(InstructionOutcome::Break)
            }
            other => self.execute_collection_instruction(_program, other),
        }
    }

    fn execute_collection_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            ObjectSet { obj, key, value } => {
                let key_value = self.registers[key as usize].clone();
                let value_value = self.registers[value as usize].clone();

                let mut obj_value = mem::replace(&mut self.registers[obj as usize], Value::Null);

                if let Ok(obj_mut) = obj_value.as_object_mut() {
                    obj_mut.insert(key_value, value_value);
                    self.registers[obj as usize] = obj_value;
                } else {
                    self.registers[obj as usize] = obj_value;
                    return Err(VmError::RegisterNotObject { register: obj });
                }
                Ok(InstructionOutcome::Continue)
            }
            ObjectCreate { params_index } => {
                let params = program
                    .instruction_data
                    .get_object_create_params(params_index)
                    .ok_or(VmError::InvalidObjectCreateParams {
                        index: params_index,
                    })?;

                let mut any_undefined = false;

                for &(_, value_reg) in params.literal_key_field_pairs() {
                    if matches!(self.registers[value_reg as usize], Value::Undefined) {
                        any_undefined = true;
                        break;
                    }
                }

                if !any_undefined {
                    for &(key_reg, value_reg) in params.field_pairs() {
                        if matches!(self.registers[key_reg as usize], Value::Undefined)
                            || matches!(self.registers[value_reg as usize], Value::Undefined)
                        {
                            any_undefined = true;
                            break;
                        }
                    }
                }

                if any_undefined {
                    self.registers[params.dest as usize] = Value::Undefined;
                } else {
                    let mut obj_value = program
                        .literals
                        .get(params.template_literal_idx as usize)
                        .ok_or(VmError::InvalidTemplateLiteralIndex {
                            index: params.template_literal_idx,
                        })?
                        .clone();

                    if let Ok(obj_mut) = obj_value.as_object_mut() {
                        let mut literal_updates = params.literal_key_field_pairs().iter();
                        let mut current_literal_update = literal_updates.next();

                        for (key, value) in obj_mut.iter_mut() {
                            if let Some(&(literal_idx, value_reg)) = current_literal_update {
                                if let Some(literal_key) =
                                    program.literals.get(literal_idx as usize)
                                {
                                    if key == literal_key {
                                        *value = self.registers[value_reg as usize].clone();
                                        current_literal_update = literal_updates.next();
                                    }
                                }
                            } else {
                                break;
                            }
                        }

                        while let Some(&(literal_idx, value_reg)) = current_literal_update {
                            if let Some(key_value) = program.literals.get(literal_idx as usize) {
                                let value_value = self.registers[value_reg as usize].clone();
                                obj_mut.insert(key_value.clone(), value_value);
                            }
                            current_literal_update = literal_updates.next();
                        }

                        for &(key_reg, value_reg) in params.field_pairs() {
                            let key_value = self.registers[key_reg as usize].clone();
                            let value_value = self.registers[value_reg as usize].clone();
                            obj_mut.insert(key_value, value_value);
                        }
                    } else {
                        return Err(VmError::ObjectCreateInvalidTemplate);
                    }

                    self.registers[params.dest as usize] = obj_value;
                }
                Ok(InstructionOutcome::Continue)
            }
            Index {
                dest,
                container,
                key,
            } => {
                let key_value = &self.registers[key as usize];
                let container_value = &self.registers[container as usize];
                let result = container_value[key_value].clone();
                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            IndexLiteral {
                dest,
                container,
                literal_idx,
            } => {
                let container_value = &self.registers[container as usize];

                if let Some(key_value) = program.literals.get(literal_idx as usize) {
                    let result = container_value[key_value].clone();
                    self.registers[dest as usize] = result;
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::LiteralIndexOutOfBounds {
                        index: literal_idx as usize,
                    })
                }
            }
            ArrayNew { dest } => {
                let empty_array = Value::Array(crate::Rc::new(Vec::new()));
                self.registers[dest as usize] = empty_array;
                Ok(InstructionOutcome::Continue)
            }
            ArrayPush { arr, value } => {
                let value_to_push = self.registers[value as usize].clone();

                let mut arr_value = mem::replace(&mut self.registers[arr as usize], Value::Null);

                if let Ok(arr_mut) = arr_value.as_array_mut() {
                    arr_mut.push(value_to_push);
                    self.registers[arr as usize] = arr_value;
                } else {
                    self.registers[arr as usize] = arr_value;
                    return Err(VmError::RegisterNotArray { register: arr });
                }
                Ok(InstructionOutcome::Continue)
            }
            ArrayCreate { params_index } => {
                if let Some(params) = program
                    .instruction_data
                    .get_array_create_params(params_index)
                {
                    let mut any_undefined = false;
                    for &reg in params.element_registers() {
                        if matches!(self.registers[reg as usize], Value::Undefined) {
                            any_undefined = true;
                            break;
                        }
                    }

                    if any_undefined {
                        self.registers[params.dest as usize] = Value::Undefined;
                    } else {
                        let elements: Vec<Value> = params
                            .element_registers()
                            .iter()
                            .map(|&reg| self.registers[reg as usize].clone())
                            .collect();

                        let array_value = Value::Array(crate::Rc::new(elements));
                        self.registers[params.dest as usize] = array_value;
                    }
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::InvalidArrayCreateParams {
                        index: params_index,
                    })
                }
            }
            SetNew { dest } => {
                let empty_set = Value::Set(crate::Rc::new(BTreeSet::new()));
                self.registers[dest as usize] = empty_set;
                Ok(InstructionOutcome::Continue)
            }
            SetAdd { set, value } => {
                let value_to_add = self.registers[value as usize].clone();

                let mut set_value = mem::replace(&mut self.registers[set as usize], Value::Null);

                if let Ok(set_mut) = set_value.as_set_mut() {
                    set_mut.insert(value_to_add);
                    self.registers[set as usize] = set_value;
                } else {
                    self.registers[set as usize] = set_value;
                    return Err(VmError::RegisterNotSet { register: set });
                }
                Ok(InstructionOutcome::Continue)
            }
            SetCreate { params_index } => {
                if let Some(params) = program.instruction_data.get_set_create_params(params_index) {
                    let mut any_undefined = false;
                    for &reg in params.element_registers() {
                        if matches!(self.registers[reg as usize], Value::Undefined) {
                            any_undefined = true;
                            break;
                        }
                    }

                    if any_undefined {
                        self.registers[params.dest as usize] = Value::Undefined;
                    } else {
                        let mut set = BTreeSet::new();
                        for &reg in params.element_registers() {
                            set.insert(self.registers[reg as usize].clone());
                        }

                        let set_value = Value::Set(crate::Rc::new(set));
                        self.registers[params.dest as usize] = set_value;
                    }
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::InvalidSetCreateParams {
                        index: params_index,
                    })
                }
            }
            Contains {
                dest,
                collection,
                value,
            } => {
                let value_to_check = &self.registers[value as usize];
                let collection_value = &self.registers[collection as usize];

                let result = match collection_value {
                    Value::Set(set_elements) => Value::Bool(set_elements.contains(value_to_check)),
                    Value::Array(array_items) => Value::Bool(array_items.contains(value_to_check)),
                    Value::Object(object_fields) => Value::Bool(
                        object_fields.contains_key(value_to_check)
                            || object_fields.values().any(|v| v == value_to_check),
                    ),
                    _ => Value::Bool(false),
                };

                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            Count { dest, collection } => {
                let collection_value = &self.registers[collection as usize];

                let result = match collection_value {
                    Value::Array(array_items) => Value::from(array_items.len()),
                    Value::Object(object_fields) => Value::from(object_fields.len()),
                    Value::Set(set_elements) => Value::from(set_elements.len()),
                    _ => Value::Undefined,
                };

                self.registers[dest as usize] = result;
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_loop_instruction(program, other),
        }
    }

    fn execute_loop_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            LoopStart { params_index } => {
                let loop_params = &self.program.instruction_data.loop_params[params_index as usize];
                let mode = loop_params.mode.clone();
                let params = LoopParams {
                    collection: loop_params.collection,
                    key_reg: loop_params.key_reg,
                    value_reg: loop_params.value_reg,
                    result_reg: loop_params.result_reg,
                    body_start: loop_params.body_start,
                    loop_end: loop_params.loop_end,
                };
                self.execute_loop_start(&mode, params)?;
                Ok(InstructionOutcome::Continue)
            }
            LoopNext {
                body_start,
                loop_end,
            } => {
                self.execute_loop_next(body_start, loop_end)?;
                Ok(InstructionOutcome::Continue)
            }
            Halt {} => {
                let result = self.registers[0].clone();
                Ok(InstructionOutcome::Return(result))
            }
            other => self.execute_virtual_instruction(program, other),
        }
    }

    fn execute_virtual_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            ChainedIndex { params_index } => {
                let params = program
                    .instruction_data
                    .get_chained_index_params(params_index)
                    .ok_or(VmError::InvalidChainedIndexParams {
                        index: params_index,
                    })?;

                let mut current_value = self.registers[params.root as usize].clone();

                for component in &params.path_components {
                    let key_value = match component {
                        LiteralOrRegister::Literal(idx) => program
                            .literals
                            .get(*idx as usize)
                            .ok_or(VmError::LiteralIndexOutOfBounds {
                                index: *idx as usize,
                            })?
                            .clone(),
                        LiteralOrRegister::Register(reg) => self.registers[*reg as usize].clone(),
                    };

                    current_value = current_value[&key_value].clone();

                    if current_value == Value::Undefined {
                        break;
                    }
                }

                self.registers[params.dest as usize] = current_value;
                Ok(InstructionOutcome::Continue)
            }
            VirtualDataDocumentLookup { params_index } => {
                self.execute_virtual_data_document_lookup(params_index)?;
                Ok(InstructionOutcome::Continue)
            }
            ComprehensionBegin { params_index } => {
                let params = program
                    .instruction_data
                    .get_comprehension_begin_params(params_index)
                    .ok_or(VmError::InvalidComprehensionBeginParams {
                        index: params_index,
                    })?
                    .clone();
                self.execute_comprehension_begin(&params)?;
                Ok(InstructionOutcome::Continue)
            }
            ComprehensionYield { value_reg, key_reg } => {
                self.execute_comprehension_yield(value_reg, key_reg)?;
                Ok(InstructionOutcome::Continue)
            }
            ComprehensionEnd {} => {
                self.execute_comprehension_end()?;
                Ok(InstructionOutcome::Continue)
            }
            unexpected => Err(VmError::Internal(alloc::format!(
                "Unhandled instruction variant: {:?}",
                unexpected
            ))),
        }
    }
}
