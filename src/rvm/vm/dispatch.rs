// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::rvm::instructions::{GuardMode, Instruction, LiteralOrRegister};
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
        self.memory_check()?;
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
                if let Some(value) = program.literals.get(usize::from(literal_idx)) {
                    self.set_register(dest, value.clone())?;
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::LiteralIndexOutOfBounds {
                        index: literal_idx,
                        pc: self.pc,
                    })
                }
            }
            LoadTrue { dest } => {
                self.set_register(dest, Value::Bool(true))?;
                Ok(InstructionOutcome::Continue)
            }
            LoadFalse { dest } => {
                self.set_register(dest, Value::Bool(false))?;
                Ok(InstructionOutcome::Continue)
            }
            LoadNull { dest } => {
                self.set_register(dest, Value::Null)?;
                Ok(InstructionOutcome::Continue)
            }
            LoadBool { dest, value } => {
                self.set_register(dest, Value::Bool(value))?;
                Ok(InstructionOutcome::Continue)
            }
            LoadData { dest } => {
                self.set_register(dest, self.data.clone())?;
                Ok(InstructionOutcome::Continue)
            }
            LoadInput { dest } => {
                self.set_register(dest, self.input.clone())?;
                Ok(InstructionOutcome::Continue)
            }
            LoadContext { dest } => {
                self.set_register(dest, self.context.clone())?;
                Ok(InstructionOutcome::Continue)
            }
            LoadMetadata { dest } => {
                self.set_register(dest, self.metadata_value.clone())?;
                Ok(InstructionOutcome::Continue)
            }
            Move { dest, src } => {
                let value = self.get_register(src)?.clone();
                self.set_register(dest, value)?;
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_arithmetic_instruction(program, other),
        }
    }

    fn execute_arithmetic_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Add { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.add_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Sub { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.sub_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Mul { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.mul_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Div { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.div_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Mod { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                let result = self.mod_values(a, b)?;
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_comparison_instruction(program, other),
        }
    }

    fn execute_comparison_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            Eq { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                self.set_register(dest, Value::Bool(a == b))?;
                Ok(InstructionOutcome::Continue)
            }
            Ne { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                self.set_register(dest, Value::Bool(a != b))?;
                Ok(InstructionOutcome::Continue)
            }
            Lt { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a < b))?;
                Ok(InstructionOutcome::Continue)
            }
            Le { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a <= b))?;
                Ok(InstructionOutcome::Continue)
            }
            Gt { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a > b))?;
                Ok(InstructionOutcome::Continue)
            }
            Ge { dest, left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;

                if a == &Value::Undefined || b == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                if self.strict_builtin_errors && mem::discriminant(a) != mem::discriminant(b) {
                    return Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: cannot compare values of different types (left={a:?}, right={b:?})"
                        ),
                        pc: self.pc,
                    });
                }

                self.set_register(dest, Value::Bool(a >= b))?;
                Ok(InstructionOutcome::Continue)
            }
            And { dest, left, right } => {
                let left_value = self.get_register(left)?;
                let right_value = self.get_register(right)?;

                if left_value == &Value::Undefined || right_value == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                match (self.to_bool(left_value), self.to_bool(right_value)) {
                    (Some(a), Some(b)) => {
                        self.set_register(dest, Value::Bool(a && b))?;
                        Ok(InstructionOutcome::Continue)
                    }
                    _ => Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: logical AND expects booleans (left={left_value:?}, right={right_value:?})"
                        ),
                        pc: self.pc,
                    }),
                }
            }
            Or { dest, left, right } => {
                let left_value = self.get_register(left)?;
                let right_value = self.get_register(right)?;

                if left_value == &Value::Undefined || right_value == &Value::Undefined {
                    self.set_register(dest, Value::Undefined)?;
                    return Ok(InstructionOutcome::Continue);
                }

                match (self.to_bool(left_value), self.to_bool(right_value)) {
                    (Some(a), Some(b)) => {
                        self.set_register(dest, Value::Bool(a || b))?;
                        Ok(InstructionOutcome::Continue)
                    }
                    _ => Err(VmError::ArithmeticError {
                        message: alloc::format!(
                            "#undefined: logical OR expects booleans (left={left_value:?}, right={right_value:?})"
                        ),
                        pc: self.pc,
                    }),
                }
            }
            Not { dest, operand } => {
                let operand_value = self.get_register(operand)?;
                let negated = match *operand_value {
                    Value::Undefined => true,
                    Value::Bool(b) => !b,
                    _ => false,
                };
                self.set_register(dest, Value::Bool(negated))?;
                Ok(InstructionOutcome::Continue)
            }
            AssertEq { left, right } => {
                let a = self.get_register(left)?;
                let b = self.get_register(right)?;
                let passed = a != &Value::Undefined && b != &Value::Undefined && a == b;
                self.handle_condition(passed)?;
                Ok(InstructionOutcome::Continue)
            }
            Guard { register, mode } => {
                let value = self.get_register(register)?;
                let passed = match mode {
                    GuardMode::Not => match *value {
                        Value::Undefined => true,
                        Value::Bool(b) => !b,
                        _ => false,
                    },
                    GuardMode::Condition => match *value {
                        Value::Bool(b) => b,
                        Value::Undefined => false,
                        _ => true,
                    },
                    GuardMode::NotUndefined => !matches!(value, Value::Undefined),
                };
                self.handle_condition(passed)?;
                Ok(InstructionOutcome::Continue)
            }
            ReturnUndefinedIfNotTrue { condition } => {
                let value = self.get_register(condition)?;
                if matches!(value, Value::Bool(true)) {
                    Ok(InstructionOutcome::Continue)
                } else {
                    Ok(InstructionOutcome::Return(Value::Undefined))
                }
            }
            CoalesceUndefinedToNull { register } => {
                let value = self.get_register(register)?;
                if matches!(value, Value::Undefined) {
                    self.set_register(register, Value::Null)?;
                }
                Ok(InstructionOutcome::Continue)
            }
            other => self.execute_call_instruction(program, other),
        }
    }

    fn execute_call_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use Instruction::*;
        match instruction {
            BuiltinCall { params_index } => {
                self.execute_builtin_call(params_index)?;
                Ok(InstructionOutcome::Continue)
            }
            HostAwait { dest, arg, id } => {
                let argument = self.get_register(arg)?.clone();
                let identifier = self
                    .registers
                    .get(usize::from(id))
                    .cloned()
                    .unwrap_or(Value::Undefined);
                match self.execution_mode {
                    ExecutionMode::RunToCompletion => {
                        let response = self.next_host_await_response(&identifier, dest)?;
                        self.set_register(dest, response)?;
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
                let result = self.get_register(value)?.clone();
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
            other => self.execute_collection_instruction(program, other),
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
                let key_value = self.get_register(key)?.clone();
                let value_value = self.get_register(value)?.clone();

                // Take ownership so Rc refcount stays at 1 and make_mut is a no-op.
                let mut obj_value = self.take_register(obj)?;

                if let Ok(obj_mut) = obj_value.as_object_mut() {
                    obj_mut.insert(key_value, value_value);
                    self.set_register(obj, obj_value)?;
                } else {
                    let offending = obj_value.clone();
                    self.set_register(obj, obj_value)?;
                    return Err(VmError::RegisterNotObject {
                        register: obj,
                        value: offending,
                        pc: self.pc,
                    });
                }
                Ok(InstructionOutcome::Continue)
            }
            ObjectDeepSet { params_index } => {
                let params = program
                    .instruction_data
                    .get_object_deep_set_params(params_index)
                    .ok_or(VmError::InvalidObjectDeepSetParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.object_deep_set_params.len(),
                    })?;

                // Read all key values and the leaf value upfront
                let key_values: alloc::vec::Vec<Value> = params
                    .keys
                    .iter()
                    .map(|&k| self.get_register(k).cloned())
                    .collect::<core::result::Result<_, _>>()?;
                let leaf_value = self.get_register(params.value)?.clone();
                let multi_value = params.multi_value;
                let obj = params.obj;

                let mut root = self.take_register(obj)?;
                self.object_deep_set(&mut root, &key_values, leaf_value, multi_value, obj)?;
                self.set_register(obj, root)?;
                Ok(InstructionOutcome::Continue)
            }
            ObjectCreate { params_index } => {
                let params = program
                    .instruction_data
                    .get_object_create_params(params_index)
                    .ok_or(VmError::InvalidObjectCreateParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.object_create_params.len(),
                    })?;

                let mut any_undefined = false;

                for &(_, value_reg) in params.literal_key_field_pairs() {
                    if matches!(self.get_register(value_reg)?, Value::Undefined) {
                        any_undefined = true;
                        break;
                    }
                }

                if !any_undefined {
                    for &(key_reg, value_reg) in params.field_pairs() {
                        if matches!(self.get_register(key_reg)?, Value::Undefined)
                            || matches!(self.get_register(value_reg)?, Value::Undefined)
                        {
                            any_undefined = true;
                            break;
                        }
                    }
                }

                if any_undefined {
                    self.set_register(params.dest, Value::Undefined)?;
                } else {
                    let mut obj_value = program
                        .literals
                        .get(usize::from(params.template_literal_idx))
                        .ok_or(VmError::InvalidTemplateLiteralIndex {
                            index: params.template_literal_idx,
                            pc: self.pc,
                            available: program.literals.len(),
                        })?
                        .clone();

                    if let Ok(obj_mut) = obj_value.as_object_mut() {
                        let mut literal_updates = params.literal_key_field_pairs().iter();
                        let mut current_literal_update = literal_updates.next();

                        for (key, value) in obj_mut.iter_mut() {
                            if let Some(&(literal_idx, value_reg)) = current_literal_update {
                                if let Some(literal_key) =
                                    program.literals.get(usize::from(literal_idx))
                                {
                                    if key == literal_key {
                                        *value = self.get_register(value_reg)?.clone();
                                        current_literal_update = literal_updates.next();
                                    }
                                }
                            } else {
                                break;
                            }
                        }

                        while let Some(&(literal_idx, value_reg)) = current_literal_update {
                            if let Some(key_value) = program.literals.get(usize::from(literal_idx))
                            {
                                let value_value = self.get_register(value_reg)?.clone();
                                obj_mut.insert(key_value.clone(), value_value);
                            }
                            current_literal_update = literal_updates.next();
                        }

                        for &(key_reg, value_reg) in params.field_pairs() {
                            let key_value = self.get_register(key_reg)?.clone();
                            let value_value = self.get_register(value_reg)?.clone();
                            obj_mut.insert(key_value, value_value);
                        }
                    } else {
                        return Err(VmError::ObjectCreateInvalidTemplate {
                            template: obj_value,
                            pc: self.pc,
                        });
                    }

                    self.set_register(params.dest, obj_value)?;
                }
                Ok(InstructionOutcome::Continue)
            }
            Index {
                dest,
                container,
                key,
            } => {
                let key_value = self.get_register(key)?;
                let container_value = self.get_register(container)?;
                let result = container_value[key_value].clone();
                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            IndexLiteral {
                dest,
                container,
                literal_idx,
            } => {
                let container_value = self.get_register(container)?;

                if let Some(key_value) = program.literals.get(usize::from(literal_idx)) {
                    let result = container_value[key_value].clone();
                    self.set_register(dest, result)?;
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::LiteralIndexOutOfBounds {
                        index: literal_idx,
                        pc: self.pc,
                    })
                }
            }
            ArrayNew { dest } => {
                let empty_array = Value::Array(crate::Rc::new(Vec::new()));
                self.set_register(dest, empty_array)?;
                Ok(InstructionOutcome::Continue)
            }
            ArrayPush { arr, value } => {
                let value_to_push = self.get_register(value)?.clone();

                // Take ownership so Rc refcount stays at 1 and make_mut is a no-op.
                let mut arr_value = self.take_register(arr)?;

                if let Ok(arr_mut) = arr_value.as_array_mut() {
                    arr_mut.push(value_to_push);
                    self.set_register(arr, arr_value)?;
                } else {
                    let offending = arr_value.clone();
                    self.set_register(arr, arr_value)?;
                    return Err(VmError::RegisterNotArray {
                        register: arr,
                        value: offending,
                        pc: self.pc,
                    });
                }
                Ok(InstructionOutcome::Continue)
            }
            ArrayPushDefined { arr, value } => {
                // Skip undefined values — matches Azure Policy's
                // `field('alias[*].property')` collection semantics where
                // absent nested properties are excluded from the collected
                // array.
                if self.get_register(value)? == &Value::Undefined {
                    return Ok(InstructionOutcome::Continue);
                }

                let value_to_push = self.get_register(value)?.clone();

                let mut arr_value = self.take_register(arr)?;

                if let Ok(arr_mut) = arr_value.as_array_mut() {
                    arr_mut.push(value_to_push);
                    self.set_register(arr, arr_value)?;
                } else {
                    let offending = arr_value.clone();
                    self.set_register(arr, arr_value)?;
                    return Err(VmError::RegisterNotArray {
                        register: arr,
                        value: offending,
                        pc: self.pc,
                    });
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
                        if matches!(self.get_register(reg)?, Value::Undefined) {
                            any_undefined = true;
                            break;
                        }
                    }

                    if any_undefined {
                        self.set_register(params.dest, Value::Undefined)?;
                    } else {
                        let elements: Vec<Value> = params
                            .element_registers()
                            .iter()
                            .map(|&reg| self.get_register(reg).cloned())
                            .collect::<Result<Vec<_>>>()?;

                        let array_value = Value::Array(crate::Rc::new(elements));
                        self.set_register(params.dest, array_value)?;
                    }
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::InvalidArrayCreateParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.array_create_params.len(),
                    })
                }
            }
            SetNew { dest } => {
                let empty_set = Value::Set(crate::Rc::new(BTreeSet::new()));
                self.set_register(dest, empty_set)?;
                Ok(InstructionOutcome::Continue)
            }
            SetAdd { set, value } => {
                let value_to_add = self.get_register(value)?.clone();

                // Take ownership so Rc refcount stays at 1 and make_mut is a no-op.
                let mut set_value = self.take_register(set)?;

                if let Ok(set_mut) = set_value.as_set_mut() {
                    set_mut.insert(value_to_add);
                    self.set_register(set, set_value)?;
                } else {
                    let offending = set_value.clone();
                    self.set_register(set, set_value)?;
                    return Err(VmError::RegisterNotSet {
                        register: set,
                        value: offending,
                        pc: self.pc,
                    });
                }
                Ok(InstructionOutcome::Continue)
            }
            SetCreate { params_index } => {
                if let Some(params) = program.instruction_data.get_set_create_params(params_index) {
                    let mut any_undefined = false;
                    for &reg in params.element_registers() {
                        if matches!(self.get_register(reg)?, Value::Undefined) {
                            any_undefined = true;
                            break;
                        }
                    }

                    if any_undefined {
                        self.set_register(params.dest, Value::Undefined)?;
                    } else {
                        let mut set = BTreeSet::new();
                        for &reg in params.element_registers() {
                            set.insert(self.get_register(reg)?.clone());
                        }

                        let set_value = Value::Set(crate::Rc::new(set));
                        self.set_register(params.dest, set_value)?;
                    }
                    Ok(InstructionOutcome::Continue)
                } else {
                    Err(VmError::InvalidSetCreateParams {
                        index: params_index,
                        pc: self.pc,
                        available: program.instruction_data.set_create_params.len(),
                    })
                }
            }
            Contains {
                dest,
                collection,
                value,
            } => {
                let value_to_check = self.get_register(value)?;
                let collection_value = self.get_register(collection)?;

                let result = match *collection_value {
                    Value::Set(ref set_elements) => {
                        Value::Bool(set_elements.contains(value_to_check))
                    }
                    Value::Array(ref array_items) => {
                        Value::Bool(array_items.contains(value_to_check))
                    }
                    Value::Object(ref object_fields) => {
                        Value::Bool(object_fields.values().any(|v| v == value_to_check))
                    }
                    _ => Value::Bool(false),
                };

                self.set_register(dest, result)?;
                Ok(InstructionOutcome::Continue)
            }
            Count { dest, collection } => {
                let collection_value = self.get_register(collection)?;

                let result = match *collection_value {
                    Value::Array(ref array_items) => Value::from(array_items.len()),
                    Value::Object(ref object_fields) => Value::from(object_fields.len()),
                    Value::Set(ref set_elements) => Value::from(set_elements.len()),
                    _ => Value::Undefined,
                };

                self.set_register(dest, result)?;
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
                let loop_params_len = program.instruction_data.loop_params.len();

                let loop_params = program
                    .instruction_data
                    .get_loop_params(params_index)
                    .ok_or(VmError::InvalidLoopParams {
                        index: params_index,
                        pc: self.pc,
                        available: loop_params_len,
                    })?;
                let mode = loop_params.mode;

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
                let result = self.get_register(0)?.clone();
                Ok(InstructionOutcome::Return(result))
            }
            other => self.execute_policy_instruction(program, other),
        }
    }

    #[cfg(not(feature = "azure_policy"))]
    fn execute_policy_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        match instruction {
            instruction @ (Instruction::PolicyCondition { .. }
            | Instruction::LogicalBlockStart { .. }
            | Instruction::LogicalBlockEnd { .. }
            | Instruction::AllOfNext { .. }
            | Instruction::AnyOfNext { .. }) => Err(VmError::UnhandledInstruction {
                instruction: alloc::format!("{:?} requires the azure_policy feature", instruction),
                pc: self.pc,
            }),
            other => self.execute_virtual_instruction(program, other),
        }
    }

    /// Check whether `l` "contains" `r` using Azure Policy semantics.
    ///
    /// Works on strings (case-insensitive substring), arrays/sets (element
    /// membership), and objects (key membership). For string haystacks,
    /// non-string scalar RHS values are coerced to strings before the
    /// substring check. For non-string scalar LHS values, coercion to string
    /// only happens when the RHS is already a string.
    #[cfg(feature = "azure_policy")]
    #[inline]
    fn policy_contains_check(l: &Value, r: &Value) -> bool {
        use crate::builtins::azure_policy::helpers::{case_insensitive_equals, coerce_to_string};
        use crate::languages::azure_policy::strings;

        match *l {
            Value::String(ref haystack) => match *r {
                Value::String(ref needle) => strings::case_fold::contains(haystack, needle),
                _ => coerce_to_string(r)
                    .is_some_and(|needle| strings::case_fold::contains(haystack, &needle)),
            },
            Value::Array(ref items) => items.iter().any(|item| case_insensitive_equals(item, r)),
            Value::Set(ref items) => items.iter().any(|item| case_insensitive_equals(item, r)),
            // ARM template contains(object, key) checks key membership.
            Value::Object(ref map) => map.keys().any(|key| case_insensitive_equals(key, r)),
            // Coerce non-string scalar LHS (e.g., count result)
            // to a string only when the RHS is already a string.
            _ => {
                if let Value::String(ref needle) = *r {
                    coerce_to_string(l)
                        .is_some_and(|haystack| strings::case_fold::contains(&haystack, needle))
                } else {
                    false
                }
            }
        }
    }

    /// Evaluate a Policy comparison operator.  Undefined LHS → false.
    #[cfg(feature = "azure_policy")]
    fn policy_compare(
        &mut self,
        dest: u8,
        left: u8,
        right: u8,
        cmp: fn(i8) -> bool,
    ) -> Result<InstructionOutcome> {
        use crate::builtins::azure_policy::helpers::{compare_values, is_undefined};

        let l = self.get_register(left)?;
        if is_undefined(l) {
            self.set_register(dest, Value::Bool(false))?;
        } else {
            let r = self.get_register(right)?;
            let result = compare_values(l, r).is_some_and(cmp);
            self.set_register(dest, Value::Bool(result))?;
        }
        Ok(InstructionOutcome::Continue)
    }

    #[cfg(feature = "azure_policy")]
    fn execute_policy_instruction(
        &mut self,
        program: &Program,
        instruction: Instruction,
    ) -> Result<InstructionOutcome> {
        use crate::builtins::azure_policy::helpers::{
            as_boolish, case_insensitive_equals, coerce_to_string_ci,
            collection_any_ci_eq_excluding_null, collection_has_null, is_true, is_undefined,
            match_like_pattern_ci, match_pattern,
        };
        use crate::rvm::instructions::{LogicalBlockMode, PolicyOp};

        use Instruction::*;
        match instruction {
            PolicyCondition {
                dest,
                left,
                right,
                op,
            } => {
                let l = self.get_register(left)?;
                let result = match op {
                    PolicyOp::Equals => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            matches!(r, Value::Null)
                        } else {
                            case_insensitive_equals(l, r)
                        }
                    }
                    PolicyOp::NotEquals => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            !matches!(r, Value::Null)
                        } else {
                            !case_insensitive_equals(l, r)
                        }
                    }
                    PolicyOp::Greater => {
                        return self.policy_compare(dest, left, right, |c| c > 0);
                    }
                    PolicyOp::GreaterOrEquals => {
                        return self.policy_compare(dest, left, right, |c| c >= 0);
                    }
                    PolicyOp::Less => {
                        return self.policy_compare(dest, left, right, |c| c < 0);
                    }
                    PolicyOp::LessOrEquals => {
                        return self.policy_compare(dest, left, right, |c| c <= 0);
                    }
                    PolicyOp::In => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            collection_has_null(r)
                        } else if matches!(*l, Value::Null) || is_undefined(r) {
                            false
                        } else {
                            collection_any_ci_eq_excluding_null(r, l)
                        }
                    }
                    PolicyOp::NotIn => {
                        let r = self.get_register(right)?;
                        if is_undefined(l) {
                            !collection_has_null(r)
                        } else if matches!(*l, Value::Null) || is_undefined(r) {
                            true
                        } else {
                            !collection_any_ci_eq_excluding_null(r, l)
                        }
                    }
                    PolicyOp::Contains | PolicyOp::NotContains => {
                        let negated = op.is_negated();
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            if is_undefined(r) {
                                // undefined RHS: positive → false, negated → false
                                false
                            } else {
                                negated ^ Self::policy_contains_check(l, r)
                            }
                        }
                    }
                    PolicyOp::ContainsKey | PolicyOp::NotContainsKey => {
                        let negated = op.is_negated();
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            if is_undefined(r) {
                                false
                            } else {
                                let found = match *l {
                                    Value::Object(ref map) => {
                                        map.keys().any(|key| case_insensitive_equals(key, r))
                                    }
                                    _ => false,
                                };
                                negated ^ found
                            }
                        }
                    }
                    PolicyOp::Like | PolicyOp::NotLike => {
                        let negated = op.is_negated();
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            let positive = match (coerce_to_string_ci(l), coerce_to_string_ci(r)) {
                                (Some(input), Some(pattern)) => {
                                    match_like_pattern_ci(&input, &pattern)
                                }
                                _ => false,
                            };
                            negated ^ positive
                        }
                    }
                    PolicyOp::Match
                    | PolicyOp::NotMatch
                    | PolicyOp::MatchInsensitively
                    | PolicyOp::NotMatchInsensitively => {
                        let negated = op.is_negated();
                        let case_insensitive = matches!(
                            op,
                            PolicyOp::MatchInsensitively | PolicyOp::NotMatchInsensitively
                        );
                        if is_undefined(l) {
                            negated
                        } else {
                            let r = self.get_register(right)?;
                            negated ^ match_pattern(l, r, case_insensitive)
                        }
                    }
                    PolicyOp::Exists => {
                        let r = self.get_register(right)?;
                        let expected = as_boolish(r).unwrap_or(false);
                        let is_defined = !is_undefined(l) && !matches!(l, Value::Null);
                        is_defined == expected
                    }
                    PolicyOp::ValueConditionGuard => {
                        // left = value register, right = condition register
                        if is_undefined(l) {
                            self.set_register(dest, Value::Bool(false))?;
                            return Ok(InstructionOutcome::Continue);
                        } else {
                            let c = self.get_register(right)?.clone();
                            self.set_register(dest, c)?;
                            return Ok(InstructionOutcome::Continue);
                        }
                    }
                    PolicyOp::Not => {
                        // left = operand, right unused
                        !is_true(l)
                    }
                };
                self.set_register(dest, Value::Bool(result))?;
                Ok(InstructionOutcome::Continue)
            }

            // AllOf / AnyOf structured instructions
            LogicalBlockStart {
                mode: _,
                result,
                end_pc: _,
            } => {
                // Initialize result to false (pessimistic).
                self.set_register(result, Value::Bool(false))?;
                Ok(InstructionOutcome::Continue)
            }
            AllOfNext {
                check,
                result,
                end_pc,
            } => {
                let val = self.get_register(check)?;
                if !matches!(val, Value::Bool(true)) {
                    // Child failed — short-circuit. Ensure the block result is false.
                    self.set_register(result, Value::Bool(false))?;
                    self.pc = usize::from(end_pc);
                }
                Ok(InstructionOutcome::Continue)
            }
            AnyOfNext {
                check,
                result,
                end_pc,
            } => {
                let val = self.get_register(check)?;
                if matches!(val, Value::Bool(true)) {
                    // Child succeeded — short-circuit.
                    self.set_register(result, Value::Bool(true))?;
                    self.pc = usize::from(end_pc);
                }
                Ok(InstructionOutcome::Continue)
            }
            LogicalBlockEnd { mode, result } => {
                match mode {
                    LogicalBlockMode::AllOf => {
                        // All children passed — set result to true.
                        self.set_register(result, Value::Bool(true))?;
                    }
                    LogicalBlockMode::AnyOf => {
                        // No child matched — result stays false (set by LogicalBlockStart).
                    }
                }
                Ok(InstructionOutcome::Continue)
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
                        pc: self.pc,
                        available: program.instruction_data.chained_index_params.len(),
                    })?;

                let mut current_value = self.get_register(params.root)?.clone();

                for component in &params.path_components {
                    let key_value = match *component {
                        LiteralOrRegister::Literal(idx) => program
                            .literals
                            .get(usize::from(idx))
                            .ok_or(VmError::LiteralIndexOutOfBounds {
                                index: idx,
                                pc: self.pc,
                            })?
                            .clone(),
                        LiteralOrRegister::Register(reg) => self.get_register(reg)?.clone(),
                    };

                    current_value = current_value[&key_value].clone();

                    if current_value == Value::Undefined {
                        break;
                    }
                }

                self.set_register(params.dest, current_value)?;
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
                        pc: self.pc,
                        available: program.instruction_data.comprehension_begin_params.len(),
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
            unexpected => Err(VmError::UnhandledInstruction {
                instruction: alloc::format!("{:?}", unexpected),
                pc: self.pc,
            }),
        }
    }

    fn object_deep_set(
        &self,
        current: &mut Value,
        key_values: &[Value],
        leaf_value: Value,
        multi_value: bool,
        obj_register: u8,
    ) -> Result<()> {
        let Some((first_key, remaining_keys)) = key_values.split_first() else {
            return Err(VmError::Internal {
                message: alloc::string::String::from("ObjectDeepSet requires a non-empty key path"),
                pc: self.pc,
            });
        };

        let object = match current.as_object_mut() {
            Ok(obj) => obj,
            Err(_) => {
                return Err(VmError::RegisterNotObject {
                    register: obj_register,
                    value: current.clone(),
                    pc: self.pc,
                });
            }
        };

        if remaining_keys.is_empty() {
            if multi_value {
                let leaf = match object.entry(first_key.clone()) {
                    alloc::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
                    alloc::collections::btree_map::Entry::Vacant(entry) => {
                        entry.insert(Value::new_set())
                    }
                };

                let leaf_snapshot = leaf.clone();
                let set = leaf.as_set_mut().map_err(|_| VmError::RegisterNotSet {
                    register: obj_register,
                    value: leaf_snapshot,
                    pc: self.pc,
                })?;
                set.insert(leaf_value);
            } else {
                object.insert(first_key.clone(), leaf_value);
            }

            return Ok(());
        }

        let child = match object.entry(first_key.clone()) {
            alloc::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
            alloc::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(Value::new_object())
            }
        };

        if !matches!(child, Value::Object(_)) {
            return Err(VmError::RegisterNotObject {
                register: obj_register,
                value: child.clone(),
                pc: self.pc,
            });
        }

        self.object_deep_set(child, remaining_keys, leaf_value, multi_value, obj_register)
    }
}
