// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Delivery of evaluation events to an installed [`ExplanationRecorder`].
//!
//! Hook sites check [`RegoVM::explain_enabled`] and call the cold functions
//! here only when a recorder is installed.

use alloc::boxed::Box;
use alloc::string::String;
use core::fmt;

use crate::builtins::types::get_type;
use crate::explain::{
    BodyEndEvent, BuiltinErrorEvent, CheckEvent, ConditionKind, EmissionEvent, ExplanationRecorder,
    HookContext, NotCapturedEvent, Operator, Outcome, UncapturedConstruct,
};
use crate::rvm::instructions::{GuardMode, Instruction, LoopMode};
use crate::rvm::program::{Program, RuleType};
use crate::value::Value;

use super::errors::{Result, VmError};
use super::execution_model::{ExecutionMode, FrameKind, RuleFramePhase};
use super::machine::RegoVM;

#[derive(Default)]
pub(super) struct ExplainHooks {
    recorder: Option<Box<dyn ExplanationRecorder>>,
    /// Run-to-completion only: smallest call depth whose frame was inside a
    /// comprehension when it called the rule or function executing above it.
    comprehension_floor: Option<usize>,
    /// Run-to-completion only: call depth of the rule or function whose
    /// parameter patterns are executing.
    parameters_depth: Option<usize>,
}

impl fmt::Debug for ExplainHooks {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ExplainHooks")
            .field("recorder", &self.recorder.is_some())
            .finish()
    }
}

/// The checked expression of a guard, read from the instruction that
/// computed the guarded register.
struct Checked<'a> {
    kind: ConditionKind,
    operator: Option<Operator>,
    left: &'a Value,
    right: Option<&'a Value>,
}

impl<'a> Checked<'a> {
    const fn event(self, outcome: Outcome) -> CheckEvent<'a> {
        CheckEvent {
            kind: self.kind,
            operator: self.operator,
            left: self.left,
            right: self.right,
            outcome,
        }
    }
}

impl RegoVM {
    /// Installs a recorder that receives this VM's evaluation events,
    /// replacing any previous one. Recording slows evaluation; without a
    /// recorder, evaluation is unaffected.
    #[cfg_attr(docsrs, doc(cfg(feature = "explanations")))]
    pub fn set_explanation_recorder(&mut self, recorder: Box<dyn ExplanationRecorder>) {
        self.explain.recorder = Some(recorder);
    }

    /// Removes and returns the installed recorder.
    #[cfg_attr(docsrs, doc(cfg(feature = "explanations")))]
    pub fn take_explanation_recorder(&mut self) -> Option<Box<dyn ExplanationRecorder>> {
        self.explain.recorder.take()
    }

    #[inline(always)]
    pub(super) const fn explain_enabled(&self) -> bool {
        self.explain.recorder.is_some()
    }

    fn explain_context(&self) -> HookContext {
        self.explain_context_at(self.pc)
    }

    /// Context of an event reported at `pc`, the check site of the event in
    /// [`Provenance`](crate::explain::Provenance) when it is a check.
    fn explain_context_at(&self, pc: usize) -> HookContext {
        let call_depth = self.call_rule_stack.len();
        let in_comprehension = match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                !self.comprehension_stack.is_empty()
                    || self
                        .explain
                        .comprehension_floor
                        .is_some_and(|floor| floor < call_depth)
            }
            ExecutionMode::Suspendable => (0..self.execution_stack.len()).any(|i| {
                matches!(
                    self.execution_stack.get(i).map(|frame| &frame.kind),
                    Some(FrameKind::Comprehension { .. })
                )
            }),
        };
        let rule = self.call_rule_stack.last();
        HookContext {
            pc,
            rule_index: rule.map(|ctx| ctx.rule_index),
            definition_index: rule.map_or(0, |ctx| ctx.current_definition_index),
            body_index: rule.map_or(0, |ctx| ctx.current_body_index),
            call_depth,
            in_comprehension,
        }
    }

    /// Whether the executing instructions match a rule's or function's
    /// parameter patterns, which are not checks of its body.
    fn explain_in_parameters(&self) -> bool {
        match self.execution_mode {
            ExecutionMode::RunToCompletion => {
                self.explain.parameters_depth == Some(self.call_rule_stack.len())
            }
            ExecutionMode::Suspendable => (0..self.execution_stack.len())
                .rev()
                .find_map(|i| match self.execution_stack.get(i)?.kind {
                    FrameKind::Rule(ref data) => Some(data.phase),
                    _ => None,
                })
                .is_some_and(|phase| phase == RuleFramePhase::ExecutingDestructuring),
        }
    }

    /// Run-to-completion: called before a definition's parameter patterns
    /// are matched. Returns the state to pass to
    /// [`explain_leave_parameters`](Self::explain_leave_parameters).
    pub(super) const fn explain_enter_parameters(&mut self) -> Option<usize> {
        let depth = self.call_rule_stack.len();
        self.explain.parameters_depth.replace(depth)
    }

    pub(super) const fn explain_leave_parameters(&mut self, outer: Option<usize>) {
        self.explain.parameters_depth = outer;
    }

    fn explain_register(&self, register: u8) -> &Value {
        self.registers
            .get(usize::from(register))
            .unwrap_or(&Value::Undefined)
    }

    /// Called after the execution timer starts, so that the recorder's
    /// reset counts toward the time limit.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_reset(&mut self) {
        self.explain.comprehension_floor = None;
        self.explain.parameters_depth = None;
        // Taken while it runs, so that a panicking recorder is dropped.
        if let Some(mut recorder) = self.explain.recorder.take() {
            recorder.reset();
            self.explain.recorder = Some(recorder);
        }
    }

    /// Run-to-completion: called before a rule or function call is pushed.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_rule_call(&mut self) {
        let caller_depth = self.call_rule_stack.len();
        if self
            .explain
            .comprehension_floor
            .is_some_and(|floor| floor < caller_depth)
        {
            return;
        }
        self.explain.comprehension_floor =
            (!self.comprehension_stack.is_empty()).then_some(caller_depth);
    }

    /// Temporarily takes the recorder so that events can borrow the VM.
    fn explain_deliver(&mut self, deliver: impl FnOnce(&Self, &mut dyn ExplanationRecorder)) {
        if let Some(mut recorder) = self.explain.recorder.take() {
            deliver(self, recorder.as_mut());
            self.explain.recorder = Some(recorder);
        }
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_guard(
        &mut self,
        program: &Program,
        register: u8,
        mode: GuardMode,
        passed: bool,
    ) {
        // Azure Policy programs (which set `virtual_element_on_non_collection`)
        // compile their conditions to guards; those are not reported.
        if (mode == GuardMode::NotUndefined && passed)
            || self.virtual_element_on_non_collection
            || self.explain_in_parameters()
        {
            return;
        }
        self.explain_deliver(|vm, recorder| {
            if let Some((pc, event)) = vm.explain_guard_event(program, register, mode, passed) {
                recorder.check(&vm.explain_context_at(pc), &event);
            }
        });
    }

    /// Returns `None` for guards that are not checks of their own, such as
    /// the end of a `some` iteration. Otherwise returns the event and the pc
    /// of its check site: the guard's own, except for an `every` quantifier,
    /// whose site is its `LoopStart`.
    fn explain_guard_event(
        &self,
        program: &Program,
        register: u8,
        mode: GuardMode,
        passed: bool,
    ) -> Option<(usize, CheckEvent<'_>)> {
        let mut site = self.pc;
        let value = self.explain_register(register);
        if mode == GuardMode::NotUndefined {
            return Some((
                site,
                CheckEvent {
                    kind: ConditionKind::Existence,
                    operator: None,
                    left: value,
                    right: None,
                    outcome: Outcome::Undefined,
                },
            ));
        }
        let mut outcome = if mode == GuardMode::Condition && *value == Value::Undefined {
            Outcome::Undefined
        } else {
            passed_outcome(passed)
        };
        let mut checked = Checked {
            kind: if mode == GuardMode::Not {
                ConditionKind::Negation
            } else {
                ConditionKind::Truthiness
            },
            operator: None,
            left: value,
            right: None,
        };
        let previous = self.pc.checked_sub(1);
        let previous = previous.and_then(|pc| program.instructions.get(pc));
        match previous {
            _ if mode != GuardMode::Condition => {}
            Some(&Instruction::Not { dest, operand }) if dest == register => {
                if let Some((found, undefined)) =
                    self.explain_keyed_membership(program, self.pc, register)
                {
                    if undefined {
                        outcome = Outcome::Undefined;
                    }
                    return Some((site, found.event(outcome)));
                }
                checked.kind = ConditionKind::Negation;
                checked.left = self.explain_register(operand);
                let inner = self.pc.checked_sub(2);
                let negated_membership = self
                    .pc
                    .checked_sub(1)
                    .filter(|_| operand != dest)
                    .and_then(|end| self.explain_keyed_membership(program, end, operand));
                if let Some((found, _)) = negated_membership {
                    checked = Checked {
                        kind: ConditionKind::Negation,
                        ..found
                    };
                } else if let Some(&inner) = inner.and_then(|pc| program.instructions.get(pc)) {
                    if let Some(found) = self.explain_operation(inner, operand, dest) {
                        checked = Checked {
                            kind: ConditionKind::Negation,
                            ..found
                        };
                    }
                }
            }
            Some(&Instruction::LoopNext {
                body_start,
                loop_end,
            }) if usize::from(loop_end) == self.pc => {
                let start = usize::from(body_start).checked_sub(1);
                let params = match start.and_then(|pc| program.instructions.get(pc)) {
                    Some(&Instruction::LoopStart { params_index }) => {
                        program.instruction_data.get_loop_params(params_index)
                    }
                    _ => None,
                };
                if let Some(params) = params.filter(|params| params.result_reg == register) {
                    if params.mode != LoopMode::Every {
                        return None;
                    }
                    checked.kind = ConditionKind::Iteration;
                    checked.left = self.explain_register(params.collection);
                    site = start.unwrap_or(site);
                }
            }
            Some(&previous) => {
                if let Some(found) = self.explain_operation(previous, register, register) {
                    if found.left == &Value::Undefined
                        || found.right.is_some_and(|right| right == &Value::Undefined)
                    {
                        outcome = Outcome::Undefined;
                    }
                    checked = found;
                }
            }
            None => {}
        }
        Some((site, checked.event(outcome)))
    }

    /// Keyed membership (`key, value in collection`) is compiled to `Index`,
    /// `Eq` and two in-place `Not`s on the guarded register, so that a
    /// missing key gives `false` instead of undefined. Decodes it as the
    /// membership test it is rather than as a negation, with the key on the
    /// left and the collection on the right, and whether it is undefined.
    ///
    /// `end` is the pc after the second `Not`, which writes `register`.
    ///
    /// The key is evaluated only when the value and the collection are
    /// defined and the collection is an array or an object; otherwise the
    /// key's register was not written and the key is reported as undefined.
    fn explain_keyed_membership(
        &self,
        program: &Program,
        end: usize,
        register: u8,
    ) -> Option<(Checked<'_>, bool)> {
        let instruction = |offset: usize| {
            end.checked_sub(offset)
                .and_then(|pc| program.instructions.get(pc))
                .copied()
        };
        match (
            instruction(1)?,
            instruction(2)?,
            instruction(3)?,
            instruction(4)?,
        ) {
            (
                Instruction::Not {
                    dest: first_dest,
                    operand: first_operand,
                },
                Instruction::Not {
                    dest: second_dest,
                    operand: second_operand,
                },
                Instruction::Eq {
                    dest: eq_dest,
                    left: indexed,
                    right: value,
                },
                Instruction::Index {
                    dest: index_dest,
                    container,
                    key,
                },
            ) if first_dest == register
                && first_operand == register
                && second_dest == register
                && second_operand == register
                && eq_dest == register
                && indexed == index_dest
                && index_dest != key
                && index_dest != container
                && key != register
                && container != register
                && value != register =>
            {
                let collection = self.explain_register(container);
                let evaluated = self.explain_register(value) != &Value::Undefined
                    && matches!(collection, Value::Array(_) | Value::Object(_));
                let key = if evaluated {
                    self.explain_register(key)
                } else {
                    &Value::Undefined
                };
                let undefined = if evaluated {
                    key == &Value::Undefined
                } else {
                    collection == &Value::Undefined
                        || self.explain_register(value) == &Value::Undefined
                };
                Some((
                    Checked {
                        kind: ConditionKind::Membership,
                        operator: Some(Operator::In),
                        left: key,
                        right: Some(collection),
                    },
                    undefined,
                ))
            }
            _ => None,
        }
    }

    /// Decodes a comparison or membership test that wrote `target`, provided
    /// its operands still hold their values (neither is `target` nor
    /// `clobbered`, which later instructions overwrote).
    fn explain_operation(
        &self,
        instruction: Instruction,
        target: u8,
        clobbered: u8,
    ) -> Option<Checked<'_>> {
        let (operator, written, left, right) = match instruction {
            Instruction::Eq { dest, left, right } => (Operator::Eq, dest, left, right),
            Instruction::Ne { dest, left, right } => (Operator::Ne, dest, left, right),
            Instruction::Lt { dest, left, right } => (Operator::Lt, dest, left, right),
            Instruction::Le { dest, left, right } => (Operator::Le, dest, left, right),
            Instruction::Gt { dest, left, right } => (Operator::Gt, dest, left, right),
            Instruction::Ge { dest, left, right } => (Operator::Ge, dest, left, right),
            Instruction::Contains {
                dest,
                collection,
                value,
            } => (Operator::In, dest, value, collection),
            _ => return None,
        };
        let intact = |reg: u8| reg != target && reg != clobbered;
        (written == target && intact(left) && intact(right)).then(|| Checked {
            kind: if operator == Operator::In {
                ConditionKind::Membership
            } else {
                ConditionKind::Comparison
            },
            operator: Some(operator),
            left: self.explain_register(left),
            right: Some(self.explain_register(right)),
        })
    }

    /// Called at a `LoopStart`, the iteration's check site, whose
    /// collection is undefined. The body continues with no iteration.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_undefined_collection(&mut self) {
        if self.explain_in_parameters() {
            return;
        }
        self.explain_deliver(|vm, recorder| {
            let event = CheckEvent {
                kind: ConditionKind::Iteration,
                operator: None,
                left: &Value::Undefined,
                right: None,
                outcome: Outcome::Undefined,
            };
            recorder.check(&vm.explain_context(), &event);
        });
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_assert_eq(&mut self, left: u8, right: u8, passed: bool) {
        if self.explain_in_parameters() {
            return;
        }
        self.explain_deliver(|vm, recorder| {
            let left = vm.explain_register(left);
            let right = vm.explain_register(right);
            let outcome = if left == &Value::Undefined || right == &Value::Undefined {
                Outcome::Undefined
            } else {
                passed_outcome(passed)
            };
            let event = CheckEvent {
                kind: ConditionKind::Comparison,
                operator: Some(Operator::Eq),
                left,
                right: Some(right),
                outcome,
            };
            recorder.check(&vm.explain_context(), &event);
        });
    }

    /// With strict builtin errors, an ordering comparison of values of
    /// different types raised an error instead of writing `dest`. Reported
    /// only when the comparison is checked, as decoded for guards: directly
    /// (an undefined comparison) or under `not` (a failed negation).
    #[cold]
    #[inline(never)]
    pub(super) fn explain_comparison_error(
        &mut self,
        program: &Program,
        operator: Operator,
        dest: u8,
        left: u8,
        right: u8,
    ) {
        if self.virtual_element_on_non_collection || self.explain_in_parameters() {
            return;
        }
        let next = |offset: usize| {
            self.pc
                .checked_add(offset)
                .and_then(|pc| program.instructions.get(pc))
        };
        // The check's site is its guard: the next instruction, or the one
        // after the `Not` of a negated comparison.
        let negated = match (next(1), next(2)) {
            (
                Some(&Instruction::Guard {
                    register,
                    mode: GuardMode::Condition,
                }),
                _,
            ) if register == dest => false,
            (
                Some(&Instruction::Not {
                    dest: negated,
                    operand,
                }),
                Some(&Instruction::Guard {
                    register,
                    mode: GuardMode::Condition,
                }),
            ) if operand == dest && register == negated => true,
            _ => return,
        };
        let site = self.pc.saturating_add(if negated { 2 } else { 1 });
        self.explain_deliver(|vm, recorder| {
            let event = CheckEvent {
                kind: if negated {
                    ConditionKind::Negation
                } else {
                    ConditionKind::Comparison
                },
                operator: Some(operator),
                left: vm.explain_register(left),
                right: Some(vm.explain_register(right)),
                outcome: if negated {
                    Outcome::Failure
                } else {
                    Outcome::Undefined
                },
            };
            recorder.check(&vm.explain_context_at(site), &event);
        });
    }

    /// Called after `target` was written with `key` and `value`, as read
    /// before the write. Only writes to the executing partial rule's result
    /// are emissions; `key` is `None` for a set element.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_emission(&mut self, target: u8, key: Option<&Value>, value: &Value) {
        let emits = self.call_rule_stack.last().is_some_and(|ctx| {
            ctx.result_reg == target
                && match ctx.rule_type {
                    RuleType::PartialSet => key.is_none(),
                    RuleType::PartialObject => key.is_some(),
                    RuleType::Complete => false,
                }
        });
        if !emits {
            return;
        }
        self.explain_deliver(|vm, recorder| {
            if value == &Value::Undefined || key.is_some_and(|key| key == &Value::Undefined) {
                return;
            }
            let event = EmissionEvent { key, value };
            recorder.emission(&vm.explain_context(), &event);
        });
    }

    /// `result_reg` is the register holding a complete rule's or a
    /// function's value, if the body succeeded.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_body_end(&mut self, succeeded: bool, result_reg: Option<u8>) {
        self.explain_deliver(|vm, recorder| {
            let event = BodyEndEvent {
                outcome: passed_outcome(succeeded),
                result: result_reg
                    .filter(|_| succeeded)
                    .map(|reg| vm.explain_register(reg)),
            };
            recorder.body_end(&vm.explain_context(), &event);
        });
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_builtin_error(
        &mut self,
        builtin_index: u16,
        args: &[Value],
        error: &anyhow::Error,
    ) {
        // Both end the evaluation, like the operators' fatal errors.
        if error.downcast_ref::<crate::LimitError>().is_some()
            || (self.strict_builtin_errors
                && error
                    .downcast_ref::<crate::number::NumericOverflowError>()
                    .is_some())
        {
            return;
        }
        self.explain_deliver(|vm, recorder| {
            let name = vm
                .program
                .get_builtin_info(builtin_index)
                .map_or("", |info| info.name.as_str());
            // The set operators `|` and `&` are compiled to internal builtins.
            let operator = match name {
                "__builtin_sets.union" => Some("or"),
                "__builtin_sets.intersection" => Some("and"),
                _ => None,
            };
            let message = operator
                .and_then(|_| {
                    operand_type_message(args, "set", |arg| matches!(*arg, Value::Set(_)))
                })
                .unwrap_or_else(|| without_source_frame(&alloc::format!("{error:#}")).into());
            let event = BuiltinErrorEvent {
                name: operator.unwrap_or(name),
                message: &message,
                raised: vm.strict_builtin_errors,
            };
            recorder.builtin_error(&vm.explain_context(), &event);
        });
    }

    /// Reports an arithmetic operator's error, or its undefined result when
    /// dividing by zero. `name` is the operator's builtin name, such as
    /// `"plus"`.
    #[cold]
    #[inline(never)]
    pub(super) fn explain_arithmetic(&mut self, name: &str, result: &Result<Value>) {
        let (message, raised) = match *result {
            Err(ref error) if self.is_fatal_vm_error(error) => return,
            Err(ref error) => (arithmetic_message(error), true),
            Ok(Value::Undefined) if name == "div" => ("divide by zero".into(), false),
            Ok(Value::Undefined) if name == "rem" => ("modulo by zero".into(), false),
            Ok(_) => return,
        };
        self.explain_deliver(|vm, recorder| {
            let event = BuiltinErrorEvent {
                name,
                message: &message,
                raised,
            };
            recorder.builtin_error(&vm.explain_context(), &event);
        });
    }

    #[cold]
    #[inline(never)]
    pub(super) fn explain_comprehension(&mut self) {
        self.explain_deliver(|vm, recorder| {
            let event = NotCapturedEvent {
                construct: UncapturedConstruct::Comprehension,
            };
            recorder.not_captured(&vm.explain_context(), &event);
        });
    }
}

/// Describes an arithmetic error by its operands' types, as OPA does,
/// rather than by their values.
fn arithmetic_message(error: &VmError) -> String {
    let is_number = |value: &Value| matches!(*value, Value::Number(_));
    match *error {
        VmError::InvalidDivision {
            ref left,
            ref right,
            ..
        } if is_number(left.as_value()) && is_number(right.as_value()) => {
            Some("divide by zero".into())
        }
        VmError::InvalidModulo {
            ref left,
            ref right,
            ..
        } if is_number(left.as_value()) && is_number(right.as_value()) => {
            Some("modulo by zero".into())
        }
        VmError::InvalidAddition {
            ref left,
            ref right,
            ..
        }
        | VmError::InvalidMultiplication {
            ref left,
            ref right,
            ..
        }
        | VmError::InvalidDivision {
            ref left,
            ref right,
            ..
        }
        | VmError::InvalidModulo {
            ref left,
            ref right,
            ..
        } => operand_type_message([left.as_value(), right.as_value()], "number", is_number),
        VmError::InvalidSubtraction {
            ref left,
            ref right,
            ..
        } => match *left.as_value() {
            Value::Number(_) => {
                operand_type_message([left.as_value(), right.as_value()], "number", is_number)
            }
            Value::Set(_) => {
                operand_type_message([left.as_value(), right.as_value()], "set", |value| {
                    matches!(*value, Value::Set(_))
                })
            }
            _ => Some(alloc::format!(
                "operand 1 must be one of {{number, set}} but got {}",
                get_type(left.as_value())
            )),
        },
        VmError::ModuloOnFloat { .. } => Some("modulo on floating-point number".into()),
        VmError::ArithmeticError { ref message, .. } => Some(message.clone()),
        _ => None,
    }
    .unwrap_or_else(|| alloc::format!("{error}"))
}

/// Names the first operand that `accepts` rejects, numbered from 1.
fn operand_type_message<'a>(
    operands: impl IntoIterator<Item = &'a Value>,
    expected: &str,
    accepts: impl Fn(&Value) -> bool,
) -> Option<String> {
    operands
        .into_iter()
        .enumerate()
        .find(|&(_, operand)| !accepts(operand))
        .map(|(index, operand)| {
            alloc::format!(
                "operand {} must be {expected} but got {}",
                index.saturating_add(1),
                get_type(operand)
            )
        })
}

/// Removes the source frame that builtins put before their messages: they
/// report errors at a placeholder location with no source text.
fn without_source_frame(message: &str) -> &str {
    message
        .strip_prefix("\n--> <builtin>:")
        .and_then(|frame| frame.split_once("\nerror: "))
        .map_or(message, |(_, message)| message)
}

const fn passed_outcome(passed: bool) -> Outcome {
    if passed {
        Outcome::Success
    } else {
        Outcome::Failure
    }
}
