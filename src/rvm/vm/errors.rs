// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::execution_model::SuspendReason;
use crate::value::Value;
use alloc::string::String;
use alloc::vec::Vec;
use core::time::Duration;
use thiserror::Error;

/// VM execution errors
#[derive(Error, Debug, Clone, PartialEq)]
pub enum VmError {
    #[error("Execution stopped: exceeded maximum instruction limit of {limit} after {executed} instructions (pc={pc})")]
    InstructionLimitExceeded {
        limit: usize,
        executed: usize,
        pc: usize,
    },

    #[error("Execution exceeded time limit (elapsed={elapsed:?}, limit={limit:?}, pc={pc})")]
    TimeLimitExceeded {
        elapsed: Duration,
        limit: Duration,
        pc: usize,
    },

    #[error("Execution exceeded memory limit (usage={usage} bytes, limit={limit} bytes, pc={pc})")]
    MemoryLimitExceeded { usage: u64, limit: u64, pc: usize },

    #[error("Literal index {index} out of bounds (pc={pc})")]
    LiteralIndexOutOfBounds { index: u16, pc: usize },

    #[error("Register {register} does not contain an object (value={value:?}, pc={pc})")]
    RegisterNotObject {
        register: u8,
        value: Value,
        pc: usize,
    },

    #[error("ObjectCreate: template is not an object (pc={pc}, template={template:?})")]
    ObjectCreateInvalidTemplate { template: Value, pc: usize },

    #[error("Register {register} does not contain an array (value={value:?}, pc={pc})")]
    RegisterNotArray {
        register: u8,
        value: Value,
        pc: usize,
    },

    #[error("Register {register} does not contain a set (value={value:?}, pc={pc})")]
    RegisterNotSet {
        register: u8,
        value: Value,
        pc: usize,
    },

    #[error("Register index {index} out of bounds (pc={pc}, register_count={register_count})")]
    RegisterIndexOutOfBounds {
        index: u8,
        pc: usize,
        register_count: usize,
    },

    #[error("Rule index {index} out of bounds (pc={pc}, available={available})")]
    RuleIndexOutOfBounds {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Rule index {index} has no info (pc={pc}, available={available})")]
    RuleInfoMissing {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid object create params index: {index} (pc={pc}, available={available})")]
    InvalidObjectCreateParams {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid template literal index: {index} (pc={pc}, available={available})")]
    InvalidTemplateLiteralIndex {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid chained index params index: {index} (pc={pc}, available={available})")]
    InvalidChainedIndexParams {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid array create params index: {index} (pc={pc}, available={available})")]
    InvalidArrayCreateParams {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid set create params index: {index} (pc={pc}, available={available})")]
    InvalidSetCreateParams {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid virtual data document lookup params index: {index} (pc={pc}, available={available})")]
    InvalidVirtualDataDocumentLookupParams {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid comprehension start params index: {index} (pc={pc}, available={available})")]
    InvalidComprehensionBeginParams {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid loop params index: {index} (pc={pc}, available={available})")]
    InvalidLoopParams {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid rule index: {rule_index:?} (pc={pc})")]
    InvalidRuleIndex { rule_index: Value, pc: usize },

    #[error("Invalid rule tree entry: {value:?} (pc={pc})")]
    InvalidRuleTreeEntry { value: Value, pc: usize },

    #[error("Builtin function expects exactly {expected} arguments, got {actual} (pc={pc})")]
    BuiltinArgumentMismatch {
        expected: u16,
        actual: usize,
        pc: usize,
    },

    #[error("Builtin function not resolved: {name} (pc={pc})")]
    BuiltinNotResolved { name: String, pc: usize },

    #[error("Cannot add {left:?} and {right:?} (pc={pc})")]
    InvalidAddition {
        left: Value,
        right: Value,
        pc: usize,
    },

    #[error("Cannot subtract {left:?} and {right:?} (pc={pc})")]
    InvalidSubtraction {
        left: Value,
        right: Value,
        pc: usize,
    },

    #[error("Cannot multiply {left:?} and {right:?} (pc={pc})")]
    InvalidMultiplication {
        left: Value,
        right: Value,
        pc: usize,
    },

    #[error("Cannot divide {left:?} and {right:?} (pc={pc})")]
    InvalidDivision {
        left: Value,
        right: Value,
        pc: usize,
    },

    #[error("modulo on floating-point number (left={left:?}, right={right:?}, pc={pc})")]
    ModuloOnFloat {
        left: Value,
        right: Value,
        pc: usize,
    },

    #[error("Cannot modulo {left:?} and {right:?} (pc={pc})")]
    InvalidModulo {
        left: Value,
        right: Value,
        pc: usize,
    },

    #[error("Cannot iterate over {value:?} (pc={pc})")]
    InvalidIteration { value: Value, pc: usize },

    #[error("HostAwait executed but no response provided for destination register {dest} (id: {identifier:?}, pc={pc})")]
    HostAwaitResponseMissing {
        dest: u8,
        identifier: Value,
        pc: usize,
    },

    #[error("Assertion failed (pc={pc})")]
    AssertionFailed { pc: usize },

    #[error("Rule-data conflict: {message} (pc={pc})")]
    RuleDataConflict { message: String, pc: usize },

    #[error("Arithmetic error: {message} (pc={pc})")]
    ArithmeticError { message: String, pc: usize },

    #[error("Entry point index {index} out of bounds (max: {max_index}, pc={pc})")]
    InvalidEntryPointIndex {
        index: usize,
        max_index: usize,
        pc: usize,
    },

    #[error("Entry point '{name}' not found (pc={pc}). Available entry points: {available:?}")]
    EntryPointNotFound {
        name: String,
        available: Vec<String>,
        pc: usize,
    },

    #[error("Entry point PC {pc} >= instruction count {instruction_count} for entry point '{entry_point}'")]
    EntryPointPcOutOfBounds {
        pc: usize,
        instruction_count: usize,
        entry_point: String,
    },

    #[error("Register count {register_count} below base count {base_count} (pc={pc})")]
    RegisterCountBelowBase {
        register_count: usize,
        base_count: usize,
        pc: usize,
    },

    #[error("Program counter {pc} out of bounds for instruction count {instruction_count}")]
    ProgramCounterOutOfBounds { pc: usize, instruction_count: usize },

    #[error("Rule cache size {cache_size} != rule info count {rule_info_count} (pc={pc})")]
    RuleCacheSizeMismatch {
        cache_size: usize,
        rule_info_count: usize,
        pc: usize,
    },

    #[error("Suspend reason {reason:?} is not supported in run-to-completion execution (pc={pc})")]
    UnsupportedSuspendInRunToCompletion { reason: SuspendReason, pc: usize },

    #[error("Cannot resume VM when execution state is {state} (pc={pc})")]
    InvalidResumeState { state: String, pc: usize },

    #[error("HostAwait suspension requires a resume value for reason {reason:?} (pc={pc})")]
    MissingResumeValue { reason: SuspendReason, pc: usize },

    #[error("Unexpected resume value supplied for reason {reason:?} (pc={pc})")]
    UnexpectedResumeValue { reason: SuspendReason, pc: usize },

    #[error("Missing execution frame: {context} (pc={pc})")]
    MissingExecutionFrame { context: &'static str, pc: usize },

    #[error("Unhandled instruction variant: {instruction} (pc={pc})")]
    UnhandledInstruction { instruction: String, pc: usize },

    #[error("Invalid function call params index: {index} (pc={pc}, available={available})")]
    InvalidFunctionCallParamsIndex {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid builtin call params index: {index} (pc={pc}, available={available})")]
    InvalidBuiltinCallParamsIndex {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Invalid builtin info index: {index} (pc={pc}, available={available})")]
    InvalidBuiltinInfoIndex {
        index: u16,
        pc: usize,
        available: usize,
    },

    #[error("Rule frame has no initial PC (pc={pc})")]
    RuleFrameMissingInitialPc { pc: usize },

    #[error("Call rule stack underflow during rule finalization (pc={pc})")]
    CallRuleStackUnderflow { pc: usize },

    #[error("Internal VM error: {message} (pc={pc})")]
    Internal { message: String, pc: usize },
}

impl From<anyhow::Error> for VmError {
    fn from(err: anyhow::Error) -> Self {
        VmError::ArithmeticError {
            message: alloc::format!("{}", err),
            pc: 0,
        }
    }
}

pub type Result<T> = core::result::Result<T, VmError>;
