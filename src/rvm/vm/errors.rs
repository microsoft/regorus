// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;
use alloc::string::String;
use alloc::vec::Vec;
use thiserror::Error;

/// VM execution errors
#[derive(Error, Debug, Clone, PartialEq)]
pub enum VmError {
    #[error("Execution stopped: exceeded maximum instruction limit of {limit}")]
    InstructionLimitExceeded { limit: usize },

    #[error("Literal index {index} out of bounds")]
    LiteralIndexOutOfBounds { index: usize },

    #[error("Register {register} does not contain an object")]
    RegisterNotObject { register: u8 },

    #[error("ObjectCreate: template is not an object")]
    ObjectCreateInvalidTemplate,

    #[error("Register {register} does not contain an array")]
    RegisterNotArray { register: u8 },

    #[error("Register {register} does not contain a set")]
    RegisterNotSet { register: u8 },

    #[error("Rule index {index} out of bounds")]
    RuleIndexOutOfBounds { index: u16 },

    #[error("Rule index {index} has no info")]
    RuleInfoMissing { index: u16 },

    #[error("Invalid object create params index: {index}")]
    InvalidObjectCreateParams { index: u16 },

    #[error("Invalid template literal index: {index}")]
    InvalidTemplateLiteralIndex { index: u16 },

    #[error("Invalid chained index params index: {index}")]
    InvalidChainedIndexParams { index: u16 },

    #[error("Invalid array create params index: {index}")]
    InvalidArrayCreateParams { index: u16 },

    #[error("Invalid set create params index: {index}")]
    InvalidSetCreateParams { index: u16 },

    #[error("Invalid virtual data document lookup params index: {index}")]
    InvalidVirtualDataDocumentLookupParams { index: u16 },

    #[error("Invalid comprehension start params index: {index}")]
    InvalidComprehensionBeginParams { index: u16 },

    #[error("Invalid rule index: {rule_index:?}")]
    InvalidRuleIndex { rule_index: Value },

    #[error("Invalid rule tree entry: {value:?}")]
    InvalidRuleTreeEntry { value: Value },

    #[error("Builtin function expects exactly {expected} arguments, got {actual}")]
    BuiltinArgumentMismatch { expected: u16, actual: usize },

    #[error("Builtin function not resolved: {name}")]
    BuiltinNotResolved { name: String },

    #[error("Cannot add {left:?} and {right:?}")]
    InvalidAddition { left: Value, right: Value },

    #[error("Cannot subtract {left:?} and {right:?}")]
    InvalidSubtraction { left: Value, right: Value },

    #[error("Cannot multiply {left:?} and {right:?}")]
    InvalidMultiplication { left: Value, right: Value },

    #[error("Cannot divide {left:?} and {right:?}")]
    InvalidDivision { left: Value, right: Value },

    #[error("modulo on floating-point number")]
    ModuloOnFloat,

    #[error("Cannot modulo {left:?} and {right:?}")]
    InvalidModulo { left: Value, right: Value },

    #[error("Cannot iterate over {value:?}")]
    InvalidIteration { value: Value },

    #[error("HostAwait executed but no response provided for destination register {dest} (id: {identifier:?})")]
    HostAwaitResponseMissing { dest: u8, identifier: Value },

    #[error("Assertion failed")]
    AssertionFailed,

    #[error("Rule-data conflict: {0}")]
    RuleDataConflict(String),

    #[error("Arithmetic error: {0}")]
    ArithmeticError(String),

    #[error("Entry point index {index} out of bounds (max: {max_index})")]
    InvalidEntryPointIndex { index: usize, max_index: usize },

    #[error("Entry point '{name}' not found. Available entry points: {available:?}")]
    EntryPointNotFound {
        name: String,
        available: Vec<String>,
    },

    #[error("Internal VM error: {0}")]
    Internal(String),
}

impl From<anyhow::Error> for VmError {
    fn from(err: anyhow::Error) -> Self {
        VmError::ArithmeticError(alloc::format!("{}", err))
    }
}

pub type Result<T> = core::result::Result<T, VmError>;
