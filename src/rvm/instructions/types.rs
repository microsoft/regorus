// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use serde::{Deserialize, Serialize};

/// Represents either a literal index or a register number for path components
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LiteralOrRegister {
    /// Index into the program's literal table
    Literal(u16),
    /// Register number containing the value
    Register(u8),
}

/// Loop execution modes for different Rego iteration constructs
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LoopMode {
    /// Any quantification: some x in arr, x := arr[_], etc.
    /// Succeeds if ANY iteration succeeds, exits early on first success
    Any,

    /// Every quantification: every x in arr
    /// Succeeds only if ALL iterations succeed, exits early on first failure
    Every,

    /// ForEach processing: processes all elements without early exit
    /// Used for set membership rules (contains), object rules, and complete rules
    /// where all candidates must be evaluated. Determined by output constness.
    ForEach,
}

/// Comprehension execution modes for different comprehension types
#[repr(C)]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ComprehensionMode {
    /// Set comprehension: {expr | condition}
    /// Collects unique successful iterations into a set
    Set,
    /// Array comprehension: [expr | condition]
    /// Collects successful iterations into an array (preserves order)
    Array,
    /// Object comprehension: {key: value | condition}
    /// Collects successful key-value pairs into an object
    Object,
}

/// Azure Policy condition operator sub-opcodes.
///
/// Each variant maps to one of the ~21 Azure Policy condition operators.
/// Stored inside `Instruction::PolicyCondition` to collapse 21 enum variants
/// into a single instruction with a sub-op discriminant.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PolicyOp {
    Equals,
    NotEquals,
    Greater,
    GreaterOrEquals,
    Less,
    LessOrEquals,
    In,
    NotIn,
    Contains,
    NotContains,
    ContainsKey,
    NotContainsKey,
    Like,
    NotLike,
    Match,
    NotMatch,
    MatchInsensitively,
    NotMatchInsensitively,
    Exists,
    /// Guard for `value:` conditions — forces false when LHS is undefined.
    /// Uses `left` = value register, `right` = condition register.
    ValueConditionGuard,
    /// Logical negation: `!is_true(operand)`.  Uses `left` = operand, `right` is unused (0).
    Not,
}

impl PolicyOp {
    /// Display name used in assembly listings and Debug output.
    pub const fn display_name(self) -> &'static str {
        match self {
            Self::Equals => "POLICY_EQUALS",
            Self::NotEquals => "POLICY_NOT_EQUALS",
            Self::Greater => "POLICY_GREATER",
            Self::GreaterOrEquals => "POLICY_GREATER_OR_EQUALS",
            Self::Less => "POLICY_LESS",
            Self::LessOrEquals => "POLICY_LESS_OR_EQUALS",
            Self::In => "POLICY_IN",
            Self::NotIn => "POLICY_NOT_IN",
            Self::Contains => "POLICY_CONTAINS",
            Self::NotContains => "POLICY_NOT_CONTAINS",
            Self::ContainsKey => "POLICY_CONTAINS_KEY",
            Self::NotContainsKey => "POLICY_NOT_CONTAINS_KEY",
            Self::Like => "POLICY_LIKE",
            Self::NotLike => "POLICY_NOT_LIKE",
            Self::Match => "POLICY_MATCH",
            Self::NotMatch => "POLICY_NOT_MATCH",
            Self::MatchInsensitively => "POLICY_MATCH_INSENSITIVELY",
            Self::NotMatchInsensitively => "POLICY_NOT_MATCH_INSENSITIVELY",
            Self::Exists => "POLICY_EXISTS",
            Self::ValueConditionGuard => "VALUE_CONDITION_GUARD",
            Self::Not => "POLICY_NOT",
        }
    }

    /// Compact name for tabular assembly listings.
    pub const fn compact_name(self) -> &'static str {
        match self {
            Self::Equals => "POLICY_EQ",
            Self::NotEquals => "POLICY_NE",
            Self::Greater => "POLICY_GT",
            Self::GreaterOrEquals => "POLICY_GE",
            Self::Less => "POLICY_LT",
            Self::LessOrEquals => "POLICY_LE",
            Self::In => "POLICY_IN",
            Self::NotIn => "POLICY_NOT_IN",
            Self::Contains => "POLICY_CONTAINS",
            Self::NotContains => "POLICY_NOT_CONTAINS",
            Self::ContainsKey => "POLICY_CONTAINS_KEY",
            Self::NotContainsKey => "POLICY_NOT_CONTAINS_KEY",
            Self::Like => "POLICY_LIKE",
            Self::NotLike => "POLICY_NOT_LIKE",
            Self::Match => "POLICY_MATCH",
            Self::NotMatch => "POLICY_NOT_MATCH",
            Self::MatchInsensitively => "POLICY_MATCH_CI",
            Self::NotMatchInsensitively => "POLICY_NOT_MATCH_CI",
            Self::Exists => "POLICY_EXISTS",
            Self::ValueConditionGuard => "VAL_COND_GUARD",
            Self::Not => "POLICY_NOT",
        }
    }

    /// Returns `true` for negated condition operators (NotEquals, NotIn, etc.).
    pub const fn is_negated(self) -> bool {
        matches!(
            self,
            Self::NotEquals
                | Self::NotIn
                | Self::NotContains
                | Self::NotContainsKey
                | Self::NotLike
                | Self::NotMatch
                | Self::NotMatchInsensitively
        )
    }
}

/// Guard sub-modes for the consolidated `Guard` instruction.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum GuardMode {
    /// Assert negation — succeed if operand is false/undefined, fail if true.
    Not,
    /// Assert condition — fail (return undefined) if register is false/undefined.
    Condition,
    /// Assert not undefined — fail (return undefined) if register is undefined.
    NotUndefined,
}

/// Mode discriminant for merged AllOf/AnyOf Start and End instructions.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LogicalBlockMode {
    AllOf,
    AnyOf,
}
