// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod display;
mod params;
mod types;

pub use params::{
    ArrayCreateParams, BuiltinCallParams, ChainedIndexParams, ComprehensionBeginParams,
    FunctionCallParams, InstructionData, LoopStartParams, ObjectCreateParams, SetCreateParams,
    VirtualDataDocumentLookupParams,
};
pub use types::{
    ComprehensionMode, GuardMode, LiteralOrRegister, LogicalBlockMode, LoopMode, PolicyOp,
};

use serde::{Deserialize, Serialize};

/// RVM Instructions - simplified enum-based design
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum Instruction {
    /// Load literal value from literal table into register
    Load {
        dest: u8,
        literal_idx: u16,
    },

    /// Load true value into register
    LoadTrue {
        dest: u8,
    },

    /// Load false value into register
    LoadFalse {
        dest: u8,
    },

    /// Load null value into register
    LoadNull {
        dest: u8,
    },

    /// Load boolean value into register
    LoadBool {
        dest: u8,
        value: bool,
    },

    /// Load global data object into register
    LoadData {
        dest: u8,
    },

    /// Load global input object into register
    LoadInput {
        dest: u8,
    },

    /// Load host-supplied context value into register
    LoadContext {
        dest: u8,
    },

    /// Load program metadata value into register
    LoadMetadata {
        dest: u8,
    },

    /// Move value from one register to another
    Move {
        dest: u8,
        src: u8,
    },

    /// Arithmetic operations
    Add {
        dest: u8,
        left: u8,
        right: u8,
    },
    Sub {
        dest: u8,
        left: u8,
        right: u8,
    },
    Mul {
        dest: u8,
        left: u8,
        right: u8,
    },
    Div {
        dest: u8,
        left: u8,
        right: u8,
    },
    Mod {
        dest: u8,
        left: u8,
        right: u8,
    },

    /// Comparison operations
    Eq {
        dest: u8,
        left: u8,
        right: u8,
    },
    Ne {
        dest: u8,
        left: u8,
        right: u8,
    },
    Lt {
        dest: u8,
        left: u8,
        right: u8,
    },
    Le {
        dest: u8,
        left: u8,
        right: u8,
    },
    Gt {
        dest: u8,
        left: u8,
        right: u8,
    },
    Ge {
        dest: u8,
        left: u8,
        right: u8,
    },

    /// Logical operations
    And {
        dest: u8,
        left: u8,
        right: u8,
    },
    Or {
        dest: u8,
        left: u8,
        right: u8,
    },
    Not {
        dest: u8,
        operand: u8,
    },

    /// Builtin function calls - optimized for builtin functions
    BuiltinCall {
        /// Index into program's instruction_data.builtin_call_params table
        params_index: u16,
    },

    /// Suspend execution and yield control to the host
    HostAwait {
        /// Destination register to store the resume value
        dest: u8,
        /// Register containing the value to pass to the host
        arg: u8,
        /// Register containing a unique identifier for this await site
        id: u8,
    },

    /// Function rule calls - for user-defined function rules
    FunctionCall {
        /// Index into program's instruction_data.function_call_params table
        params_index: u16,
    },

    /// Return result
    Return {
        value: u8,
    },

    /// Set object field
    ObjectSet {
        obj: u8,
        key: u8,
        value: u8,
    },

    /// Create object with optimized field setting - uses parameter table
    ObjectCreate {
        /// Index into program's instruction_data.object_create_params table
        params_index: u16,
    },

    /// Index into container (object, array, set)
    Index {
        dest: u8,
        container: u8,
        key: u8,
    },

    /// Index into container using literal key (optimization for Load + Index)
    IndexLiteral {
        dest: u8,
        container: u8,
        literal_idx: u16,
    },

    /// Multi-level chained indexing (e.g., obj.field1[expr].field2)
    ChainedIndex {
        /// Index into program's instruction_data.chained_index_params table
        params_index: u16,
    },

    /// Create empty array
    ArrayNew {
        dest: u8,
    },

    /// Push element to array
    ArrayPush {
        arr: u8,
        value: u8,
    },

    /// Push element to array, but skip if the value is undefined.
    ///
    /// Used by Azure Policy's `field('alias[*].property')` wildcard collection
    /// so that absent nested properties are excluded from the collected array
    /// rather than producing undefined entries.
    ArrayPushDefined {
        arr: u8,
        value: u8,
    },

    /// Create array from registers - returns undefined if any element is undefined
    ArrayCreate {
        /// Index into program's instruction_data.array_create_params table
        params_index: u16,
    },

    /// Create empty set
    SetNew {
        dest: u8,
    },

    /// Add element to set
    SetAdd {
        set: u8,
        value: u8,
    },

    /// Create set from registers - returns undefined if any element is undefined
    SetCreate {
        /// Index into program's instruction_data.set_create_params table
        params_index: u16,
    },

    /// Check if collection contains value (for membership testing)
    Contains {
        dest: u8,
        collection: u8,
        value: u8,
    },

    /// Get count/length of collection (arrays, objects, sets) - returns undefined for non-collections
    Count {
        dest: u8,
        collection: u8,
    },

    /// Assert that two registers are equal - if either is undefined or they differ, fail the condition
    AssertEq {
        left: u8,
        right: u8,
    },

    /// Consolidated guard instruction — replaces AssertNot, AssertCondition, AssertNotUndefined.
    Guard {
        register: u8,
        mode: GuardMode,
    },

    /// Return undefined immediately when the condition register is not exactly
    /// `Bool(true)`.  Any other value — including `false`, `Undefined`, `Null`,
    /// numbers, strings, etc. — causes an immediate return of `Undefined`.
    ///
    /// This is used by Azure Policy compilation to model "condition does not match"
    /// without treating it as a VM assertion failure.
    ReturnUndefinedIfNotTrue {
        condition: u8,
    },

    /// Replace Undefined with Null in a register.
    ///
    /// Azure Policy treats missing fields as null rather than undefined.
    /// This instruction prevents the RVM's undefined-propagation from
    /// short-circuiting subsequent builtin calls.
    CoalesceUndefinedToNull {
        register: u8,
    },

    /// Start a loop over a collection with specified semantics - uses parameter table
    LoopStart {
        /// Index into program's instruction_data.loop_params table
        params_index: u16,
    },

    /// Continue to next iteration or exit loop
    LoopNext {
        /// Jump target back to loop body
        body_start: u16,
        /// Jump target for loop end
        loop_end: u16,
    },

    /// Call rule with caching - checks cache first, executes rule if needed, supports call stack
    CallRule {
        /// Destination register to store the result of the rule call
        dest: u8,
        /// Rule index to execute
        rule_index: u16,
    },

    /// Initialize a rule
    RuleInit {
        /// The register where rule's result is accumulated.
        result_reg: u8,

        /// The rule number of the rule
        rule_index: u16,
    },

    /// Lookup in data namespace virtual documents (rules + base data)
    VirtualDataDocumentLookup {
        /// Index into program's instruction_data.virtual_data_document_lookup_params table
        params_index: u16,
    },

    /// Mark successful completion of parameter destructuring validation
    DestructuringSuccess {},

    /// Return from rule execution
    RuleReturn {},

    /// Stop execution
    Halt {},

    /// Begin a comprehension with specified parameters
    ComprehensionBegin {
        /// Index into program's instruction_data.comprehension_begin_params table
        params_index: u16,
    },

    /// Yield a value to the current comprehension result
    ComprehensionYield {
        /// Register containing the value to yield to the comprehension
        value_reg: u8,
        /// Optional register containing the key for object comprehensions
        key_reg: Option<u8>,
    },

    /// End a comprehension block
    ComprehensionEnd {},

    // ── Azure Policy condition operators (consolidated) ────────────────
    /// Consolidated Azure Policy condition instruction.
    ///
    /// Replaces 21 separate Policy* variants.  The `op` discriminant selects
    /// the specific Azure Policy condition semantics.
    ///
    /// For most ops: `dest = op(left, right)`.
    /// For `PolicyOp::Not`: `dest = !is_true(left)`, `right` is unused (0).
    /// For `PolicyOp::ValueConditionGuard`: `left` = value register,
    ///   `right` = condition register.
    PolicyCondition {
        dest: u8,
        left: u8,
        right: u8,
        op: PolicyOp,
    },

    // ── AllOf / AnyOf structured short-circuit instructions ───────────
    /// Initialize allOf/anyOf: set result register to false.
    LogicalBlockStart {
        mode: LogicalBlockMode,
        /// Register that accumulates the result.
        result: u8,
        /// PC of the corresponding End instruction.
        end_pc: u16,
    },

    /// Check one allOf child: if not true, short-circuit (result stays false),
    /// jump to end_pc.
    AllOfNext {
        /// Register holding the child condition result.
        check: u8,
        /// Register that accumulates the allOf result.
        result: u8,
        /// PC of the AllOfEnd instruction (jump target on short-circuit).
        end_pc: u16,
    },

    /// Check one anyOf child: if true, short-circuit (set result to true),
    /// jump to end_pc.
    AnyOfNext {
        /// Register holding the child condition result.
        check: u8,
        /// Register that accumulates the anyOf result.
        result: u8,
        /// PC of the AnyOfEnd instruction.
        end_pc: u16,
    },

    /// Finalize allOf/anyOf block.
    ///
    /// For AllOf: all children passed → set result to true.
    /// For AnyOf: no child matched → result stays false (no-op).
    LogicalBlockEnd {
        mode: LogicalBlockMode,
        /// Register that accumulates the result.
        result: u8,
    },
}

impl Instruction {
    /// Create a new LoopStart instruction with parameter table index
    pub const fn loop_start(params_index: u16) -> Self {
        Self::LoopStart { params_index }
    }

    /// Create a new BuiltinCall instruction with parameter table index
    pub const fn builtin_call(params_index: u16) -> Self {
        Self::BuiltinCall { params_index }
    }

    /// Create a new HostAwait instruction
    pub const fn host_await(dest: u8, arg: u8, id: u8) -> Self {
        Self::HostAwait { dest, arg, id }
    }

    /// Create a new FunctionCall instruction with parameter table index
    pub const fn function_call(params_index: u16) -> Self {
        Self::FunctionCall { params_index }
    }

    /// Create a new ObjectCreate instruction with parameter table index
    pub const fn object_create(params_index: u16) -> Self {
        Self::ObjectCreate { params_index }
    }

    /// Create a new ArrayCreate instruction with parameter table index
    pub const fn array_create(params_index: u16) -> Self {
        Self::ArrayCreate { params_index }
    }

    /// Create a new SetCreate instruction with parameter table index
    pub const fn set_create(params_index: u16) -> Self {
        Self::SetCreate { params_index }
    }

    /// Create a new ComprehensionBegin instruction with parameter table index
    pub const fn comprehension_begin(params_index: u16) -> Self {
        Self::ComprehensionBegin { params_index }
    }

    /// Create a new ComprehensionYield instruction
    pub const fn comprehension_yield(value_reg: u8) -> Self {
        Self::ComprehensionYield {
            value_reg,
            key_reg: None,
        }
    }

    /// Create a new ComprehensionYield instruction for object comprehensions
    pub const fn comprehension_yield_object(key_reg: u8, value_reg: u8) -> Self {
        Self::ComprehensionYield {
            value_reg,
            key_reg: Some(key_reg),
        }
    }

    /// Create a new ComprehensionEnd instruction
    pub const fn comprehension_end() -> Self {
        Self::ComprehensionEnd {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::mem::size_of;

    #[test]
    fn instruction_size() {
        // Lock the instruction size to detect unintended growth.
        // Without repr(C), Rust picks a 1-byte discriminant (< 256 variants)
        // plus 4 bytes for the largest payload variant + 1 byte alignment
        // padding for u16 fields = 6 bytes total.
        //
        // TODO: Reduce to 4 bytes by making LoopNext zero-payload (both fields
        // are redundant with LoopStart params) and moving IndexLiteral to a
        // params table.
        let size = size_of::<Instruction>();
        assert_eq!(
            size, 6,
            "Instruction size changed from 6 to {size} — review new variants for bloat"
        );
    }
}
