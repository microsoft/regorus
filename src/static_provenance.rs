// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

//! Static provenance analysis for RVM programs.
//!
//! This module computes, at compile time, the data-path origin (provenance) for
//! every register in every rule definition.  The analysis is a single forward
//! pass over each definition's instruction range and produces:
//!
//! 1. **Register provenances** – the `input.*` / `data.*` path that flows into
//!    each register, when statically determinable.
//! 2. **Condition infos** – structured metadata for each `Guard` /
//!    `AssertEq` instruction: which registers are checked, what their
//!    provenances are, operator kind, source text, etc.
//!
//! All results are stored inside `Program` and are available for:
//! - Explanation/causality reports (replacing the runtime `ProvenanceTracker`)
//! - Unknown/assumption handling (detecting input-rooted undefineds)

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use crate::Rc;

// ---------------------------------------------------------------------------
// Provenance types
// ---------------------------------------------------------------------------

/// The root origin of a data path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceRoot {
    /// Comes from <code>input</code>.
    Input,
    /// Comes from <code>data</code> (base documents).
    Data,
    /// Result of evaluating another rule.
    RuleResult { rule_index: u16 },
    /// Virtual data document lookup.
    VirtualDocument,
}

/// A single segment in a provenance path.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Segment {
    /// Static field access, e.g. `.role`.
    Field(Rc<str>),
    /// Dynamic key lookup whose value comes from a register.
    DynamicKey { register: u8 },
    /// Wildcard iteration value, e.g. `[_]`.
    Wildcard,
    /// Wildcard iteration key.
    WildcardKey,
}

/// A fully-resolved provenance path for a register value.
///
/// Example: `input.containers[_].securityContext.privileged` is represented as:
/// ```text
/// Provenance {
///     root: Input,
///     segments: [Field("containers"), Wildcard, Field("securityContext"), Field("privileged")]
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Provenance {
    pub root: ProvenanceRoot,
    pub segments: Vec<Segment>,
}

impl Provenance {
    pub const fn input() -> Self {
        Self {
            root: ProvenanceRoot::Input,
            segments: Vec::new(),
        }
    }

    pub const fn data() -> Self {
        Self {
            root: ProvenanceRoot::Data,
            segments: Vec::new(),
        }
    }

    pub const fn rule_result(rule_index: u16) -> Self {
        Self {
            root: ProvenanceRoot::RuleResult { rule_index },
            segments: Vec::new(),
        }
    }

    pub const fn virtual_document() -> Self {
        Self {
            root: ProvenanceRoot::VirtualDocument,
            segments: Vec::new(),
        }
    }

    pub fn is_input_rooted(&self) -> bool {
        self.root == ProvenanceRoot::Input
    }

    pub fn is_data_rooted(&self) -> bool {
        self.root == ProvenanceRoot::Data
    }

    /// Create a new provenance by appending a static field access.
    pub fn with_field(&self, name: &str) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::Field(Rc::from(name)));
        Self {
            root: self.root.clone(),
            segments,
        }
    }

    /// Create a new provenance by appending a dynamic key lookup.
    pub fn with_dynamic_key(&self, register: u8) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::DynamicKey { register });
        Self {
            root: self.root.clone(),
            segments,
        }
    }

    /// Create a new provenance by appending a wildcard iteration (value).
    pub fn with_wildcard(&self) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::Wildcard);
        Self {
            root: self.root.clone(),
            segments,
        }
    }

    /// Create a new provenance by appending a wildcard key.
    pub fn with_wildcard_key(&self) -> Self {
        let mut segments = self.segments.clone();
        segments.push(Segment::WildcardKey);
        Self {
            root: self.root.clone(),
            segments,
        }
    }
}

impl fmt::Display for Provenance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.root {
            ProvenanceRoot::Input => write!(f, "input")?,
            ProvenanceRoot::Data => write!(f, "data")?,
            ProvenanceRoot::RuleResult { rule_index } => write!(f, "rule[{rule_index}]")?,
            ProvenanceRoot::VirtualDocument => write!(f, "virtual")?,
        }
        for seg in &self.segments {
            match *seg {
                Segment::Field(ref name) => write!(f, ".{name}")?,
                Segment::DynamicKey { register } => write!(f, "[r{register}]")?,
                Segment::Wildcard => write!(f, "[_]")?,
                Segment::WildcardKey => write!(f, "[_key]")?,
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Condition info types
// ---------------------------------------------------------------------------

/// The kind of condition being asserted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConditionKind {
    /// A comparison operator (==, !=, <, <=, >, >=).
    Comparison,
    /// A membership test (`x in coll`).
    Membership,
    /// A truthiness/boolean check.
    Truthiness,
    /// An existence check (not-undefined).
    Existence,
    /// An equality assertion (`AssertEq`).
    EqualityAssertion,
    /// A negation guard (`not expr`).
    Negation,
    /// A variable binding (`:=` assignment).
    Binding,
}

/// Comparison/logical operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operator {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Contains,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Eq => write!(f, "=="),
            Self::Ne => write!(f, "!="),
            Self::Lt => write!(f, "<"),
            Self::Le => write!(f, "<="),
            Self::Gt => write!(f, ">"),
            Self::Ge => write!(f, ">="),
            Self::Contains => write!(f, "in"),
        }
    }
}

/// Operand information for a binary condition.
#[derive(Debug, Clone)]
pub struct ConditionOperands {
    pub left_reg: u8,
    pub right_reg: u8,
    pub left_provenance: Option<Provenance>,
    pub right_provenance: Option<Provenance>,
}

/// Static metadata for a single assertion instruction.
///
/// Stored in `Program::condition_infos` parallel to the instruction vector.
#[derive(Debug, Clone)]
pub struct StaticConditionInfo {
    /// The register being checked/asserted.
    pub checked_register: u8,
    /// Provenance of the checked register (if statically known).
    pub checked_provenance: Option<Provenance>,
    /// For binary conditions: operand details.
    pub operands: Option<ConditionOperands>,
    /// Source text of the condition expression.
    pub text: String,
    /// What kind of condition this is.
    pub kind: ConditionKind,
    /// The comparison operator (for Comparison kind).
    pub operator: Option<Operator>,
    /// Whether any operand has input-rooted provenance.
    pub has_input_operand: bool,
    /// For binding conditions: the variable name being bound (e.g. `"container"`).
    pub binding_name: Option<String>,
}

impl StaticConditionInfo {
    /// Returns true if this condition involves an input-rooted value.
    pub fn involves_input(&self) -> bool {
        self.has_input_operand
            || self
                .checked_provenance
                .as_ref()
                .is_some_and(Provenance::is_input_rooted)
    }
}

// ---------------------------------------------------------------------------
// Static analysis pass
// ---------------------------------------------------------------------------

use crate::rvm::instructions::{GuardMode, Instruction, LiteralOrRegister};
use crate::rvm::program::Program;

/// Run the static provenance analysis on a compiled program.
///
/// This populates `program.condition_infos` and `program.register_provenances`.
#[cfg(feature = "explanations")]
pub fn analyze(program: &mut Program) {
    let num_instructions = program.instructions.len();
    let mut condition_infos: Vec<Option<StaticConditionInfo>> = Vec::new();
    condition_infos.resize_with(num_instructions, || None);

    let mut all_register_provenances: Vec<Vec<Option<Provenance>>> = Vec::new();

    // Analyze each rule definition.
    for rule_info in &program.rule_infos {
        for def_body_pcs in rule_info.definitions.iter() {
            if def_body_pcs.is_empty() {
                continue;
            }

            let num_regs = usize::from(rule_info.num_registers);
            let mut reg_provenance: Vec<Option<Provenance>> = Vec::new();
            reg_provenance.resize_with(num_regs, || None);

            // Determine instruction range for this definition body.
            // The body PCs are the starting PCs of each body block within the definition.
            // Walk from the first body PC until we hit a RuleReturn.
            let first_pc = def_body_pcs.first().copied().unwrap_or(0);
            let first_pc_usize: usize = first_pc.try_into().unwrap_or(0);

            // Walk instructions from first_pc to RuleReturn.
            let mut pc = first_pc_usize;
            while pc < num_instructions {
                let instruction = program.instructions.get(pc).copied();
                let Some(instr) = instruction else {
                    break;
                };

                analyze_instruction(
                    &instr,
                    pc,
                    &mut reg_provenance,
                    &mut condition_infos,
                    program,
                );

                if matches!(instr, Instruction::RuleReturn {}) {
                    break;
                }
                pc = pc.saturating_add(1);
            }

            all_register_provenances.push(reg_provenance);
        }
    }

    program.condition_infos = condition_infos;
    program.register_provenances = all_register_provenances;
}

/// Analyze a single instruction's effect on register provenances and extract
/// condition info for assertion instructions.
fn analyze_instruction(
    instr: &Instruction,
    pc: usize,
    reg_prov: &mut [Option<Provenance>],
    condition_infos: &mut [Option<StaticConditionInfo>],
    program: &Program,
) {
    use Instruction::*;

    match *instr {
        // -- Roots --
        LoadInput { dest } => {
            set_provenance(reg_prov, dest, Some(Provenance::input()));
        }
        LoadData { dest } => {
            set_provenance(reg_prov, dest, Some(Provenance::data()));
        }

        // -- Field access --
        IndexLiteral {
            dest,
            container,
            literal_idx,
        } => {
            let field_name: Option<&str> = program
                .literals
                .get(usize::from(literal_idx))
                .and_then(|v| v.as_string().ok())
                .map(|s| s.as_ref());
            let prov = get_provenance(reg_prov, container)
                .and_then(|base| field_name.map(|name| base.with_field(name)));
            set_provenance(reg_prov, dest, prov);
        }

        // -- Dynamic index --
        Index {
            dest,
            container,
            key,
        } => {
            let prov = get_provenance(reg_prov, container).map(|base| base.with_dynamic_key(key));
            set_provenance(reg_prov, dest, prov);
        }

        // -- Chained index --
        ChainedIndex { params_index } => {
            if let Some(params) = program
                .instruction_data
                .chained_index_params
                .get(usize::from(params_index))
            {
                let prov = build_chained_provenance(
                    get_provenance(reg_prov, params.root),
                    &params.path_components,
                    &program.literals,
                );
                set_provenance(reg_prov, params.dest, prov);
            }
        }

        // -- Move / copy --
        Move { dest, src } => {
            let prov = get_provenance(reg_prov, src).cloned();
            set_provenance(reg_prov, dest, prov);

            // If this Move is a binding (`:=`), create a condition info entry.
            if let Some(binding_name) = program.binding_infos.get(pc).and_then(|b| b.clone()) {
                let checked_provenance = get_provenance(reg_prov, dest).cloned();
                let has_input = checked_provenance
                    .as_ref()
                    .is_some_and(Provenance::is_input_rooted);
                let text = get_condition_text(pc, program);
                if let Some(slot) = condition_infos.get_mut(pc) {
                    *slot = Some(StaticConditionInfo {
                        checked_register: dest,
                        checked_provenance,
                        operands: None,
                        text,
                        kind: ConditionKind::Binding,
                        operator: None,
                        has_input_operand: has_input,
                        binding_name: Some(binding_name),
                    });
                }
            }
        }

        // -- Loops --
        LoopStart { params_index } => {
            if let Some(params) = program
                .instruction_data
                .loop_params
                .get(usize::from(params_index))
            {
                let base = get_provenance(reg_prov, params.collection);
                let val_prov = base.map(|b| b.with_wildcard());
                let key_prov = base.map(|b| b.with_wildcard_key());
                set_provenance(reg_prov, params.value_reg, val_prov);
                set_provenance(reg_prov, params.key_reg, key_prov);
                // result_reg is not given provenance here — it accumulates results
                clear_provenance(reg_prov, params.result_reg);
            }
        }

        // -- Comprehensions --
        ComprehensionBegin { params_index } => {
            if let Some(params) = program
                .instruction_data
                .comprehension_begin_params
                .get(usize::from(params_index))
            {
                let base = get_provenance(reg_prov, params.collection_reg);
                let val_prov = base.map(|b| b.with_wildcard());
                let key_prov = base.map(|b| b.with_wildcard_key());
                set_provenance(reg_prov, params.value_reg, val_prov);
                set_provenance(reg_prov, params.key_reg, key_prov);
                clear_provenance(reg_prov, params.result_reg);
            }
        }

        // -- Rule calls --
        CallRule { dest, rule_index } => {
            set_provenance(reg_prov, dest, Some(Provenance::rule_result(rule_index)));
        }

        // -- Virtual data document --
        VirtualDataDocumentLookup { params_index } => {
            if let Some(params) = program
                .instruction_data
                .virtual_data_document_lookup_params
                .get(usize::from(params_index))
            {
                set_provenance(reg_prov, params.dest, Some(Provenance::virtual_document()));
            }
        }

        // -- Assertions --
        Guard { register, mode } => {
            let info = build_guard_condition_info(register, mode, pc, reg_prov, program);
            if let Some(ci) = condition_infos.get_mut(pc) {
                *ci = Some(info);
            }
        }

        AssertEq { left, right } => {
            let info = build_assert_eq_condition_info(left, right, pc, reg_prov, program);
            if let Some(ci) = condition_infos.get_mut(pc) {
                *ci = Some(info);
            }
        }

        // -- Everything else: clear provenance on dest register --
        RuleInit { result_reg, .. } => {
            clear_provenance(reg_prov, result_reg);
        }
        Load { dest, .. }
        | LoadTrue { dest }
        | LoadFalse { dest }
        | LoadNull { dest }
        | LoadBool { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        Add { dest, .. }
        | Sub { dest, .. }
        | Mul { dest, .. }
        | Div { dest, .. }
        | Mod { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        Eq { dest, .. }
        | Ne { dest, .. }
        | Lt { dest, .. }
        | Le { dest, .. }
        | Gt { dest, .. }
        | Ge { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        And { dest, .. } | Or { dest, .. } | Not { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        Contains { dest, .. } | Count { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        ArrayNew { dest } | SetNew { dest } => {
            clear_provenance(reg_prov, dest);
        }
        HostAwait { dest, .. } => {
            clear_provenance(reg_prov, dest);
        }
        Return { .. } => {}
        BuiltinCall { params_index } => {
            if let Some(params) = program
                .instruction_data
                .builtin_call_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        FunctionCall { params_index } => {
            if let Some(params) = program
                .instruction_data
                .function_call_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        ObjectCreate { params_index } => {
            if let Some(params) = program
                .instruction_data
                .object_create_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        ArrayCreate { params_index } => {
            if let Some(params) = program
                .instruction_data
                .array_create_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }
        SetCreate { params_index } => {
            if let Some(params) = program
                .instruction_data
                .set_create_params
                .get(usize::from(params_index))
            {
                clear_provenance(reg_prov, params.dest);
            }
        }

        // Mutation / control-flow — no dest register to clear.
        ObjectSet { .. }
        | ObjectDeepSet { .. }
        | ArrayPush { .. }
        | SetAdd { .. }
        | LoopNext { .. }
        | RuleReturn {}
        | Halt {}
        | DestructuringSuccess {}
        | ComprehensionYield { .. }
        | ComprehensionEnd {} => {}
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn set_provenance(reg_prov: &mut [Option<Provenance>], reg: u8, prov: Option<Provenance>) {
    if let Some(slot) = reg_prov.get_mut(usize::from(reg)) {
        *slot = prov;
    }
}

fn clear_provenance(reg_prov: &mut [Option<Provenance>], reg: u8) {
    set_provenance(reg_prov, reg, None);
}

fn get_provenance(reg_prov: &[Option<Provenance>], reg: u8) -> Option<&Provenance> {
    reg_prov.get(usize::from(reg)).and_then(Option::as_ref)
}

/// Build provenance for a chained index operation by walking each path component.
fn build_chained_provenance(
    base: Option<&Provenance>,
    components: &[LiteralOrRegister],
    literals: &[crate::value::Value],
) -> Option<Provenance> {
    let mut current = base?.clone();
    for component in components {
        current = match *component {
            LiteralOrRegister::Literal(idx) => {
                let field_name: Option<&str> = literals
                    .get(usize::from(idx))
                    .and_then(|v| v.as_string().ok())
                    .map(|s| s.as_ref());
                match field_name {
                    Some(name) => current.with_field(name),
                    None => return None,
                }
            }
            LiteralOrRegister::Register(reg) => current.with_dynamic_key(reg),
        };
    }
    Some(current)
}

/// Extract source text for the condition at `pc` from span info.
fn get_condition_text(pc: usize, program: &Program) -> String {
    let span_info = match program.instruction_spans.get(pc) {
        Some(Some(info)) => info,
        _ => return String::new(),
    };

    let source = match program.sources.get(span_info.source_index) {
        Some(s) => &s.content,
        None => return String::new(),
    };

    source
        .lines()
        .nth(span_info.line.saturating_sub(1))
        .map(str::trim)
        .map(String::from)
        .unwrap_or_default()
}

/// Peek at the instruction before `pc` to identify comparison operands.
fn peek_preceding_comparison(
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> Option<(Operator, ConditionOperands)> {
    if pc == 0 {
        return None;
    }
    let prev_pc = pc.saturating_sub(1);
    let prev = program.instructions.get(prev_pc)?;
    match *prev {
        Instruction::Eq { dest, left, right } | Instruction::Ge { dest, left, right }
            if dest == get_guard_register_at(pc, program)? =>
        {
            // Re-match to get exact operator
            let op = match *prev {
                Instruction::Eq { .. } => Operator::Eq,
                _ => Operator::Ge,
            };
            Some((
                op,
                ConditionOperands {
                    left_reg: left,
                    right_reg: right,
                    left_provenance: get_provenance(reg_prov, left).cloned(),
                    right_provenance: get_provenance(reg_prov, right).cloned(),
                },
            ))
        }
        _ => {
            // Try to match all comparison variants.
            match *prev {
                Instruction::Eq { dest, left, right }
                | Instruction::Ne { dest, left, right }
                | Instruction::Lt { dest, left, right }
                | Instruction::Le { dest, left, right }
                | Instruction::Gt { dest, left, right }
                | Instruction::Ge { dest, left, right }
                    if Some(dest) == get_guard_register_at(pc, program) =>
                {
                    let op = match *prev {
                        Instruction::Eq { .. } => Operator::Eq,
                        Instruction::Ne { .. } => Operator::Ne,
                        Instruction::Lt { .. } => Operator::Lt,
                        Instruction::Le { .. } => Operator::Le,
                        Instruction::Gt { .. } => Operator::Gt,
                        Instruction::Ge { .. } => Operator::Ge,
                        _ => return None,
                    };
                    Some((
                        op,
                        ConditionOperands {
                            left_reg: left,
                            right_reg: right,
                            left_provenance: get_provenance(reg_prov, left).cloned(),
                            right_provenance: get_provenance(reg_prov, right).cloned(),
                        },
                    ))
                }
                Instruction::Contains {
                    dest,
                    collection,
                    value,
                } if Some(dest) == get_guard_register_at(pc, program) => Some((
                    Operator::Contains,
                    ConditionOperands {
                        left_reg: value,
                        right_reg: collection,
                        left_provenance: get_provenance(reg_prov, value).cloned(),
                        right_provenance: get_provenance(reg_prov, collection).cloned(),
                    },
                )),
                _ => None,
            }
        }
    }
}

/// Get the register being checked by the Guard instruction at `pc`.
fn get_guard_register_at(pc: usize, program: &Program) -> Option<u8> {
    let instr = program.instructions.get(pc).copied()?;
    match instr {
        Instruction::Guard { register, .. } => Some(register),
        _ => None,
    }
}

fn build_guard_condition_info(
    register: u8,
    mode: GuardMode,
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> StaticConditionInfo {
    let checked_provenance = get_provenance(reg_prov, register).cloned();
    let text = get_condition_text(pc, program);

    match mode {
        GuardMode::Condition => {
            // Try to find the comparison that produced this boolean.
            if let Some((op, operands)) = peek_preceding_comparison(pc, reg_prov, program) {
                let has_input = operands
                    .left_provenance
                    .as_ref()
                    .is_some_and(Provenance::is_input_rooted)
                    || operands
                        .right_provenance
                        .as_ref()
                        .is_some_and(Provenance::is_input_rooted);
                // Use the input-rooted operand's provenance as checked_provenance
                // (the guard register itself holds a boolean, not the input path).
                let effective_provenance = if has_input {
                    operands
                        .left_provenance
                        .as_ref()
                        .filter(|p| p.is_input_rooted())
                        .or(operands
                            .right_provenance
                            .as_ref()
                            .filter(|p| p.is_input_rooted()))
                        .cloned()
                } else {
                    checked_provenance
                };
                StaticConditionInfo {
                    checked_register: register,
                    checked_provenance: effective_provenance,
                    operands: Some(operands),
                    text,
                    kind: ConditionKind::Comparison,
                    operator: Some(op),
                    has_input_operand: has_input,
                    binding_name: None,
                }
            } else {
                // Generic truthiness guard.
                let has_input = checked_provenance
                    .as_ref()
                    .is_some_and(Provenance::is_input_rooted);
                StaticConditionInfo {
                    checked_register: register,
                    checked_provenance,
                    operands: None,
                    text,
                    kind: ConditionKind::Truthiness,
                    operator: None,
                    has_input_operand: has_input,
                    binding_name: None,
                }
            }
        }
        GuardMode::NotUndefined => {
            let has_input = checked_provenance
                .as_ref()
                .is_some_and(Provenance::is_input_rooted);
            StaticConditionInfo {
                checked_register: register,
                checked_provenance,
                operands: None,
                text,
                kind: ConditionKind::Existence,
                operator: None,
                has_input_operand: has_input,
                binding_name: None,
            }
        }
        GuardMode::Not => {
            let has_input = checked_provenance
                .as_ref()
                .is_some_and(Provenance::is_input_rooted);
            StaticConditionInfo {
                checked_register: register,
                checked_provenance,
                operands: None,
                text,
                kind: ConditionKind::Negation,
                operator: None,
                has_input_operand: has_input,
                binding_name: None,
            }
        }
    }
}

fn build_assert_eq_condition_info(
    left: u8,
    right: u8,
    pc: usize,
    reg_prov: &[Option<Provenance>],
    program: &Program,
) -> StaticConditionInfo {
    let left_prov = get_provenance(reg_prov, left).cloned();
    let right_prov = get_provenance(reg_prov, right).cloned();
    let text = get_condition_text(pc, program);
    let has_input = left_prov.as_ref().is_some_and(Provenance::is_input_rooted)
        || right_prov.as_ref().is_some_and(Provenance::is_input_rooted);
    StaticConditionInfo {
        checked_register: left, // Convention: left is the "checked" side
        checked_provenance: left_prov.clone(),
        operands: Some(ConditionOperands {
            left_reg: left,
            right_reg: right,
            left_provenance: left_prov,
            right_provenance: right_prov,
        }),
        text,
        kind: ConditionKind::EqualityAssertion,
        operator: Some(Operator::Eq),
        has_input_operand: has_input,
        binding_name: None,
    }
}

#[cfg(test)]
mod tests {
    use super::get_condition_text;
    use crate::rvm::program::{Program, SourceFile, SpanInfo};

    #[test]
    fn get_condition_text_returns_full_trimmed_line() {
        let mut program = Program::new();
        program.sources.push(SourceFile::new(
            "test.rego".into(),
            "package test\n        some link in input.links\n".into(),
        ));
        program
            .instruction_spans
            .push(Some(SpanInfo::new(0, 2, 23, 4)));

        let text = get_condition_text(0, &program);

        assert_eq!(text, "some link in input.links");
    }
}
