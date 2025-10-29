// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Rule-centric result structures.

use alloc::collections::BTreeMap;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::type_analysis::model::{
    RuleAnalysis, RuleConstantState, RuleSpecializationSignature, SourceOrigin, TypeFact,
};
use crate::value::Value;

use super::deps::DependencyEdge;

/// Source location for a rule or definition
#[derive(Clone, Debug, Default)]
pub struct SourceSpan {
    pub file: String,
    pub line: u32,
    pub col: u32,
}

impl SourceSpan {
    pub fn format(&self) -> String {
        format!("{}:{}:{}", self.file, self.line, self.col)
    }
}

/// Top-level storage for all analysed rules.
#[derive(Clone, Debug, Default)]
pub struct RuleTable {
    pub by_path: BTreeMap<String, RuleSummary>,
    pub modules: Vec<ModuleSummary>,
}

/// Metadata about a source module.
#[derive(Clone, Debug, Default)]
pub struct ModuleSummary {
    pub module_idx: u32,
    pub package_path: String,
    pub source_name: String,
    pub rule_paths: Vec<String>,
    /// Full summaries for each rule in this module (aligned with rule_paths).
    pub rules: Vec<RuleSummary>,
}

/// Aggregated view of a logical rule head.
#[derive(Clone, Debug, Default)]
pub struct RuleSummary {
    pub id: String,
    pub module_idx: u32,
    pub head_span: Option<SourceSpan>,
    pub definitions: Vec<DefinitionSummary>,
    pub kind: RuleKind,
    pub arity: Option<usize>,
    pub head_expr: Option<u32>,
    pub constant_state: RuleConstantState,
    pub input_dependencies: Vec<SourceOrigin>,
    pub rule_dependencies: Vec<DependencyEdge>,
    pub aggregated_head_fact: Option<TypeFact>,
    pub aggregated_parameter_facts: Vec<Option<TypeFact>>,
    pub specializations: Vec<RuleSpecializationRecord>,
    pub trace: Option<RuleVerboseInfo>,
}

/// Data captured for a concrete rule definition (individual body).
#[derive(Clone, Debug, Default)]
pub struct DefinitionSummary {
    pub definition_idx: usize,
    pub module_idx: u32,
    pub span: Option<SourceSpan>,
    pub analysis: RuleAnalysis,
    pub head_fact: Option<TypeFact>,
    pub aggregated_head_fact: Option<TypeFact>,
    pub aggregated_parameter_facts: Vec<Option<TypeFact>>,
    pub bodies: Vec<RuleBodySummary>,
    pub constant_value: Option<Value>,
    pub specializations: Vec<RuleSpecializationRecord>,
    pub trace: Option<RuleVerboseInfo>,
}

/// Summary of a single rule body (primary or else clause).
#[derive(Clone, Debug, Default)]
pub struct RuleBodySummary {
    pub body_idx: usize,
    pub kind: RuleBodyKind,
    pub span: Option<SourceSpan>,
    pub value_expr_idx: Option<u32>,
    pub value_fact: Option<TypeFact>,
    pub is_constant: bool,
}

/// Distinguishes the main body from `else` bodies within a definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum RuleBodyKind {
    #[default]
    Primary,
    Else,
}

/// Classification for rule heads.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum RuleKind {
    #[default]
    Complete,
    PartialSet,
    PartialObject,
    Function,
}

/// Specialization record captured for function rules.
#[derive(Clone, Debug)]
pub struct RuleSpecializationRecord {
    pub signature: RuleSpecializationSignature,
    pub parameter_facts: Vec<TypeFact>,
    pub head_fact: Option<TypeFact>,
    pub constant_value: Option<Value>,
    pub expr_facts: BTreeMap<u32, BTreeMap<u32, TypeFact>>,
    pub trace: Option<RuleSpecializationTrace>,
}

/// Verbose trace for full rule or specialization evaluation.
#[derive(Clone, Debug, Default)]
pub struct RuleVerboseInfo {
    pub locals: Vec<TraceLocal>,
    pub statements: Vec<TraceStatement>,
}

/// Captured locals for verbose output.
#[derive(Clone, Debug, Default)]
pub struct TraceLocal {
    pub name: String,
    pub fact: Option<TypeFact>,
}

/// Statement summary with associated fact lines.
#[derive(Clone, Debug, Default)]
pub struct TraceStatement {
    pub summary: String,
    pub fact_lines: Vec<String>,
}

/// Trace captured for an individual specialization run.
#[derive(Clone, Debug, Default)]
pub struct RuleSpecializationTrace {
    pub locals: Vec<TraceLocal>,
    pub statements: Vec<TraceStatement>,
}
