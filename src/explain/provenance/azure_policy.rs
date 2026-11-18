// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::{
    writes, AzurePolicySite, CheckSite, ConditionKind, Instruction, Program, Provenance, RuleKind,
    RuleOwner, SiteId, SiteOwner, SourceIndex, SourceLocation, SpanInfo,
};
use crate::rvm::instructions::{LiteralOrRegister, PolicyOp};
use crate::Value;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

pub(super) fn decode(program: &Program) -> Provenance {
    let sources: Vec<_> = program
        .sources
        .iter()
        .map(|s| JsonSource::new(&s.name, &s.content))
        .collect();
    let mut paths = alloc::vec![None; 256];
    let mut literals = alloc::vec![None; 256];
    let mut sites = Vec::new();
    for (pc, instruction) in program.instructions.iter().enumerate() {
        let shape = match *instruction {
            Instruction::PolicyCondition {
                op: PolicyOp::ValueConditionGuard,
                ..
            } => None,
            Instruction::PolicyCondition {
                left, right, op, ..
            } => {
                let kind = match op {
                    PolicyOp::Not => ConditionKind::Negation,
                    PolicyOp::Exists => ConditionKind::Existence,
                    PolicyOp::In | PolicyOp::NotIn => ConditionKind::Membership,
                    _ => ConditionKind::Comparison,
                };
                Some((kind, Some(op), left, (op != PolicyOp::Not).then_some(right)))
            }
            Instruction::LoopStart { params_index } => program
                .instruction_data
                .get_loop_params(params_index)
                .map(|p| (ConditionKind::Iteration, None, p.collection, None)),
            Instruction::Count { collection, .. } => {
                Some((ConditionKind::Iteration, None, collection, None))
            }
            _ => None,
        };
        if let Some((kind, operator, left, right)) = shape {
            let source = program
                .instruction_spans
                .get(pc)
                .and_then(Option::as_ref)
                .and_then(|span| sources.get(span.source_index)?.condition(span));
            let (text, location, field, source_operator) = source.unwrap_or_default();
            sites.push(CheckSite {
                id: SiteId(u32::try_from(sites.len()).unwrap_or(u32::MAX)),
                pc,
                owner: SiteOwner {
                    rule: 0,
                    definition: 0,
                    body: Some(0),
                },
                ordinal: sites.len(),
                kind,
                operator: None,
                text,
                location,
                left_path: paths.get(usize::from(left)).cloned().flatten(),
                right_path: right.and_then(|r| paths.get(usize::from(r)).cloned().flatten()),
                azure_policy: Some(AzurePolicySite {
                    operator,
                    source_operator,
                    field,
                }),
            });
        }
        track(program, instruction, &mut paths, &mut literals);
    }
    Provenance {
        rules: alloc::vec![RuleOwner {
            name: "main".into(),
            kind: RuleKind::Complete
        }],
        sites,
    }
}

fn component(program: &Program, index: u16) -> Option<String> {
    match *program.literals.get(usize::from(index))? {
        Value::String(ref key) => serde_json::to_string(key.as_ref()).ok(),
        Value::Number(ref number) => number.as_u64().map(|n| n.to_string()),
        _ => None,
    }
}

fn track(
    program: &Program,
    instruction: &Instruction,
    paths: &mut [Option<String>],
    literals: &mut [Option<u16>],
) {
    let path = |reg: u8| paths.get(usize::from(reg)).cloned().flatten();
    let literal = |reg: u8| literals.get(usize::from(reg)).copied().flatten();
    let value = match *instruction {
        Instruction::LoadInput { .. } => Some("input".into()),
        Instruction::LoadContext { .. } => Some("context".into()),
        Instruction::Move { src, .. } => path(src),
        Instruction::CoalesceUndefinedToNull { register } => path(register),
        Instruction::IndexLiteral {
            container,
            literal_idx,
            ..
        } => path(container)
            .zip(component(program, literal_idx))
            .map(|(root, key)| alloc::format!("{root}[{key}]")),
        Instruction::Index { container, key, .. } => path(container)
            .zip(literal(key).and_then(|i| component(program, i)))
            .map(|(root, key)| alloc::format!("{root}[{key}]")),
        Instruction::ChainedIndex { params_index } => (|| {
            let params = program
                .instruction_data
                .get_chained_index_params(params_index)?;
            let mut value = path(params.root)?;
            for key in &params.path_components {
                let index = match *key {
                    LiteralOrRegister::Literal(i) => i,
                    LiteralOrRegister::Register(r) => literal(r)?,
                };
                value.push_str(&alloc::format!("[{}]", component(program, index)?));
            }
            Some(value)
        })(),
        _ => None,
    };
    let key = match *instruction {
        Instruction::Load { literal_idx, .. } => Some(literal_idx),
        Instruction::Move { src, .. } => literal(src),
        _ => None,
    };
    let is_loop = matches!(instruction, Instruction::LoopStart { .. });
    if is_loop {
        super::track(program, &[], instruction, None, paths);
    }
    for register in writes(program, instruction).into_iter().flatten() {
        if !is_loop {
            if let Some(slot) = paths.get_mut(usize::from(register)) {
                *slot = value.clone();
            }
        }
        if let Some(slot) = literals.get_mut(usize::from(register)) {
            *slot = key;
        }
    }
}

struct JsonSource<'a> {
    source: SourceIndex<'a>,
    objects: Vec<Option<usize>>,
    ends: Vec<Option<usize>>,
    fields: Vec<Option<usize>>,
    operators: Vec<Option<PolicyOp>>,
}

type ConditionSource = (
    String,
    Option<SourceLocation>,
    Option<String>,
    Option<PolicyOp>,
);

impl<'a> JsonSource<'a> {
    fn new(file: &'a str, content: &'a str) -> Self {
        let source = SourceIndex::new(file, content);
        let mut objects = alloc::vec![None; source.tokens.len()];
        let mut ends = alloc::vec![None; source.tokens.len()];
        let mut stack = Vec::new();
        for index in 0..source.tokens.len() {
            if let Some(slot) = objects.get_mut(index) {
                *slot = stack.last().copied();
            }
            match source.symbol(index) {
                Some("{") => stack.push(index),
                Some("}") => {
                    if let Some(slot) = stack.pop().and_then(|open| ends.get_mut(open)) {
                        *slot = Some(index);
                    }
                }
                _ => {}
            }
        }
        let mut fields = alloc::vec![None; source.tokens.len()];
        let mut operators = alloc::vec![None; source.tokens.len()];
        for (index, object) in objects.iter().enumerate() {
            if source.symbol(index.saturating_add(1)) == Some(":") {
                if let Some(key) = Self::string_at(&source, index) {
                    if key.eq_ignore_ascii_case("field") {
                        if let Some(slot) = object.and_then(|open| fields.get_mut(open)) {
                            *slot = Some(index.saturating_add(2));
                        }
                    } else if let Some(slot) = object.and_then(|open| operators.get_mut(open)) {
                        if let Some(operator) = Self::source_operator(&key) {
                            *slot = Some(operator);
                        }
                    }
                }
            }
        }
        Self {
            source,
            objects,
            ends,
            fields,
            operators,
        }
    }

    fn string_at(source: &SourceIndex<'_>, index: usize) -> Option<String> {
        let token = source.tokens.get(index)?;
        let (start, end) = token.lexeme();
        serde_json::from_str(source.content.get(start..end)?).ok()
    }

    fn condition(&self, span: &SpanInfo) -> Option<ConditionSource> {
        let anchor = self
            .source
            .tokens
            .binary_search_by(|t| (t.line, t.column).cmp(&(span.line, span.column)))
            .ok()?;
        let mut open = if self.source.symbol(anchor) == Some("{") {
            anchor
        } else {
            self.objects.get(anchor).copied().flatten()?
        };
        let field = self
            .fields
            .get(open)
            .copied()
            .flatten()
            .and_then(|index| Self::string_at(&self.source, index));
        let original = open;
        while self.operators.get(open).copied().flatten().is_none() {
            let Some(parent) = self.objects.get(open).copied().flatten() else {
                open = original;
                break;
            };
            open = parent;
        }
        let close = self.ends.get(open).copied().flatten()?;
        Some((
            self.source.text(open, close)?,
            self.source.location(open),
            field,
            self.operators.get(open).copied().flatten(),
        ))
    }

    fn source_operator(name: &str) -> Option<PolicyOp> {
        Some(match name.to_ascii_lowercase().as_str() {
            "equals" => PolicyOp::Equals,
            "notequals" => PolicyOp::NotEquals,
            "greater" => PolicyOp::Greater,
            "greaterorequals" => PolicyOp::GreaterOrEquals,
            "less" => PolicyOp::Less,
            "lessorequals" => PolicyOp::LessOrEquals,
            "in" => PolicyOp::In,
            "notin" => PolicyOp::NotIn,
            "contains" => PolicyOp::Contains,
            "notcontains" => PolicyOp::NotContains,
            "containskey" => PolicyOp::ContainsKey,
            "notcontainskey" => PolicyOp::NotContainsKey,
            "like" => PolicyOp::Like,
            "notlike" => PolicyOp::NotLike,
            "match" => PolicyOp::Match,
            "notmatch" => PolicyOp::NotMatch,
            "matchinsensitively" => PolicyOp::MatchInsensitively,
            "notmatchinsensitively" => PolicyOp::NotMatchInsensitively,
            "exists" => PolicyOp::Exists,
            "not" => PolicyOp::Not,
            _ => return None,
        })
    }
}
