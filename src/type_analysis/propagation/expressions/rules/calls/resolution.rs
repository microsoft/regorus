// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::ast::{Expr, Rule, RuleHead};
use crate::type_analysis::model::{HybridType, StructuralType, TypeDescriptor};
use crate::type_analysis::propagation::pipeline::{RuleHeadInfo, TypeAnalyzer};
use crate::utils::get_path_string;
use crate::utils::path::normalize_rule_path;
use crate::value::Value;

pub(crate) fn resolve_call_path(expr: &Expr) -> Option<String> {
    let mut segments: Vec<String> = Vec::new();
    let mut current = expr;

    loop {
        match current {
            Expr::RefDot { refr, field, .. } => {
                let (_, field_value) = field.as_ref()?;
                let segment = field_value.as_string().ok()?.as_ref().to_owned();
                segments.push(segment);
                current = refr.as_ref();
            }
            Expr::RefBrack { refr, index, .. } => {
                if let Expr::String { value, .. } = index.as_ref() {
                    let segment = value.as_string().ok()?.as_ref().to_owned();
                    segments.push(segment);
                    current = refr.as_ref();
                } else {
                    return None;
                }
            }
            Expr::Var { value, .. } => {
                let segment = value.as_string().ok()?.as_ref().to_owned();
                segments.push(segment);
                break;
            }
            _ => return None,
        }
    }

    segments.reverse();
    Some(segments.join("."))
}

impl TypeAnalyzer {
    pub(crate) fn resolve_rule_call_targets(
        &self,
        module_idx: u32,
        call_name: &str,
    ) -> Vec<RuleHeadInfo> {
        let mut acceptable_paths: BTreeSet<String> = BTreeSet::new();

        if call_name.starts_with("data.") {
            acceptable_paths.insert(normalize_rule_path(call_name));
        } else if call_name.contains('.') {
            acceptable_paths.insert(normalize_rule_path(&format!("data.{call_name}")));
        }

        let module_path = self
            .modules
            .get(module_idx as usize)
            .and_then(|module| get_path_string(module.package.refr.as_ref(), Some("data")).ok())
            .unwrap_or_else(|| "data".to_owned());

        acceptable_paths.insert(normalize_rule_path(&format!("{module_path}.{call_name}")));

        let key = call_name.rsplit('.').next().unwrap_or(call_name);
        let mut matches = Vec::new();
        let mut seen_indices: BTreeSet<(u32, u32)> = BTreeSet::new();

        for info in self.rule_heads_for_name(module_idx, key) {
            let normalized = normalize_rule_path(&info.path);
            if acceptable_paths.contains(&normalized)
                && seen_indices.insert((info.module_idx, info.expr_idx))
            {
                matches.push(info.clone());
            }
        }

        matches
    }

    pub(crate) fn function_definition_may_match_call(
        &self,
        info: &RuleHeadInfo,
        call_args: &[HybridType],
    ) -> bool {
        if let Some(module) = self.modules.get(info.module_idx as usize) {
            if let Some(rule) = module.policy.get(info.rule_idx) {
                if let Rule::Spec {
                    head: RuleHead::Func { args, .. },
                    ..
                } = rule.as_ref()
                {
                    if args.len() != call_args.len() {
                        return false;
                    }

                    for (head_arg, call_arg) in args.iter().zip(call_args.iter()) {
                        if !function_head_arg_matches_call(head_arg.as_ref(), call_arg) {
                            return false;
                        }
                    }

                    return true;
                }
            }
        }

        true
    }
}

fn function_head_arg_matches_call(head_arg: &Expr, call_arg: &HybridType) -> bool {
    if let Some(literal) = literal_value_from_expr(head_arg) {
        if let Some(call_value) = call_arg.fact.constant.as_value() {
            if call_value == &Value::Undefined {
                return true;
            }

            return call_value == &literal;
        }

        let structural = match &call_arg.fact.descriptor {
            TypeDescriptor::Structural(st) => st.clone(),
            TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
        };

        return structural_type_accepts_value(&structural, &literal);
    }

    true
}

fn literal_value_from_expr(expr: &Expr) -> Option<Value> {
    match expr {
        Expr::String { value, .. }
        | Expr::RawString { value, .. }
        | Expr::Number { value, .. }
        | Expr::Bool { value, .. }
        | Expr::Null { value, .. } => Some(value.clone()),
        _ => None,
    }
}

fn structural_type_accepts_value(ty: &StructuralType, value: &Value) -> bool {
    use crate::value::Value as Val;

    match ty {
        StructuralType::Any | StructuralType::Unknown => true,
        StructuralType::Boolean => matches!(value, Val::Bool(_)),
        StructuralType::Number => matches!(value, Val::Number(_)),
        StructuralType::Integer => matches!(value, Val::Number(num) if num.is_integer()),
        StructuralType::String => matches!(value, Val::String(_)),
        StructuralType::Null => matches!(value, Val::Null),
        StructuralType::Array(_) => matches!(value, Val::Array(_)),
        StructuralType::Set(_) => matches!(value, Val::Set(_)),
        StructuralType::Object(_) => matches!(value, Val::Object(_)),
        StructuralType::Union(variants) => variants
            .iter()
            .any(|variant| structural_type_accepts_value(variant, value)),
        StructuralType::Enum(values) => values.iter().any(|variant| variant == value),
    }
}
