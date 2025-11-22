// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::collections::BTreeSet;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::type_analysis::model::{HybridType, StructuralType, TypeDescriptor};
use crate::type_analysis::propagation::pipeline::TypeAnalyzer;
use crate::value::Value;

use super::categories::StructuralCategory;

impl TypeAnalyzer {
    pub(super) fn get_file_for_module(&self, module_idx: u32) -> crate::Rc<str> {
        self.modules
            .get(module_idx as usize)
            .map(|m| m.as_ref().package.span.source.get_path().as_str())
            .unwrap_or("<unknown>")
            .into()
    }

    pub(super) fn hybrid_structural_type(ty: &HybridType) -> StructuralType {
        match &ty.fact.descriptor {
            TypeDescriptor::Structural(struct_ty) => struct_ty.clone(),
            TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
        }
    }

    pub(super) fn structural_types_certainly_disjoint(
        lhs: &StructuralType,
        rhs: &StructuralType,
    ) -> bool {
        let mut lhs_categories = BTreeSet::new();
        if Self::collect_structural_categories(lhs, &mut lhs_categories) {
            return false;
        }

        let mut rhs_categories = BTreeSet::new();
        if Self::collect_structural_categories(rhs, &mut rhs_categories) {
            return false;
        }

        if lhs_categories.is_empty() || rhs_categories.is_empty() {
            return false;
        }

        !lhs_categories
            .iter()
            .any(|category| rhs_categories.contains(category))
    }

    pub(super) fn hybrid_can_be_numeric(ty: &HybridType) -> bool {
        if let Some(value) = ty.fact.constant.as_value() {
            return matches!(value, Value::Number(_));
        }
        Self::structural_type_can_be_numeric(&Self::hybrid_structural_type(ty))
    }

    pub(crate) fn hybrid_can_be_integer(ty: &HybridType) -> bool {
        if let Some(value) = ty.fact.constant.as_value() {
            if let Ok(number) = value.as_number() {
                return number.is_integer();
            }
            return false;
        }
        Self::structural_type_can_be_integer(&Self::hybrid_structural_type(ty))
    }

    pub(super) fn hybrid_can_be_set(ty: &HybridType) -> bool {
        if let Some(value) = ty.fact.constant.as_value() {
            return matches!(value, Value::Set(_));
        }
        Self::structural_type_can_be_set(&Self::hybrid_structural_type(ty))
    }

    pub(super) fn hybrid_can_be_collection(ty: &HybridType) -> bool {
        if let Some(value) = ty.fact.constant.as_value() {
            return matches!(value, Value::Array(_) | Value::Set(_) | Value::Object(_));
        }
        Self::structural_type_can_be_collection(&Self::hybrid_structural_type(ty))
    }

    pub(super) fn hybrid_type_display(ty: &HybridType) -> String {
        if let Some(value) = ty.fact.constant.as_value() {
            return format!("constant {}", value);
        }
        Self::diagnostic_structural_type_label(&Self::hybrid_structural_type(ty))
    }

    pub(super) fn arithmetic_op_token(op: &crate::ast::ArithOp) -> &'static str {
        match op {
            crate::ast::ArithOp::Add => "+",
            crate::ast::ArithOp::Sub => "-",
            crate::ast::ArithOp::Mul => "*",
            crate::ast::ArithOp::Div => "/",
            crate::ast::ArithOp::Mod => "%",
        }
    }

    fn structural_type_can_be_numeric(ty: &StructuralType) -> bool {
        match ty {
            StructuralType::Number | StructuralType::Integer => true,
            StructuralType::Any | StructuralType::Unknown => true,
            StructuralType::Union(variants) => {
                variants.iter().any(Self::structural_type_can_be_numeric)
            }
            StructuralType::Enum(values) => {
                values.iter().any(|value| matches!(value, Value::Number(_)))
            }
            _ => false,
        }
    }

    fn structural_type_can_be_integer(ty: &StructuralType) -> bool {
        match ty {
            StructuralType::Integer => true,
            StructuralType::Number => true,
            StructuralType::Any | StructuralType::Unknown => true,
            StructuralType::Union(variants) => {
                variants.iter().any(Self::structural_type_can_be_integer)
            }
            StructuralType::Enum(values) => values.iter().any(|value| {
                if let Value::Number(num) = value {
                    num.is_integer()
                } else {
                    false
                }
            }),
            _ => false,
        }
    }

    fn structural_type_can_be_set(ty: &StructuralType) -> bool {
        match ty {
            StructuralType::Set(_) => true,
            StructuralType::Any | StructuralType::Unknown => true,
            StructuralType::Union(variants) => {
                variants.iter().any(Self::structural_type_can_be_set)
            }
            _ => false,
        }
    }

    fn structural_type_can_be_collection(ty: &StructuralType) -> bool {
        match ty {
            StructuralType::Array(_) | StructuralType::Set(_) | StructuralType::Object(_) => true,
            StructuralType::Any | StructuralType::Unknown => true,
            StructuralType::Union(variants) => {
                variants.iter().any(Self::structural_type_can_be_collection)
            }
            _ => false,
        }
    }

    fn diagnostic_structural_type_label(ty: &StructuralType) -> String {
        match ty {
            StructuralType::Any => "any".into(),
            StructuralType::Unknown => "unknown".into(),
            StructuralType::Boolean => "boolean".into(),
            StructuralType::Number => "number".into(),
            StructuralType::Integer => "integer".into(),
            StructuralType::String => "string".into(),
            StructuralType::Null => "null".into(),
            StructuralType::Array(inner) => {
                format!("array<{}>", Self::diagnostic_structural_type_label(inner))
            }
            StructuralType::Set(inner) => {
                format!("set<{}>", Self::diagnostic_structural_type_label(inner))
            }
            StructuralType::Object(_) => "object".into(),
            StructuralType::Union(variants) => {
                let labels: Vec<_> = variants
                    .iter()
                    .map(Self::diagnostic_structural_type_label)
                    .collect();
                labels.join(" | ")
            }
            StructuralType::Enum(values) => {
                let labels: Vec<_> = values.iter().map(|value| value.to_string()).collect();
                format!("enum {{ {} }}", labels.join(", "))
            }
        }
    }

    fn collect_structural_categories(
        ty: &StructuralType,
        output: &mut BTreeSet<StructuralCategory>,
    ) -> bool {
        use StructuralCategory::*;
        match ty {
            StructuralType::Any => true,
            StructuralType::Unknown => false,
            StructuralType::Boolean => {
                output.insert(Boolean);
                false
            }
            StructuralType::Number | StructuralType::Integer => {
                output.insert(Number);
                false
            }
            StructuralType::String => {
                output.insert(String);
                false
            }
            StructuralType::Null => {
                output.insert(Null);
                false
            }
            StructuralType::Array(_) => {
                output.insert(Array);
                false
            }
            StructuralType::Set(_) => {
                output.insert(Set);
                false
            }
            StructuralType::Object(_) => {
                output.insert(Object);
                false
            }
            StructuralType::Union(variants) => {
                for variant in variants {
                    if Self::collect_structural_categories(variant, output) {
                        return true;
                    }
                }
                false
            }
            StructuralType::Enum(values) => {
                for value in values {
                    if let Some(category) = Self::category_from_value(value) {
                        output.insert(category);
                    }
                }
                false
            }
        }
    }

    fn category_from_value(value: &Value) -> Option<StructuralCategory> {
        use StructuralCategory::*;
        match value {
            Value::Null => Some(Null),
            Value::Bool(_) => Some(Boolean),
            Value::Number(_) => Some(Number),
            Value::String(_) => Some(String),
            Value::Array(_) => Some(Array),
            Value::Set(_) => Some(Set),
            Value::Object(_) => Some(Object),
            Value::Undefined => Some(Undefined),
        }
    }
}
