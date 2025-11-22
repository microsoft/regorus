// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;

use crate::schema::Type as SchemaType;
use crate::type_analysis::model::{HybridType, SourceOrigin, StructuralType, TypeDescriptor};

use super::spec::BuiltinTypeTemplate;

pub fn matches_template(
    arg: &HybridType,
    template: BuiltinTypeTemplate,
    args: &[HybridType],
) -> bool {
    match template {
        BuiltinTypeTemplate::Any => true,
        BuiltinTypeTemplate::Boolean => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::Number => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::Integer => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::String => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::Null => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::ArrayAny => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::SetAny => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::ObjectAny => descriptor_matches(&arg.fact.descriptor, template),
        BuiltinTypeTemplate::SameAsArgument(idx) => args
            .get(idx as usize)
            .map(|other| descriptors_compatible(&arg.fact.descriptor, &other.fact.descriptor))
            .unwrap_or(true),
        BuiltinTypeTemplate::CollectionElement(_) => true,
    }
}

fn descriptor_matches(descriptor: &TypeDescriptor, template: BuiltinTypeTemplate) -> bool {
    match descriptor {
        TypeDescriptor::Structural(structural) => structural_matches(structural, template),
        TypeDescriptor::Schema(schema) => schema_matches(schema.as_type(), template),
    }
}

fn structural_matches(ty: &StructuralType, template: BuiltinTypeTemplate) -> bool {
    match template {
        BuiltinTypeTemplate::Any => true,
        BuiltinTypeTemplate::Boolean => matches!(ty, StructuralType::Boolean | StructuralType::Any),
        BuiltinTypeTemplate::Number => matches!(
            ty,
            StructuralType::Number | StructuralType::Integer | StructuralType::Any
        ),
        BuiltinTypeTemplate::Integer => matches!(ty, StructuralType::Integer | StructuralType::Any),
        BuiltinTypeTemplate::String => matches!(ty, StructuralType::String | StructuralType::Any),
        BuiltinTypeTemplate::Null => matches!(ty, StructuralType::Null | StructuralType::Any),
        BuiltinTypeTemplate::ArrayAny => {
            matches!(ty, StructuralType::Array(_) | StructuralType::Any)
        }
        BuiltinTypeTemplate::SetAny => matches!(ty, StructuralType::Set(_) | StructuralType::Any),
        BuiltinTypeTemplate::ObjectAny => {
            matches!(ty, StructuralType::Object(_) | StructuralType::Any)
        }
        BuiltinTypeTemplate::SameAsArgument(_) | BuiltinTypeTemplate::CollectionElement(_) => true,
    }
}

fn schema_matches(schema_type: &SchemaType, template: BuiltinTypeTemplate) -> bool {
    match schema_type {
        SchemaType::Any { .. } => true,
        SchemaType::Boolean { .. } => matches!(
            template,
            BuiltinTypeTemplate::Any | BuiltinTypeTemplate::Boolean
        ),
        SchemaType::Integer { .. } => matches!(
            template,
            BuiltinTypeTemplate::Any | BuiltinTypeTemplate::Integer | BuiltinTypeTemplate::Number
        ),
        SchemaType::Number { .. } => matches!(
            template,
            BuiltinTypeTemplate::Any | BuiltinTypeTemplate::Number
        ),
        SchemaType::Null { .. } => matches!(
            template,
            BuiltinTypeTemplate::Any | BuiltinTypeTemplate::Null
        ),
        SchemaType::String { .. } => matches!(
            template,
            BuiltinTypeTemplate::Any | BuiltinTypeTemplate::String
        ),
        SchemaType::Array { items, .. } => {
            matches!(
                template,
                BuiltinTypeTemplate::Any | BuiltinTypeTemplate::ArrayAny
            ) || schema_matches(items.as_type(), template)
        }
        SchemaType::Set { items, .. } => {
            matches!(
                template,
                BuiltinTypeTemplate::Any | BuiltinTypeTemplate::SetAny
            ) || schema_matches(items.as_type(), template)
        }
        SchemaType::Object { .. } => matches!(
            template,
            BuiltinTypeTemplate::Any | BuiltinTypeTemplate::ObjectAny
        ),
        SchemaType::AnyOf(variants) => variants
            .iter()
            .any(|variant| schema_matches(variant.as_type(), template)),
        SchemaType::Const { .. } | SchemaType::Enum { .. } => true,
    }
}

fn descriptors_compatible(lhs: &TypeDescriptor, rhs: &TypeDescriptor) -> bool {
    matches!(
        (lhs, rhs),
        (TypeDescriptor::Structural(_), TypeDescriptor::Structural(_))
            | (TypeDescriptor::Schema(_), TypeDescriptor::Schema(_))
    )
}

pub fn combined_arg_origins(args: &[HybridType]) -> Vec<SourceOrigin> {
    let mut origins = Vec::new();
    for arg in args {
        origins.extend(arg.fact.origins.iter().cloned());
    }
    origins
}
