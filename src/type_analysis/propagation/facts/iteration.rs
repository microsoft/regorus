// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::vec::Vec;

use crate::schema::Type;
use crate::type_analysis::model::{
    PathSegment, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};

use super::{extend_origins_with_segment, mark_origins_derived};
use crate::type_analysis::propagation::pipeline::TypeAnalyzer;

pub(crate) struct IterationFacts {
    pub(crate) value_fact: TypeFact,
    pub(crate) key_fact: Option<TypeFact>,
}

impl TypeAnalyzer {
    pub(crate) fn build_iteration_facts(&self, collection_fact: &TypeFact) -> IterationFacts {
        let provenance = match collection_fact.provenance {
            TypeProvenance::SchemaInput => TypeProvenance::SchemaInput,
            TypeProvenance::SchemaData => TypeProvenance::SchemaData,
            _ => TypeProvenance::Propagated,
        };

        let derived_origins = if collection_fact.origins.is_empty() {
            Vec::new()
        } else {
            mark_origins_derived(&extend_origins_with_segment(
                &collection_fact.origins,
                PathSegment::Any,
            ))
        };

        match &collection_fact.descriptor {
            TypeDescriptor::Schema(schema) => match schema.as_type() {
                Type::Array { items, .. } => {
                    let mut value_fact =
                        TypeFact::new(TypeDescriptor::Schema(items.clone()), provenance.clone());
                    if !derived_origins.is_empty() {
                        value_fact = value_fact.with_origins(derived_origins.clone());
                    }

                    let mut key_fact = TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::Integer),
                        provenance,
                    );
                    if !value_fact.origins.is_empty() {
                        key_fact = key_fact.with_origins(value_fact.origins.clone());
                    }

                    IterationFacts {
                        value_fact,
                        key_fact: Some(key_fact),
                    }
                }
                Type::Set { items, .. } => {
                    let mut value_fact =
                        TypeFact::new(TypeDescriptor::Schema(items.clone()), provenance.clone());
                    if !derived_origins.is_empty() {
                        value_fact = value_fact.with_origins(derived_origins.clone());
                    }

                    let key_fact = Some(value_fact.clone());

                    IterationFacts {
                        value_fact,
                        key_fact,
                    }
                }
                Type::Object {
                    properties,
                    additional_properties,
                    ..
                } => {
                    let mut property_types: Vec<StructuralType> = properties
                        .values()
                        .map(StructuralType::from_schema)
                        .collect();

                    if let Some(additional) = additional_properties {
                        property_types.push(StructuralType::from_schema(additional));
                    }

                    let value_descriptor = if property_types.is_empty() {
                        TypeDescriptor::Structural(StructuralType::Any)
                    } else {
                        let joined = Self::join_structural_types(&property_types);
                        TypeDescriptor::Structural(joined)
                    };

                    let mut value_fact = TypeFact::new(value_descriptor, provenance.clone());
                    if !derived_origins.is_empty() {
                        value_fact = value_fact.with_origins(derived_origins.clone());
                    }

                    let mut key_fact = TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::String),
                        provenance,
                    );
                    if !derived_origins.is_empty() {
                        key_fact = key_fact.with_origins(derived_origins);
                    }

                    IterationFacts {
                        value_fact,
                        key_fact: Some(key_fact),
                    }
                }
                _ => IterationFacts {
                    value_fact: TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::Any),
                        provenance,
                    ),
                    key_fact: None,
                },
            },
            TypeDescriptor::Structural(struct_ty) => match struct_ty {
                StructuralType::Array(element_ty) => {
                    let mut value_fact = TypeFact::new(
                        TypeDescriptor::Structural((**element_ty).clone()),
                        provenance.clone(),
                    );
                    if !derived_origins.is_empty() {
                        value_fact = value_fact.with_origins(derived_origins.clone());
                    }

                    let mut key_fact = TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::Integer),
                        provenance,
                    );
                    if !derived_origins.is_empty() {
                        key_fact = key_fact.with_origins(derived_origins);
                    }

                    IterationFacts {
                        value_fact,
                        key_fact: Some(key_fact),
                    }
                }
                StructuralType::Set(element_ty) => {
                    let mut value_fact = TypeFact::new(
                        TypeDescriptor::Structural((**element_ty).clone()),
                        provenance.clone(),
                    );
                    if !derived_origins.is_empty() {
                        value_fact = value_fact.with_origins(derived_origins.clone());
                    }

                    let key_fact = Some(value_fact.clone());

                    IterationFacts {
                        value_fact,
                        key_fact,
                    }
                }
                StructuralType::Object(shape) => {
                    let property_types: Vec<StructuralType> =
                        shape.fields.values().cloned().collect();

                    let value_descriptor = if property_types.is_empty() {
                        TypeDescriptor::Structural(StructuralType::Any)
                    } else {
                        let joined = Self::join_structural_types(&property_types);
                        TypeDescriptor::Structural(joined)
                    };

                    let mut value_fact = TypeFact::new(value_descriptor, provenance.clone());
                    if !derived_origins.is_empty() {
                        value_fact = value_fact.with_origins(derived_origins.clone());
                    }

                    let mut key_fact = TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::String),
                        provenance,
                    );
                    if !derived_origins.is_empty() {
                        key_fact = key_fact.with_origins(derived_origins);
                    }

                    IterationFacts {
                        value_fact,
                        key_fact: Some(key_fact),
                    }
                }
                _ => IterationFacts {
                    value_fact: TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::Any),
                        provenance,
                    ),
                    key_fact: None,
                },
            },
        }
    }
}
