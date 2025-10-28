// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::{borrow::ToOwned, boxed::Box, vec::Vec};

use crate::ast::{Expr, RuleHead};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, SourceOrigin, StructuralType, TypeDescriptor, TypeFact,
    TypeProvenance,
};

use super::super::super::result::AnalysisState;
use super::super::TypeAnalyzer;

impl TypeAnalyzer {
    pub(super) fn analyze_rule_head_without_body(
        &self,
        module_idx: u32,
        head: &RuleHead,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
    ) {
        let mut bindings = ScopedBindings::new();
        bindings.ensure_root_scope();

        match head {
            RuleHead::Compr { refr, assign, .. } => {
                if let Some(assign) = assign {
                    self.ensure_expr_capacity(module_idx, assign.value.eidx(), result);
                    let value_fact = self.infer_expr(
                        module_idx,
                        &assign.value,
                        &mut bindings,
                        result,
                        rule_analysis,
                    );

                    if let Expr::Var { value, .. } = refr.as_ref() {
                        if let Ok(name) = value.as_string() {
                            bindings.assign(name.as_ref().to_owned(), value_fact.fact.clone());
                        }
                    }
                }

                self.ensure_expr_capacity(module_idx, refr.eidx(), result);
                let fact = self.infer_expr(module_idx, refr, &mut bindings, result, rule_analysis);
                Self::record_rule_head_fact(result, module_idx, refr.eidx(), fact.fact.clone());
            }
            RuleHead::Set { refr, key, .. } => {
                self.ensure_expr_capacity(module_idx, refr.eidx(), result);

                if let Some(key_expr) = key {
                    self.ensure_expr_capacity(module_idx, key_expr.eidx(), result);
                    let element_fact =
                        self.infer_expr(module_idx, key_expr, &mut bindings, result, rule_analysis);

                    let element_type = match &element_fact.fact.descriptor {
                        TypeDescriptor::Structural(st) => st.clone(),
                        TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
                    };

                    let set_fact = TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::Set(Box::new(element_type))),
                        TypeProvenance::Propagated,
                    );

                    Self::record_rule_head_fact(result, module_idx, refr.eidx(), set_fact);
                } else {
                    let fact =
                        self.infer_expr(module_idx, refr, &mut bindings, result, rule_analysis);
                    Self::record_rule_head_fact(result, module_idx, refr.eidx(), fact.fact.clone());
                }
            }
            RuleHead::Func {
                refr, args, assign, ..
            } => {
                let has_assign = assign.is_some();
                let mut assign_value_fact: Option<(TypeFact, bool)> = None;
                if let Some(assign) = assign {
                    self.ensure_expr_capacity(module_idx, assign.value.eidx(), result);
                    let value_fact = self.infer_expr(
                        module_idx,
                        &assign.value,
                        &mut bindings,
                        result,
                        rule_analysis,
                    );

                    let informative = fact_is_informative(&value_fact.fact);
                    if informative || !self.disable_function_generic_pass {
                        assign_value_fact = Some((value_fact.fact.clone(), informative));
                    }

                    if let Expr::Var { value, .. } = refr.as_ref() {
                        if let Ok(name) = value.as_string() {
                            bindings.assign(name.as_ref().to_owned(), value_fact.fact.clone());
                        }
                    }
                }

                for arg in args {
                    self.ensure_expr_capacity(module_idx, arg.eidx(), result);
                    self.infer_expr(module_idx, arg, &mut bindings, result, rule_analysis);
                }

                self.ensure_expr_capacity(module_idx, refr.eidx(), result);
                let fact = self.infer_expr(module_idx, refr, &mut bindings, result, rule_analysis);
                if let Some((assign_fact, _)) = assign_value_fact.as_ref() {
                    Self::record_rule_head_fact(
                        result,
                        module_idx,
                        refr.eidx(),
                        assign_fact.clone(),
                    );
                }

                let fact_informative = fact_is_informative(&fact.fact);
                let assign_informative = assign_value_fact
                    .as_ref()
                    .map(|(_, informative)| *informative)
                    .unwrap_or(false);
                // Only suppress the generic fact when we're dealing with a function rule and the
                // specialized return provided a more precise descriptor. Other rule kinds still
                // rely on the generic pass for baseline facts.
                let skip_generic_fact = if assign_value_fact.is_some() {
                    self.disable_function_generic_pass || (assign_informative && !fact_informative)
                } else if has_assign {
                    self.disable_function_generic_pass
                } else {
                    false
                };

                if !skip_generic_fact {
                    Self::record_rule_head_fact(result, module_idx, refr.eidx(), fact.fact.clone());
                }
            }
        }
    }

    pub(super) fn record_rule_head_fact(
        result: &mut AnalysisState,
        module_idx: u32,
        expr_idx: u32,
        fact: TypeFact,
    ) {
        let TypeFact {
            descriptor,
            constant,
            provenance,
            origins,
            specialization_hits,
        } = fact;

        let provenance = match provenance {
            TypeProvenance::Unknown => TypeProvenance::Rule,
            other => other,
        };

        result.lookup.ensure_expr_capacity(module_idx, expr_idx);

        let slot = result.lookup.expr_types_mut().get_mut(module_idx, expr_idx);

        if let Some(existing) = slot {
            // Use constant-aware merging to preserve enum values
            Self::merge_rule_head_descriptor_with_constants(
                &mut existing.descriptor,
                &existing.constant,
                descriptor,
                &constant,
            );
            existing.constant = Self::merge_rule_head_constant(&existing.constant, constant);
            if matches!(existing.provenance, TypeProvenance::Unknown) {
                existing.provenance = provenance;
            }
            Self::merge_rule_head_origins(&mut existing.origins, origins);
            if !specialization_hits.is_empty() {
                existing
                    .specialization_hits
                    .extend(specialization_hits.into_iter());
            }
        } else {
            let mut stored = TypeFact::new(descriptor, provenance);
            stored.constant = constant;
            Self::merge_rule_head_origins(&mut stored.origins, origins);
            stored.specialization_hits = specialization_hits;
            *slot = Some(stored);
        }
    }

    fn merge_rule_head_constant(
        existing: &ConstantValue,
        incoming: ConstantValue,
    ) -> ConstantValue {
        match (existing, incoming) {
            (ConstantValue::Known(lhs), ConstantValue::Known(rhs)) => {
                if lhs == &rhs {
                    ConstantValue::Known(lhs.clone())
                } else {
                    // Different constants - we lose constant tracking but keep type info
                    ConstantValue::Unknown
                }
            }
            (ConstantValue::Known(lhs), ConstantValue::Unknown) => {
                ConstantValue::Known(lhs.clone())
            }
            (ConstantValue::Unknown, ConstantValue::Known(rhs)) => ConstantValue::Known(rhs),
            (ConstantValue::Unknown, ConstantValue::Unknown) => ConstantValue::Unknown,
        }
    }

    fn merge_rule_head_descriptor_with_constants(
        existing_descriptor: &mut TypeDescriptor,
        existing_constant: &ConstantValue,
        incoming_descriptor: TypeDescriptor,
        incoming_constant: &ConstantValue,
    ) {
        // Only create an Enum if BOTH have known constants
        let both_have_constants = matches!(existing_constant, ConstantValue::Known(_))
            && matches!(incoming_constant, ConstantValue::Known(_));

        if both_have_constants {
            // Collect known constant values
            let mut enum_values = alloc::vec::Vec::new();

            if let ConstantValue::Known(val) = existing_constant {
                enum_values.push(val.clone());
            }

            if let ConstantValue::Known(val) = incoming_constant {
                if !enum_values.contains(val) {
                    enum_values.push(val.clone());
                }
            }

            // If we have multiple distinct constants, create an Enum type
            if enum_values.len() > 1 {
                *existing_descriptor =
                    TypeDescriptor::Structural(StructuralType::Enum(enum_values));
                return;
            }
        }

        if let TypeDescriptor::Structural(StructuralType::Enum(enum_values)) = existing_descriptor {
            if let TypeDescriptor::Structural(StructuralType::Enum(incoming_values)) =
                &incoming_descriptor
            {
                let mut added = false;
                for value in incoming_values {
                    if !enum_values.contains(value) {
                        enum_values.push(value.clone());
                        added = true;
                    }
                }
                if added {
                    return;
                }
            }

            if let ConstantValue::Known(value) = incoming_constant {
                if !enum_values.contains(value) {
                    enum_values.push(value.clone());
                }
                return;
            }
        }

        // Otherwise use standard merging
        let (incoming_structural, incoming_was_schema) = match incoming_descriptor {
            TypeDescriptor::Structural(st) => (st, false),
            TypeDescriptor::Schema(schema) => (StructuralType::from_schema(&schema), true),
        };

        let (existing_structural, existing_was_schema) = match existing_descriptor {
            TypeDescriptor::Structural(st) => (st.clone(), false),
            TypeDescriptor::Schema(schema) => (StructuralType::from_schema(schema), true),
        };

        if existing_was_schema && incoming_was_schema && existing_structural == incoming_structural
        {
            return;
        }

        let merged = Self::join_structural_types(&[existing_structural, incoming_structural]);
        *existing_descriptor = TypeDescriptor::Structural(merged);
    }

    fn merge_rule_head_origins(existing: &mut Vec<SourceOrigin>, incoming: Vec<SourceOrigin>) {
        if incoming.is_empty() {
            return;
        }

        if existing.is_empty() {
            *existing = incoming;
            return;
        }

        for origin in incoming {
            if !existing.contains(&origin) {
                existing.push(origin);
            }
        }
    }
}

fn fact_is_informative(fact: &TypeFact) -> bool {
    match &fact.descriptor {
        TypeDescriptor::Structural(ty) => !structural_contains_unknownish(ty),
        _ => true,
    }
}

fn structural_contains_unknownish(ty: &StructuralType) -> bool {
    match ty {
        StructuralType::Any | StructuralType::Unknown => true,
        StructuralType::Union(variants) => variants.iter().any(structural_contains_unknownish),
        _ => false,
    }
}
