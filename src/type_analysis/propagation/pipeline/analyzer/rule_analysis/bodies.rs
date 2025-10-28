// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::{borrow::ToOwned, boxed::Box, vec};

use crate::ast::{Expr, RuleBody, RuleHead};
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    RuleAnalysis, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::value::Value;

use super::super::super::result::AnalysisState;
use super::super::TypeAnalyzer;

impl TypeAnalyzer {
    pub(super) fn analyze_rule_body(
        &self,
        module_idx: u32,
        rule_idx: usize,
        body_idx: usize,
        head: &RuleHead,
        body: &RuleBody,
        result: &mut AnalysisState,
        rule_analysis: &mut RuleAnalysis,
        allow_unreachable_diag: bool,
    ) {
        let mut bindings = ScopedBindings::new();
        bindings.ensure_root_scope();

        let specialized_param_facts = match head {
            RuleHead::Func { .. } => self
                .function_param_facts
                .borrow()
                .get(&(module_idx, rule_idx))
                .cloned(),
            _ => None,
        };

        if let RuleHead::Func { args, .. } = head {
            for (arg_idx, arg) in args.iter().enumerate() {
                let binding_plan = self
                    .loop_lookup
                    .as_ref()
                    .and_then(|lookup| lookup.get_expr_binding_plan(module_idx, arg.eidx()));

                let specialized_fact = specialized_param_facts
                    .as_ref()
                    .and_then(|facts| facts.get(arg_idx).cloned());

                let binding_fact = specialized_fact.as_ref().cloned().unwrap_or_else(|| {
                    TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::Any),
                        TypeProvenance::Unknown,
                    )
                });

                if let Some(plan) = binding_plan {
                    self.apply_binding_plan(
                        module_idx,
                        arg,
                        plan,
                        &binding_fact,
                        &mut bindings,
                        result,
                        rule_analysis,
                    );
                } else if let Some(fact) = specialized_fact {
                    self.ensure_expr_capacity(module_idx, arg.eidx(), result);
                    result
                        .lookup
                        .record_expr(module_idx, arg.eidx(), fact.clone());
                    if let Expr::Var { value, .. } = arg.as_ref() {
                        if let Ok(name) = value.as_string() {
                            bindings.assign(name.as_ref().to_owned(), fact);
                        }
                    }
                }
            }
        }

        if let Some(assign) = &body.assign {
            let fact = self
                .infer_expr(
                    module_idx,
                    &assign.value,
                    &mut bindings,
                    result,
                    rule_analysis,
                )
                .fact;
            if let Expr::Var { value, .. } = assign.value.as_ref() {
                if let Ok(name) = value.as_string() {
                    bindings.assign(name.as_ref().to_owned(), fact);
                }
            }
        }

        let query_eval = self.analyze_query(
            module_idx,
            &body.query,
            &mut bindings,
            result,
            rule_analysis,
            allow_unreachable_diag,
        );

        result.record_body_query_truth(
            module_idx,
            rule_idx,
            body_idx,
            query_eval.reachable,
            query_eval.always_true,
        );

        if !query_eval.reachable {
            return;
        }

        if let RuleHead::Func { args, .. } = head {
            for arg in args {
                if let Expr::Var { value, .. } = arg.as_ref() {
                    if let Ok(name) = value.as_string() {
                        if let Some(param_fact) = bindings.lookup(name.as_ref()) {
                            self.ensure_expr_capacity(module_idx, arg.eidx(), result);
                            result
                                .lookup
                                .record_expr(module_idx, arg.eidx(), param_fact.clone());

                            if let Some(const_value) = param_fact.constant.as_value() {
                                result.constants.record(
                                    module_idx,
                                    arg.eidx(),
                                    Some(const_value.clone()),
                                );
                            }
                        }
                    }
                }
            }
        }

        let output_context = self
            .loop_lookup
            .as_ref()
            .and_then(|lookup| lookup.get_query_context(module_idx, body.query.qidx));

        match head {
            RuleHead::Compr { refr, assign, .. } => {
                self.ensure_expr_capacity(module_idx, refr.eidx(), result);

                if let Some(context) = output_context {
                    if let Some(key_expr) = &context.key_expr {
                        let _key_fact = self.infer_expr(
                            module_idx,
                            key_expr,
                            &mut bindings,
                            result,
                            rule_analysis,
                        );

                        if let Some(value_expr) = &context.value_expr {
                            let value_fact = self.infer_expr(
                                module_idx,
                                value_expr,
                                &mut bindings,
                                result,
                                rule_analysis,
                            );

                            let mut recorded_fact = value_fact.fact.clone();
                            if !query_eval.always_true {
                                recorded_fact.constant =
                                    crate::type_analysis::ConstantValue::unknown();
                            }
                            Self::record_rule_head_fact(
                                result,
                                module_idx,
                                refr.eidx(),
                                recorded_fact,
                            );

                            if let Some(expr_idx) = context.value_expr.as_ref().map(|e| e.eidx()) {
                                result.lookup.record_expr(
                                    module_idx,
                                    expr_idx,
                                    value_fact.fact.clone(),
                                );
                            }
                            return;
                        }
                    } else if let Some(value_expr) = &context.value_expr {
                        let value_fact = self.infer_expr(
                            module_idx,
                            value_expr,
                            &mut bindings,
                            result,
                            rule_analysis,
                        );
                        let mut recorded_fact = value_fact.fact.clone();
                        if !query_eval.always_true {
                            recorded_fact.constant = crate::type_analysis::ConstantValue::unknown();
                        }
                        Self::record_rule_head_fact(result, module_idx, refr.eidx(), recorded_fact);
                        return;
                    }
                }

                let fact = self.infer_expr(module_idx, refr, &mut bindings, result, rule_analysis);
                let mut fact_to_record = fact.fact.clone();
                if assign.is_none() {
                    fact_to_record.descriptor = TypeDescriptor::Structural(StructuralType::Boolean);
                    fact_to_record.constant = crate::type_analysis::ConstantValue::unknown();
                } else if !query_eval.always_true {
                    fact_to_record.constant = crate::type_analysis::ConstantValue::unknown();
                }
                Self::record_rule_head_fact(result, module_idx, refr.eidx(), fact_to_record);
            }
            RuleHead::Set { refr, key, .. } => {
                self.ensure_expr_capacity(module_idx, refr.eidx(), result);

                if let Some(context) = output_context {
                    if let Some(value_expr) = &context.value_expr {
                        let element_fact = self.infer_expr(
                            module_idx,
                            value_expr,
                            &mut bindings,
                            result,
                            rule_analysis,
                        );
                        let element_type = match &element_fact.fact.descriptor {
                            TypeDescriptor::Structural(st) => st.clone(),
                            TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
                        };
                        let existing_fact = result.lookup.get_expr(module_idx, refr.eidx());
                        let merged_element_type =
                            Self::merge_set_element_types(existing_fact, element_type);

                        let set_fact = TypeFact::new(
                            TypeDescriptor::Structural(StructuralType::Set(Box::new(
                                merged_element_type,
                            ))),
                            TypeProvenance::Propagated,
                        );

                        Self::record_rule_head_fact(result, module_idx, refr.eidx(), set_fact);
                        return;
                    }
                }

                if let Some(key_expr) = key {
                    self.ensure_expr_capacity(module_idx, key_expr.eidx(), result);
                    let element_fact =
                        self.infer_expr(module_idx, key_expr, &mut bindings, result, rule_analysis);
                    let element_type = match &element_fact.fact.descriptor {
                        TypeDescriptor::Structural(st) => st.clone(),
                        TypeDescriptor::Schema(schema) => StructuralType::from_schema(schema),
                    };
                    let existing_fact = result.lookup.get_expr(module_idx, refr.eidx());
                    let merged_element_type =
                        Self::merge_set_element_types(existing_fact, element_type);
                    let set_fact = TypeFact::new(
                        TypeDescriptor::Structural(StructuralType::Set(Box::new(
                            merged_element_type,
                        ))),
                        TypeProvenance::Propagated,
                    );
                    Self::record_rule_head_fact(result, module_idx, refr.eidx(), set_fact);
                } else {
                    let fact =
                        self.infer_expr(module_idx, refr, &mut bindings, result, rule_analysis);
                    Self::record_rule_head_fact(result, module_idx, refr.eidx(), fact.fact.clone());
                }
            }
            RuleHead::Func { refr, assign, .. } => {
                self.ensure_expr_capacity(module_idx, refr.eidx(), result);

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
                }

                let fact = self.infer_expr(module_idx, refr, &mut bindings, result, rule_analysis);
                let mut fact_to_record = fact.fact.clone();
                if assign.is_none() {
                    fact_to_record.descriptor = TypeDescriptor::Structural(StructuralType::Boolean);
                    fact_to_record.constant = crate::type_analysis::ConstantValue::unknown();
                }
                let fact_informative = fact_is_informative(&fact_to_record);
                let assign_informative = assign_value_fact
                    .as_ref()
                    .map(|(_, informative)| *informative)
                    .unwrap_or(false);
                if let Some((value_fact, _)) = assign_value_fact.as_ref() {
                    let mut recorded_fact = value_fact.clone();
                    if !query_eval.always_true {
                        recorded_fact.constant = crate::type_analysis::ConstantValue::unknown();
                    }
                    Self::record_rule_head_fact(result, module_idx, refr.eidx(), recorded_fact);
                }
                let skip_generic_fact = if assign_value_fact.is_some() {
                    self.disable_function_generic_pass || (assign_informative && !fact_informative)
                } else if has_assign {
                    self.disable_function_generic_pass
                } else {
                    false
                };
                if assign.is_none() {
                    fact_to_record.constant = if query_eval.always_true {
                        crate::type_analysis::ConstantValue::Known(Value::Bool(true))
                    } else {
                        crate::type_analysis::ConstantValue::unknown()
                    };
                } else if !query_eval.always_true {
                    fact_to_record.constant = crate::type_analysis::ConstantValue::unknown();
                }

                if !skip_generic_fact {
                    Self::record_rule_head_fact(result, module_idx, refr.eidx(), fact_to_record);
                }
            }
        }
    }

    pub(super) fn merge_set_element_types(
        existing_fact: Option<&TypeFact>,
        new_element: StructuralType,
    ) -> StructuralType {
        if let Some(existing_fact) = existing_fact {
            match &existing_fact.descriptor {
                TypeDescriptor::Structural(StructuralType::Set(existing_elem)) => {
                    let combined = vec![existing_elem.as_ref().clone(), new_element];
                    Self::join_structural_types(&combined)
                }
                TypeDescriptor::Schema(schema) => {
                    if let StructuralType::Set(existing_elem) = StructuralType::from_schema(schema)
                    {
                        let combined = vec![(*existing_elem).clone(), new_element];
                        Self::join_structural_types(&combined)
                    } else {
                        new_element
                    }
                }
                TypeDescriptor::Structural(StructuralType::Any) => new_element,
                _ => new_element,
            }
        } else {
            new_element
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
