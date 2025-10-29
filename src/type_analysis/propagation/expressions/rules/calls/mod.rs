// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::borrow::ToOwned;
use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::ast::{Expr, Ref};
use crate::lexer::Span;
use crate::type_analysis::builtins;
use crate::type_analysis::builtins::BuiltinTypeTemplate;
use crate::type_analysis::context::ScopedBindings;
use crate::type_analysis::model::{
    ConstantValue, RuleAnalysis, StructuralType, TypeDescriptor, TypeFact, TypeProvenance,
};
use crate::type_analysis::propagation::pipeline::{RuleHeadInfo, TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;

mod effects;
mod resolution;

use effects::apply_rule_call_effects;
use resolution::resolve_call_path;

fn template_description(template: BuiltinTypeTemplate) -> String {
    match template {
        BuiltinTypeTemplate::Any => "any".to_owned(),
        BuiltinTypeTemplate::Boolean => "boolean".to_owned(),
        BuiltinTypeTemplate::Number => "number".to_owned(),
        BuiltinTypeTemplate::Integer => "integer".to_owned(),
        BuiltinTypeTemplate::String => "string".to_owned(),
        BuiltinTypeTemplate::Null => "null".to_owned(),
        BuiltinTypeTemplate::ArrayAny => "array".to_owned(),
        BuiltinTypeTemplate::SetAny => "set".to_owned(),
        BuiltinTypeTemplate::ObjectAny => "object".to_owned(),
        BuiltinTypeTemplate::SameAsArgument(idx) => {
            format!("same type as argument {}", idx + 1)
        }
        BuiltinTypeTemplate::CollectionElement(idx) => {
            format!("element type of argument {}", idx + 1)
        }
    }
}

impl TypeAnalyzer {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn infer_call_expr(
        &self,
        module_idx: u32,
        expr_idx: u32,
        span: &Span,
        fcn: &Ref<Expr>,
        params: &[Ref<Expr>],
        bindings: &mut ScopedBindings,
        result: &mut TypeAnalysisResult,
        rule_analysis: &mut RuleAnalysis,
    ) -> TypeFact {
        let mut arg_types = Vec::with_capacity(params.len());
        for param in params {
            arg_types.push(self.infer_expr(module_idx, param, bindings, result, rule_analysis));
        }

        if let Some(call_name) = resolve_call_path(fcn.as_ref()) {
            if let Some(spec) = builtins::lookup(&call_name) {
                let expected = spec.param_count() as usize;
                let mut matches = expected == arg_types.len();

                if expected != arg_types.len() {
                    self.check_builtin_call_diagnostic(
                        module_idx,
                        span,
                        &call_name,
                        expected,
                        arg_types.len(),
                        result,
                    );
                } else if let Some(templates) = spec.params() {
                    for (idx, template) in templates.iter().enumerate() {
                        if !builtins::matches_template(&arg_types[idx], *template, &arg_types) {
                            matches = false;
                            let expected_type = template_description(*template);
                            self.check_builtin_param_type_diagnostic(
                                module_idx,
                                span,
                                &call_name,
                                idx,
                                &expected_type,
                                &arg_types[idx],
                                result,
                            );
                        }
                    }
                }

                self.check_builtin_additional_rules(
                    module_idx, span, &call_name, &arg_types, result,
                );

                let descriptor = if matches {
                    spec.return_descriptor(&arg_types)
                } else {
                    TypeDescriptor::structural(StructuralType::Any)
                };

                let mut fact = TypeFact::new(descriptor, TypeProvenance::Builtin);

                if matches {
                    let origins = builtins::combined_arg_origins(&arg_types);
                    if !origins.is_empty() {
                        fact = fact.with_origins(origins);
                    }

                    if spec.is_pure() {
                        let all_constant = arg_types
                            .iter()
                            .all(|arg| arg.fact.constant.as_value().is_some());
                        if all_constant {
                            let arg_values: Vec<Value> = arg_types
                                .iter()
                                .filter_map(|arg| arg.fact.constant.as_value().cloned())
                                .collect();

                            if arg_values.len() == arg_types.len() {
                                if let Some(builtin_fn) =
                                    crate::builtins::BUILTINS.get(call_name.as_str())
                                {
                                    let dummy_span = params
                                        .first()
                                        .map(|p| p.span())
                                        .unwrap_or_else(|| fcn.span());
                                    if let Ok(result_value) =
                                        builtin_fn.0(dummy_span, params, &arg_values, false)
                                    {
                                        if result_value != Value::Undefined {
                                            fact = fact
                                                .with_constant(ConstantValue::known(result_value));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                return fact;
            }

            let targets = self.resolve_rule_call_targets(module_idx, &call_name);
            let filtered_targets: Vec<RuleHeadInfo> = targets
                .into_iter()
                .filter(|info| self.function_definition_may_match_call(info, &arg_types))
                .collect();

            if !filtered_targets.is_empty() {
                let call_arg_facts: Vec<TypeFact> =
                    arg_types.iter().map(|arg| arg.fact.clone()).collect();
                let collected_facts = apply_rule_call_effects(
                    self,
                    module_idx,
                    expr_idx,
                    filtered_targets,
                    call_arg_facts,
                    result,
                    rule_analysis,
                );

                if !collected_facts.is_empty() {
                    return Self::merge_rule_facts(&collected_facts);
                }
            }

            return TypeFact::new(
                TypeDescriptor::structural(StructuralType::Any),
                TypeProvenance::Rule,
            );
        }

        TypeFact::new(
            TypeDescriptor::structural(StructuralType::Any),
            TypeProvenance::Unknown,
        )
    }
}
