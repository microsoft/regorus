// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::redundant_pub_crate,
    clippy::missing_const_for_fn,
    clippy::option_if_let_else,
    clippy::pattern_type_mismatch
)]

use crate::ast::*;
use crate::compiler::hoist::HoistedLoopsLookup;
use crate::engine::Engine;
use crate::scheduler::*;
use crate::utils::*;
use crate::*;

use alloc::collections::BTreeMap;
use anyhow::Result;

#[cfg(feature = "azure_policy")]
use crate::target::Target;

pub(crate) type DefaultRuleInfo = (Ref<Rule>, Option<crate::String>);

#[cfg(feature = "azure_policy")]
pub(crate) type ResourceTypeInfo = (Rc<str>, Rc<Schema>);

#[cfg(feature = "azure_policy")]
pub(crate) type InferredResourceTypes = BTreeMap<Ref<Query>, ResourceTypeInfo>;

/// Wrapper around CompiledPolicyData that holds an Rc reference.
#[derive(Debug, Clone)]
pub struct CompiledPolicy {
    pub(crate) inner: Rc<CompiledPolicyData>,
}

impl CompiledPolicy {
    /// Create a new CompiledPolicy from CompiledPolicyData.
    pub(crate) fn new(inner: Rc<CompiledPolicyData>) -> Self {
        Self { inner }
    }

    /// Get access to the rules in the compiled policy for downstream consumers like the RVM compiler.
    pub fn get_rules(&self) -> &Map<String, Vec<Ref<Rule>>> {
        &self.inner.rules
    }

    /// Get access to the modules in the compiled policy.
    pub fn get_modules(&self) -> &Vec<Ref<Module>> {
        self.inner.modules.as_ref()
    }

    /// Returns true when the compiled policy should use Rego v0 semantics.
    pub fn is_rego_v0(&self) -> bool {
        !self.inner.modules.iter().any(|module| module.rego_v1)
    }
}

impl CompiledPolicy {
    /// Evaluate the compiled policy with the given input.
    ///
    /// For target policies, evaluates the target's effect rule.
    /// For regular policies, evaluates the originally compiled rule.
    ///
    /// * `input`: Input data (resource) to validate against the policy.
    ///
    /// Returns the result of evaluating the rule.
    pub fn eval_with_input(&self, input: Value) -> Result<Value> {
        let mut engine = Engine::new_from_compiled_policy(self.inner.clone());

        // Set input
        engine.set_input(input);

        // Evaluate the rule
        #[cfg(feature = "azure_policy")]
        if let Some(target_info) = self.inner.target_info.as_ref() {
            return engine.eval_rule(target_info.effect_path.to_string());
        }
        engine.eval_rule(self.inner.rule_to_evaluate.to_string())
    }

    /// Get information about the compiled policy including metadata about modules,
    /// target configuration, and resource types.
    ///
    /// Returns a [`crate::policy_info::PolicyInfo`] struct containing comprehensive
    /// information about the compiled policy such as module IDs, target name,
    /// applicable resource types, entry point rule, and parameters.
    ///
    /// # Examples
    ///
    /// ```no_run
    /// use regorus::*;
    /// # use std::sync::Arc;
    ///
    /// # fn main() -> anyhow::Result<()> {
    /// # // Register a target for the example
    /// # #[cfg(feature = "azure_policy")]
    /// # {
    /// #    let target = regorus::target::Target::from_json_file("tests/interpreter/cases/target/definitions/sample_target.json")?;
    /// #    regorus::registry::targets::register(std::sync::Arc::new(target))?;
    /// # }
    ///
    /// // Compile the policy
    /// let policy_rego = r#"
    ///     package policy.example
    ///     import rego.v1
    ///     __target__ := "target.tests.sample_test_target"
    ///     
    ///     effect := "allow" if {
    ///         input.type == "storage_account"
    ///         input.location in ["eastus", "westus"]
    ///     }
    /// "#;
    ///
    /// let modules = vec![regorus::PolicyModule {
    ///     id: "policy.rego".into(),
    ///     content: policy_rego.into(),
    /// }];
    ///
    /// #[cfg(feature = "azure_policy")]
    /// let compiled = regorus::compile_policy_for_target(Value::new_object(), &modules)?;
    /// #[cfg(not(feature = "azure_policy"))]
    /// let compiled = regorus::compile_policy_with_entrypoint(Value::new_object(), &modules, "allow".into())?;
    /// let info = compiled.get_policy_info()?;
    ///
    /// assert_eq!(info.target_name, Some("target.tests.sample_test_target".into()));
    /// assert_eq!(info.effect_rule, Some("effect".into()));
    /// assert!(info.module_ids.len() > 0);
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_policy_info(&self) -> Result<crate::policy_info::PolicyInfo> {
        // Extract module IDs from the compiled policy
        let module_ids: Vec<Rc<str>> = self
            .inner
            .modules
            .iter()
            .enumerate()
            .map(|(i, module)| {
                // Use source file path if available, otherwise generate an ID
                let source_path = module.package.span.source.get_path();
                if source_path.is_empty() {
                    format!("module_{}", i).into()
                } else {
                    source_path.clone().into()
                }
            })
            .collect();

        // Extract target name and effect rule
        #[cfg(feature = "azure_policy")]
        let (target_name, effect_rule) = if let Some(target_info) = &self.inner.target_info {
            (
                Some(target_info.target.name.clone()),
                Some(target_info.effect_name.clone()),
            )
        } else {
            (None, None)
        };

        #[cfg(not(feature = "azure_policy"))]
        let (target_name, effect_rule) = (None, None);

        // Extract applicable resource types from inferred types
        #[cfg(feature = "azure_policy")]
        let applicable_resource_types: Vec<Rc<str>> =
            if let Some(inferred_types) = &self.inner.inferred_resource_types {
                inferred_types
                    .values()
                    .map(|(resource_type, _schema)| resource_type.clone())
                    .collect::<std::collections::BTreeSet<_>>() // Remove duplicates
                    .into_iter()
                    .collect()
            } else {
                Vec::new()
            };

        #[cfg(not(feature = "azure_policy"))]
        let applicable_resource_types: Vec<Rc<str>> = Vec::new();

        // Get parameters from the modules
        #[cfg(feature = "azure_policy")]
        let parameters = {
            // Create a new engine from the compiled modules to extract parameters
            let temp_engine = crate::engine::Engine::new_from_compiled_policy(self.inner.clone());

            temp_engine.get_policy_parameters()?
        };

        Ok(crate::policy_info::PolicyInfo {
            module_ids,
            target_name,
            applicable_resource_types,
            entrypoint_rule: self.inner.rule_to_evaluate.clone(),
            effect_rule,
            #[cfg(feature = "azure_policy")]
            parameters,
        })
    }
}

#[cfg(feature = "azure_policy")]
#[derive(Debug, Clone)]
pub(crate) struct TargetInfo {
    pub(crate) target: Rc<Target>,
    pub(crate) package: String,
    pub(crate) effect_schema: Rc<Schema>,
    pub(crate) effect_name: Rc<str>,
    pub(crate) effect_path: Rc<str>,
}

#[derive(Debug, Clone, Default)]
pub(crate) struct CompiledPolicyData {
    pub(crate) modules: Rc<Vec<Ref<Module>>>,
    pub(crate) schedule: Option<Rc<Schedule>>,
    pub(crate) rules: Map<String, Vec<Ref<Rule>>>,
    pub(crate) default_rules: Map<String, Vec<DefaultRuleInfo>>,
    pub(crate) imports: BTreeMap<String, Ref<Expr>>,
    pub(crate) functions: FunctionTable,
    pub(crate) rule_paths: Set<String>,
    #[cfg(feature = "azure_policy")]
    pub(crate) target_info: Option<TargetInfo>,
    #[cfg(feature = "azure_policy")]
    pub(crate) inferred_resource_types: Option<InferredResourceTypes>,

    // User-defined rule to evaluate
    pub(crate) rule_to_evaluate: Rc<str>,

    // User-defined data
    pub(crate) data: Option<Value>,

    // Evaluation settings
    pub(crate) strict_builtin_errors: bool,

    // The semantics of extensions ought to be changes to be more Clone friendly.
    pub(crate) extensions: Map<String, (u8, Rc<Box<dyn Extension>>)>,

    // Pre-computed loop hoisting information
    pub(crate) loop_hoisting_table: HoistedLoopsLookup,
}
