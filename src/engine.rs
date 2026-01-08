// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::print_stderr)]

use crate::ast::*;
use crate::compiled_policy::CompiledPolicy;
use crate::interpreter::*;
use crate::lexer::*;
use crate::parser::*;
use crate::scheduler::*;
use crate::utils::gather_functions;
use crate::utils::limits::{self, fallback_execution_timer_config, ExecutionTimerConfig};
use crate::value::*;
use crate::*;
use crate::{Extension, QueryResults};

use crate::Rc;
use anyhow::{anyhow, bail, Result};

/// The Rego evaluation engine.
///
#[derive(Debug, Clone)]
pub struct Engine {
    modules: Rc<Vec<Ref<Module>>>,
    interpreter: Interpreter,
    prepared: bool,
    rego_v1: bool,
    execution_timer_config: Option<ExecutionTimerConfig>,
}

#[cfg(feature = "azure_policy")]
#[derive(Debug, Clone, Serialize)]
pub struct PolicyPackageNameDefinition {
    pub source_file: String,
    pub package_name: String,
}

#[cfg(feature = "azure_policy")]
#[derive(Debug, Clone, Serialize)]
pub struct PolicyParameter {
    pub name: String,
    pub modifiable: bool,
    pub required: bool,
}

#[cfg(feature = "azure_policy")]
#[derive(Debug, Clone, Serialize)]
pub struct PolicyModifier {
    pub name: String,
}

#[cfg(feature = "azure_policy")]
#[derive(Debug, Clone, Serialize)]
pub struct PolicyParameters {
    pub source_file: String,
    pub parameters: Vec<PolicyParameter>,
    pub modifiers: Vec<PolicyModifier>,
}

/// Create a default engine.
impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    fn effective_execution_timer_config(&self) -> Option<ExecutionTimerConfig> {
        self.execution_timer_config
            .or_else(fallback_execution_timer_config)
    }

    fn apply_effective_execution_timer_config(&mut self) {
        let config = self.effective_execution_timer_config();
        self.interpreter.set_execution_timer_config(config);
    }

    /// Create an instance of [Engine].
    pub fn new() -> Self {
        let mut engine = Self {
            modules: Rc::new(vec![]),
            interpreter: Interpreter::new(),
            prepared: false,
            rego_v1: true,
            execution_timer_config: None,
        };
        engine.apply_effective_execution_timer_config();
        engine
    }

    /// Enable rego v0.
    ///
    /// Note that regorus now defaults to v1.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // Enable v0 for old style policies.
    /// engine.set_rego_v0(true);
    ///
    /// engine.add_policy(
    ///    "test.rego".to_string(),
    ///    r#"
    ///    package test
    ///
    ///    allow { # v0 syntax does not require if keyword
    ///       1 < 2
    ///    }
    ///    "#.to_string())?;
    ///
    /// # Ok(())
    /// # }
    /// ```
    ///
    pub const fn set_rego_v0(&mut self, rego_v0: bool) {
        self.rego_v1 = !rego_v0;
    }

    /// Configure the execution timer.
    ///
    /// Stores the supplied configuration and ensures the next evaluation is checked against those
    /// limits. Engines start without a time limit and otherwise fall back to the global
    /// configuration (if provided).
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroU32;
    /// use std::time::Duration;
    /// use regorus::utils::limits::ExecutionTimerConfig;
    /// use regorus::Engine;
    ///
    /// let mut engine = Engine::new();
    /// let config = ExecutionTimerConfig {
    ///     limit: Duration::from_millis(10),
    ///     check_interval: NonZeroU32::new(1).unwrap(),
    /// };
    ///
    /// engine.set_execution_timer_config(config);
    /// ```
    pub fn set_execution_timer_config(&mut self, config: ExecutionTimerConfig) {
        self.execution_timer_config = Some(config);
        self.interpreter.set_execution_timer_config(Some(config));
    }

    /// Clear the engine-specific execution timer configuration, falling back to the global value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::num::NonZeroU32;
    /// use std::time::Duration;
    /// use regorus::utils::limits::{
    ///     set_fallback_execution_timer_config,
    ///     ExecutionTimerConfig,
    /// };
    /// use regorus::Engine;
    ///
    /// let mut engine = Engine::new();
    /// let global = ExecutionTimerConfig {
    ///     limit: Duration::from_millis(5),
    ///     check_interval: NonZeroU32::new(1).unwrap(),
    /// };
    /// set_fallback_execution_timer_config(Some(global));
    ///
    /// engine.clear_execution_timer_config();
    /// ```
    pub fn clear_execution_timer_config(&mut self) {
        self.execution_timer_config = None;
        self.apply_effective_execution_timer_config();
    }

    /// Add a policy.
    ///
    /// The policy file will be parsed and converted to AST representation.
    /// Multiple policy files may be added to the engine.
    /// Returns the Rego package name declared in the policy.
    ///
    /// * `path`: A filename to be associated with the policy.
    /// * `rego`: The rego policy code.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// let package = engine.add_policy(
    ///    "test.rego".to_string(),
    ///    r#"
    ///    package test
    ///    allow = input.user == "root"
    ///    "#.to_string())?;
    ///
    /// assert_eq!(package, "data.test");
    /// # Ok(())
    /// # }
    /// ```
    ///
    pub fn add_policy(&mut self, path: String, rego: String) -> Result<String> {
        let source = Source::from_contents(path, rego)?;
        let mut parser = self.make_parser(&source)?;
        let module = Ref::new(parser.parse()?);
        limits::enforce_memory_limit().map_err(|err| anyhow!(err))?;
        Rc::make_mut(&mut self.modules).push(module.clone());
        // if policies change, interpreter needs to be prepared again
        self.prepared = false;
        Interpreter::get_path_string(&module.package.refr, Some("data"))
    }

    /// Add a policy from a given file.
    ///
    /// The policy file will be parsed and converted to AST representation.
    /// Multiple policy files may be added to the engine.
    /// Returns the Rego package name declared in the policy.
    ///
    /// * `path`: Path to the policy file (.rego).
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    /// // framework.rego does not conform to v1.
    /// engine.set_rego_v0(true);
    ///
    /// let package = engine.add_policy_from_file("tests/aci/framework.rego")?;
    ///
    /// assert_eq!(package, "data.framework");
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn add_policy_from_file<P: AsRef<std::path::Path>>(&mut self, path: P) -> Result<String> {
        let source = Source::from_file(path)?;
        let mut parser = self.make_parser(&source)?;
        let module = Ref::new(parser.parse()?);
        limits::enforce_memory_limit().map_err(|err| anyhow!(err))?;
        Rc::make_mut(&mut self.modules).push(module.clone());
        // if policies change, interpreter needs to be prepared again
        self.prepared = false;
        Interpreter::get_path_string(&module.package.refr, Some("data"))
    }

    /// Get the list of packages defined by loaded policies.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    /// // framework.rego does not conform to v1.
    /// engine.set_rego_v0(true);
    ///
    /// let _ = engine.add_policy_from_file("tests/aci/framework.rego")?;
    ///
    /// // Package names can be different from file names.
    /// let _ = engine.add_policy("policy.rego".into(), "package hello.world".into())?;
    ///
    /// assert_eq!(engine.get_packages()?, vec!["data.framework", "data.hello.world"]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_packages(&self) -> Result<Vec<String>> {
        self.modules
            .iter()
            .map(|m| Interpreter::get_path_string(&m.package.refr, Some("data")))
            .collect()
    }

    /// Get the list of policy files.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// # let mut engine = Engine::new();
    ///
    /// let pkg = engine.add_policy("hello.rego".to_string(), "package test".to_string())?;
    /// assert_eq!(pkg, "data.test");
    ///
    /// let policies = engine.get_policies()?;
    ///
    /// assert_eq!(policies[0].get_path(), "hello.rego");
    /// assert_eq!(policies[0].get_contents(), "package test");
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_policies(&self) -> Result<Vec<Source>> {
        Ok(self
            .modules
            .iter()
            .map(|m| m.package.refr.span().source.clone())
            .collect())
    }

    /// Get the list of policy files as a JSON object.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// # let mut engine = Engine::new();
    ///
    /// let pkg = engine.add_policy("hello.rego".to_string(), "package test".to_string())?;
    /// assert_eq!(pkg, "data.test");
    ///
    /// let policies = engine.get_policies_as_json()?;
    ///
    /// let v = Value::from_json_str(&policies)?;
    /// assert_eq!(v[0]["path"].as_string()?.as_ref(), "hello.rego");
    /// assert_eq!(v[0]["contents"].as_string()?.as_ref(), "package test");
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_policies_as_json(&self) -> Result<String> {
        #[derive(Serialize)]
        struct Source<'a> {
            path: &'a String,
            contents: &'a String,
        }

        let mut sources = vec![];
        for m in self.modules.iter() {
            let source = &m.package.refr.span().source;
            sources.push(Source {
                path: source.get_path(),
                contents: source.get_contents(),
            });
        }

        serde_json::to_string_pretty(&sources).map_err(anyhow::Error::msg)
    }

    /// Set the input document.
    ///
    /// * `input`: Input documented. Typically this [Value] is constructed from JSON or YAML.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// let input = Value::from_json_str(r#"
    /// {
    ///   "role" : "admin",
    ///   "action": "delete"
    /// }"#)?;
    ///
    /// engine.set_input(input);
    /// # Ok(())
    /// # }
    /// ```
    pub fn set_input(&mut self, input: Value) {
        self.interpreter.set_input(input);
    }

    pub fn set_input_json(&mut self, input_json: &str) -> Result<()> {
        self.set_input(Value::from_json_str(input_json)?);
        Ok(())
    }

    /// Clear the data document.
    ///
    /// The data document will be reset to an empty object.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// engine.clear_data();
    ///
    /// // Evaluate data.
    /// let results = engine.eval_query("data".to_string(), false)?;
    ///
    /// // Assert that it is empty object.
    /// assert_eq!(results.result.len(), 1);
    /// assert_eq!(results.result[0].expressions.len(), 1);
    /// assert_eq!(results.result[0].expressions[0].value, Value::new_object());
    /// # Ok(())
    /// # }
    /// ```
    pub fn clear_data(&mut self) {
        self.interpreter.set_init_data(Value::new_object());
        self.prepared = false;
    }

    /// Add data document.
    ///
    /// The specified data document is merged into existing data document.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // Only objects can be added.
    /// assert!(engine.add_data(Value::from_json_str("[]")?).is_err());
    ///
    /// // Merge { "x" : 1, "y" : {} }
    /// assert!(engine.add_data(Value::from_json_str(r#"{ "x" : 1, "y" : {}}"#)?).is_ok());
    ///
    /// // Merge { "z" : 2 }
    /// assert!(engine.add_data(Value::from_json_str(r#"{ "z" : 2 }"#)?).is_ok());
    ///
    /// // Merge { "z" : 3 }. Conflict error.
    /// assert!(engine.add_data(Value::from_json_str(r#"{ "z" : 3 }"#)?).is_err());
    ///
    /// assert_eq!(
    ///   engine.eval_query("data".to_string(), false)?.result[0].expressions[0].value,
    ///   Value::from_json_str(r#"{ "x": 1, "y": {}, "z": 2}"#)?
    /// );
    /// # Ok(())
    /// # }
    /// ```
    pub fn add_data(&mut self, data: Value) -> Result<()> {
        if data.as_object().is_err() {
            bail!("data must be object");
        }
        self.prepared = false;
        self.interpreter.get_init_data_mut().merge(data)
    }

    /// Get the data document.
    ///
    /// The returned value is the data document that has been constructed using
    /// one or more calls to [`Engine::pre`]. The values of policy rules are
    /// not included in the returned document.
    ///
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // If not set, data document is empty.
    /// assert_eq!(engine.get_data(), Value::new_object());
    ///
    /// // Merge { "x" : 1, "y" : {} }
    /// assert!(engine.add_data(Value::from_json_str(r#"{ "x" : 1, "y" : {}}"#)?).is_ok());
    ///
    /// // Merge { "z" : 2 }
    /// assert!(engine.add_data(Value::from_json_str(r#"{ "z" : 2 }"#)?).is_ok());
    ///
    /// let data = engine.get_data();
    /// assert_eq!(data["x"], Value::from(1));
    /// assert_eq!(data["y"], Value::new_object());
    /// assert_eq!(data["z"], Value::from(2));
    ///
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_data(&self) -> Value {
        self.interpreter.get_init_data().clone()
    }

    pub fn add_data_json(&mut self, data_json: &str) -> Result<()> {
        self.add_data(Value::from_json_str(data_json)?)
    }

    /// Set whether builtins should raise errors strictly or not.
    ///
    /// Regorus differs from OPA in that by default builtins will
    /// raise errors instead of returning Undefined.
    ///
    /// ----
    /// **_NOTE:_** Currently not all builtins honor this flag and will always strictly raise errors.
    /// ----
    pub fn set_strict_builtin_errors(&mut self, b: bool) {
        self.interpreter.set_strict_builtin_errors(b);
    }

    #[doc(hidden)]
    pub fn get_modules(&mut self) -> &Vec<Ref<Module>> {
        &self.modules
    }

    /// Compiles a target-aware policy from the current engine state.
    ///
    /// This method creates a compiled policy that can work with Azure Policy targets,
    /// enabling resource type inference and target-specific evaluation. The compiled
    /// policy will automatically detect and handle `__target__` declarations in the
    /// loaded modules.
    ///
    /// The engine must have been prepared with:
    /// - Policy modules added via [`Engine::add_policy`]
    /// - Data added via [`Engine::add_data`] (optional)
    ///
    /// # Returns
    ///
    /// Returns a [`CompiledPolicy`] that can be used for efficient policy evaluation
    /// with target support, including resource type inference capabilities.
    ///
    /// # Examples
    ///
    /// ## Basic Target-Aware Compilation
    ///
    /// ```no_run
    /// use regorus::*;
    ///
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    /// engine.add_data(Value::from_json_str(r#"{"allowed_sizes": ["small", "medium"]}"#)?)?;
    /// engine.add_policy("policy.rego".to_string(), r#"
    ///     package policy.test
    ///     import rego.v1
    ///     __target__ := "target.tests.sample_test_target"
    ///     
    ///     default allow := false
    ///     allow if {
    ///         input.type == "vm"
    ///         input.size in data.allowed_sizes
    ///     }
    /// "#.to_string())?;
    ///
    /// let compiled = engine.compile_for_target()?;
    /// let result = compiled.eval_with_input(Value::from_json_str(r#"{"type": "vm", "size": "small"}"#)?)?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ## Target Registration and Usage
    ///
    /// ```no_run
    /// use regorus::*;
    /// use regorus::registry::targets;
    /// use regorus::target::Target;
    /// use std::sync::Arc;
    ///
    /// # fn main() -> anyhow::Result<()> {
    /// // Register a target first
    /// let target_json = r#"
    /// {
    ///   "name": "target.example.vm_policy",
    ///   "description": "Simple VM validation target",
    ///   "version": "1.0.0",
    ///   "resource_schema_selector": "type",
    ///   "resource_schemas": [
    ///     {
    ///       "type": "object",
    ///       "properties": {
    ///         "name": { "type": "string" },
    ///         "type": { "const": "vm" },
    ///         "size": { "enum": ["small", "medium", "large"] }
    ///       },
    ///       "required": ["name", "type", "size"]
    ///     }
    ///   ],
    ///   "effects": {
    ///     "allow": { "type": "boolean" },
    ///     "deny": { "type": "boolean" }
    ///   }
    /// }
    /// "#;
    ///
    /// let target = Target::from_json_str(target_json)?;
    /// targets::register(Arc::new(target))?;
    ///
    /// // Use the target in a policy
    /// let mut engine = Engine::new();
    /// engine.add_data(Value::from_json_str(r#"{"allowed_locations": ["us-east"]}"#)?)?;
    /// engine.add_policy("vm_policy.rego".to_string(), r#"
    ///     package vm.validation
    ///     import rego.v1
    ///     __target__ := "target.example.vm_policy"
    ///     
    ///     default allow := false
    ///     allow if {
    ///         input.type == "vm"
    ///         input.size in ["small", "medium"]
    ///     }
    /// "#.to_string())?;
    ///
    /// let compiled = engine.compile_for_target()?;
    /// let result = compiled.eval_with_input(Value::from_json_str(r#"
    /// {
    ///   "name": "test-vm",
    ///   "type": "vm",
    ///   "size": "small"
    /// }"#)?)?;
    /// assert_eq!(result, Value::from(true));
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Notes
    ///
    /// - This method is only available when the `azure_policy` feature is enabled
    /// - Automatically enables print gathering for debugging purposes
    /// - Requires that at least one module contains a `__target__` declaration
    /// - The target referenced must be registered in the target registry
    ///
    /// # See Also
    ///
    /// - [`Engine::compile_with_entrypoint`] for explicit rule-based compilation
    /// - [`crate::compile_policy_for_target`] for a higher-level convenience function
    #[cfg(feature = "azure_policy")]
    #[cfg_attr(docsrs, doc(cfg(feature = "azure_policy")))]
    pub fn compile_for_target(&mut self) -> Result<CompiledPolicy> {
        self.prepare_for_eval(false, true)?;
        self.apply_effective_execution_timer_config();
        self.interpreter.clean_internal_evaluation_state();
        self.interpreter.compile(None).map(CompiledPolicy::new)
    }

    /// Compiles a policy with a specific entry point rule.
    ///
    /// This method creates a compiled policy that evaluates a specific rule as the entry point.
    /// Unlike [`Engine::compile_for_target`], this method requires you to explicitly specify which
    /// rule should be evaluated and does not automatically handle target-specific features.
    ///
    /// The engine must have been prepared with:
    /// - Policy modules added via [`Engine::add_policy`]
    /// - Data added via [`Engine::add_data`] (optional)
    ///
    /// # Arguments
    ///
    /// * `rule` - The specific rule path to evaluate (e.g., "data.policy.allow")
    ///
    /// # Returns
    ///
    /// Returns a [`CompiledPolicy`] that can be used for efficient policy evaluation
    /// focused on the specified entry point rule.
    ///
    /// # Examples
    ///
    /// ## Basic Usage
    ///
    /// ```no_run
    /// use regorus::*;
    /// use std::rc::Rc;
    ///
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    /// engine.add_data(Value::from_json_str(r#"{"allowed_users": ["alice", "bob"]}"#)?)?;
    /// engine.add_policy("authz.rego".to_string(), r#"
    ///     package authz
    ///     import rego.v1
    ///     
    ///     default allow := false
    ///     allow if {
    ///         input.user in data.allowed_users
    ///         input.action == "read"
    ///     }
    ///     
    ///     deny if {
    ///         input.user == "guest"
    ///     }
    /// "#.to_string())?;
    ///
    /// let compiled = engine.compile_with_entrypoint(&"data.authz.allow".into())?;
    /// let result = compiled.eval_with_input(Value::from_json_str(r#"{"user": "alice", "action": "read"}"#)?)?;
    /// assert_eq!(result, Value::from(true));
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// ## Multi-Module Policy
    ///
    /// ```no_run
    /// use regorus::*;
    /// use std::rc::Rc;
    ///
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    /// engine.add_data(Value::from_json_str(r#"{"departments": {"engineering": ["alice"], "hr": ["bob"]}}"#)?)?;
    ///
    /// engine.add_policy("users.rego".to_string(), r#"
    ///     package users
    ///     import rego.v1
    ///     
    ///     user_department(user) := dept if {
    ///         dept := [d | data.departments[d][_] == user][0]
    ///     }
    /// "#.to_string())?;
    ///
    /// engine.add_policy("permissions.rego".to_string(), r#"
    ///     package permissions
    ///     import rego.v1
    ///     import data.users
    ///     
    ///     default allow := false
    ///     allow if {
    ///         users.user_department(input.user) == "engineering"
    ///         input.resource.type == "code"
    ///     }
    ///     
    ///     allow if {
    ///         users.user_department(input.user) == "hr"
    ///         input.resource.type == "personnel_data"
    ///     }
    /// "#.to_string())?;
    ///
    /// let compiled = engine.compile_with_entrypoint(&"data.permissions.allow".into())?;
    ///
    /// // Test engineering access to code
    /// let result = compiled.eval_with_input(Value::from_json_str(r#"
    /// {
    ///   "user": "alice",
    ///   "resource": {"type": "code", "name": "main.rs"}
    /// }"#)?)?;
    /// assert_eq!(result, Value::from(true));
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// # Entry Point Rule Format
    ///
    /// The `rule` parameter should follow the Rego rule path format:
    /// - `"data.package.rule"` - For rules in a specific package
    /// - `"data.package.subpackage.rule"` - For nested packages
    /// - `"allow"` - For rules in the default package (though this is not recommended)
    ///
    /// # Notes
    ///
    /// - Automatically enables print gathering for debugging purposes
    /// - If you need target-aware compilation with automatic `__target__` handling,
    ///   consider using [`Engine::compile_for_target`] instead (requires `azure_policy` feature)
    ///
    /// # See Also
    ///
    /// - [`Engine::compile_for_target`] for target-aware compilation
    /// - [`crate::compile_policy_with_entrypoint`] for a higher-level convenience function
    pub fn compile_with_entrypoint(&mut self, rule: &Rc<str>) -> Result<CompiledPolicy> {
        self.prepare_for_eval(false, false)?;
        self.apply_effective_execution_timer_config();
        self.interpreter.clean_internal_evaluation_state();
        self.interpreter
            .compile(Some(rule.clone()))
            .map(CompiledPolicy::new)
    }

    /// Evaluate specified rule(s).
    ///
    /// [`Engine::eval_rule`] is often faster than [`Engine::eval_query`] and should be preferred if
    /// OPA style [`QueryResults`] are not needed.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // Add policy
    /// engine.add_policy(
    ///   "policy.rego".to_string(),
    ///   r#"
    ///   package example
    ///   import rego.v1
    ///
    ///   x = [1, 2]
    ///
    ///   y := 5 if input.a > 2
    ///   "#.to_string())?;
    ///
    /// // Evaluate rule.
    /// let v = engine.eval_rule("data.example.x".to_string())?;
    /// assert_eq!(v, Value::from(vec![Value::from(1), Value::from(2)]));
    ///
    /// // y evaluates to undefined.
    /// let v = engine.eval_rule("data.example.y".to_string())?;
    /// assert_eq!(v, Value::Undefined);
    ///
    /// // Evaluating a non-existent rule is an error.
    /// let r = engine.eval_rule("data.exaample.x".to_string());
    /// assert!(r.is_err());
    ///
    /// // Path must be valid rule paths.
    /// assert!( engine.eval_rule("data".to_string()).is_err());
    /// assert!( engine.eval_rule("data.example".to_string()).is_err());
    /// # Ok(())
    /// # }
    /// ```
    pub fn eval_rule(&mut self, rule: String) -> Result<Value> {
        self.prepare_for_eval(false, false)?;
        self.apply_effective_execution_timer_config();
        self.interpreter.clean_internal_evaluation_state();
        self.interpreter.eval_rule_in_path(rule)
    }

    /// Evaluate a Rego query.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // Add policies
    /// engine.set_rego_v0(true);
    /// engine.add_policy_from_file("tests/aci/framework.rego")?;
    /// engine.add_policy_from_file("tests/aci/api.rego")?;
    /// engine.add_policy_from_file("tests/aci/policy.rego")?;
    ///
    /// // Add data document (if any).
    /// // If multiple data documents can be added, they will be merged together.
    /// engine.add_data(Value::from_json_file("tests/aci/data.json")?)?;
    ///
    /// // At this point the policies and data have been loaded.
    /// // Either the same engine can be used to make multiple queries or the engine
    /// // can be cloned to avoid having the reload the policies and data.
    /// let _clone = engine.clone();
    ///
    /// // Evaluate a query.
    /// // Load input and make query.
    /// engine.set_input(Value::new_object());
    /// let results = engine.eval_query("data.framework.mount_overlay.allowed".to_string(), false)?;
    /// assert_eq!(results.result[0].expressions[0].value, Value::from(false));
    ///
    /// // Evaluate query with different inputs.
    /// engine.set_input(Value::from_json_file("tests/aci/input.json")?);
    /// let results = engine.eval_query("data.framework.mount_overlay.allowed".to_string(), false)?;
    /// assert_eq!(results.result[0].expressions[0].value, Value::from(true));
    /// # Ok(())
    /// # }
    /// ```
    pub fn eval_query(&mut self, query: String, enable_tracing: bool) -> Result<QueryResults> {
        self.prepare_for_eval(enable_tracing, false)?;
        self.apply_effective_execution_timer_config();
        self.interpreter.clean_internal_evaluation_state();

        self.interpreter.create_rule_prefixes()?;
        let (query_module, query_node, query_schedule) = self.make_query(query)?;
        if query_node.span.text() == "data" {
            self.eval_modules(enable_tracing)?;
        }

        self.interpreter
            .eval_user_query(&query_module, &query_node, query_schedule, enable_tracing)
    }

    /// Evaluate a Rego query that produces a boolean value.
    ///
    ///
    /// This function should be preferred over [`Engine::eval_query`] if just a `true`/`false`
    /// value is desired instead of [`QueryResults`].
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// # let mut engine = Engine::new();
    ///
    /// let enable_tracing = false;
    /// assert_eq!(engine.eval_bool_query("1 > 2".to_string(), enable_tracing)?, false);
    /// assert_eq!(engine.eval_bool_query("1 < 2".to_string(), enable_tracing)?, true);
    ///
    /// // Non boolean queries will raise an error.
    /// assert!(engine.eval_bool_query("1+1".to_string(), enable_tracing).is_err());
    ///
    /// // Queries producing multiple values will raise an error.
    /// assert!(engine.eval_bool_query("true; true".to_string(), enable_tracing).is_err());
    ///
    /// // Queries producing no values will raise an error.
    /// assert!(engine.eval_bool_query("true; false; true".to_string(), enable_tracing).is_err());
    /// # Ok(())
    /// # }
    /// ```
    pub fn eval_bool_query(&mut self, query: String, enable_tracing: bool) -> Result<bool> {
        let results = self.eval_query(query, enable_tracing)?;
        let entries = results.result.as_slice();
        let entry = entries
            .first()
            .ok_or_else(|| anyhow!("query did not produce any values"))?;
        if entries.len() > 1 {
            bail!("query produced more than one value");
        }

        let expressions = entry.expressions.as_slice();
        let expr = expressions
            .first()
            .ok_or_else(|| anyhow!("query result missing expression"))?;
        if expressions.len() > 1 {
            bail!("query produced more than one value");
        }

        expr.value.as_bool().copied()
    }

    /// Evaluate an `allow` query.
    ///
    /// This is a wrapper over [`Engine::eval_bool_query`] that returns true only if the
    /// boolean query succeed and produced a `true` value.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// # let mut engine = Engine::new();
    ///
    /// let enable_tracing = false;
    /// assert_eq!(engine.eval_allow_query("1 > 2".to_string(), enable_tracing), false);
    /// assert_eq!(engine.eval_allow_query("1 < 2".to_string(), enable_tracing), true);
    /// assert_eq!(engine.eval_allow_query("1+1".to_string(), enable_tracing), false);
    /// assert_eq!(engine.eval_allow_query("true; true".to_string(), enable_tracing), false);
    /// assert_eq!(engine.eval_allow_query("true; false; true".to_string(), enable_tracing), false);
    /// # Ok(())
    /// # }
    /// ```
    pub fn eval_allow_query(&mut self, query: String, enable_tracing: bool) -> bool {
        matches!(self.eval_bool_query(query, enable_tracing), Ok(true))
    }

    /// Evaluate a `deny` query.
    ///
    /// This is a wrapper over [`Engine::eval_bool_query`] that returns false only if the
    /// boolean query succeed and produced a `false` value.
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// # let mut engine = Engine::new();
    ///
    /// let enable_tracing = false;
    /// assert_eq!(engine.eval_deny_query("1 > 2".to_string(), enable_tracing), false);
    /// assert_eq!(engine.eval_deny_query("1 < 2".to_string(), enable_tracing), true);
    ///
    /// assert_eq!(engine.eval_deny_query("1+1".to_string(), enable_tracing), true);
    /// assert_eq!(engine.eval_deny_query("true; true".to_string(), enable_tracing), true);
    /// assert_eq!(engine.eval_deny_query("true; false; true".to_string(), enable_tracing), true);
    /// # Ok(())
    /// # }
    /// ```
    pub fn eval_deny_query(&mut self, query: String, enable_tracing: bool) -> bool {
        !matches!(self.eval_bool_query(query, enable_tracing), Ok(false))
    }

    fn make_query(&mut self, query: String) -> Result<(NodeRef<Module>, NodeRef<Query>, Schedule)> {
        let mut query_module = {
            let source = Source::from_contents(
                "<query_module.rego>".to_owned(),
                "package __internal_query_module".to_owned(),
            )?;
            Parser::new(&source)?.parse()?
        };

        // Parse the query.
        let query_source = Source::from_contents("<query.rego>".to_string(), query)?;
        let mut parser = self.make_parser(&query_source)?;
        let query_node = parser.parse_user_query()?;
        query_module.num_expressions = parser.num_expressions();
        query_module.num_queries = parser.num_queries();
        query_module.num_statements = parser.num_statements();
        let query_schedule = Analyzer::new().analyze_query_snippet(&self.modules, &query_node)?;

        // Populate loop hoisting for the query snippet
        // Query snippets are treated as if they're in a module appended at the end (same as analyzer)
        // The loop hoisting table already has capacity for this (ensured in prepare_for_eval)
        let module_idx = u32::try_from(self.modules.len())
            .map_err(|_| anyhow!("module count exceeds u32::MAX"))?;

        use crate::compiler::hoist::LoopHoister;

        let query_schedule_rc = Rc::new(query_schedule.clone());

        // Run loop hoisting for query snippet
        let mut hoister = LoopHoister::new_with_schedule(query_schedule_rc.clone());
        hoister.populate_query_snippet(
            module_idx,
            &query_node,
            query_module.num_statements,
            query_module.num_expressions,
        )?;
        let query_lookup = hoister.finalize();

        #[cfg(debug_assertions)]
        {
            for stmt in &query_node.stmts {
                debug_assert!(
                    query_lookup
                        .get_statement_loops(module_idx, stmt.sidx)
                        .ok()
                        .and_then(|entry| entry)
                        .is_some(),
                    "missing hoisted loop entry for query statement index {}",
                    stmt.sidx
                );
            }
        }

        // Get the existing table, merge in the query loops, and set it back
        let mut existing_table = self.interpreter.take_loop_hoisting_table();
        existing_table.truncate_modules(self.modules.len());
        #[cfg(debug_assertions)]
        {
            debug_assert!(
                existing_table.module_len() <= self.modules.len(),
                "loop hoisting table should not retain extra modules before merge"
            );
        }
        existing_table.merge_query_loops(query_lookup, self.modules.len());
        #[cfg(debug_assertions)]
        {
            for stmt in &query_node.stmts {
                debug_assert!(
                    existing_table
                        .get_statement_loops(module_idx, stmt.sidx)
                        .ok()
                        .and_then(|entry| entry)
                        .is_some(),
                    "missing hoisted loop entry after merge for module {} stmt {}",
                    module_idx,
                    stmt.sidx
                );
            }
        }
        self.interpreter.set_loop_hoisting_table(existing_table);

        Ok((Ref::new(query_module), query_node, query_schedule))
    }

    #[doc(hidden)]
    /// Evaluate the given query and all the rules in the supplied policies.
    ///
    /// This is mainly used for testing Regorus itself.
    pub fn eval_query_and_all_rules(
        &mut self,
        query: String,
        enable_tracing: bool,
    ) -> Result<QueryResults> {
        self.eval_modules(enable_tracing)?;
        // Restart the timer window for the user query after module evaluation.
        self.apply_effective_execution_timer_config();

        let (query_module, query_node, query_schedule) = self.make_query(query)?;
        self.interpreter
            .eval_user_query(&query_module, &query_node, query_schedule, enable_tracing)
    }

    #[doc(hidden)]
    fn prepare_for_eval(&mut self, enable_tracing: bool, for_target: bool) -> Result<()> {
        // Fail fast if the engine already exceeds the global memory limit before evaluation work.
        limits::enforce_memory_limit().map_err(|err| anyhow!(err))?;

        self.interpreter.set_traces(enable_tracing);

        // if the data/policies have changed or the interpreter has never been prepared
        if !self.prepared {
            // Analyze the modules and determine how statements must be scheduled.
            let analyzer = Analyzer::new();
            let schedule = Rc::new(analyzer.analyze(&self.modules)?);

            self.interpreter.set_modules(self.modules.clone());

            self.interpreter.clear_builtins_cache();
            // clean_internal_evaluation_state will set data to an efficient clont of use supplied init_data
            // Initialize the with-document with initial data values.
            // with-modifiers will be applied to this document.
            self.interpreter.init_with_document()?;

            self.interpreter
                .set_functions(gather_functions(&self.modules)?);
            self.interpreter.gather_rules()?;
            self.interpreter.process_imports()?;

            // Populate loop hoisting table for efficient evaluation
            // Reserve capacity for 1 extra module (for query modules)
            use crate::compiler::hoist::LoopHoister;

            // Run loop hoisting pass first
            let hoister = LoopHoister::new_with_schedule(schedule.clone());
            let loop_lookup = hoister.populate_with_extra_capacity(&self.modules, 0)?;

            self.interpreter.set_loop_hoisting_table(loop_lookup);

            // Set schedule after hoisting completes
            self.interpreter.set_schedule(Some(schedule));

            #[cfg(feature = "azure_policy")]
            if for_target {
                // Resolve and validate target specifications across all modules
                crate::interpreter::target::resolve::resolve_and_apply_target(
                    &mut self.interpreter,
                )?;
                // Infer resource types
                crate::interpreter::target::infer::infer_resource_type(&mut self.interpreter)?;
            }

            if !for_target {
                // Check if any module specifies a target and warn if so
                #[cfg(feature = "azure_policy")]
                self.warn_if_targets_present();
            }

            self.prepared = true;
        }

        Ok(())
    }

    #[doc(hidden)]
    pub fn eval_rule_in_module(
        &mut self,
        module: &Ref<Module>,
        rule: &Ref<Rule>,
        enable_tracing: bool,
    ) -> Result<Value> {
        self.prepare_for_eval(enable_tracing, false)?;
        self.apply_effective_execution_timer_config();
        self.interpreter.clean_internal_evaluation_state();

        self.interpreter.eval_rule(module, rule)?;

        Ok(self.interpreter.get_data_mut().clone())
    }

    #[doc(hidden)]
    pub fn eval_modules(&mut self, enable_tracing: bool) -> Result<Value> {
        self.prepare_for_eval(enable_tracing, false)?;
        self.apply_effective_execution_timer_config();
        self.interpreter.clean_internal_evaluation_state();

        // Ensure that empty modules are created.
        for m in self.modules.iter().filter(|m| m.policy.is_empty()) {
            let path = Parser::get_path_ref_components(&m.package.refr)?;
            let path: Vec<&str> = path.iter().map(|s| s.text()).collect();
            let vref =
                Interpreter::make_or_get_value_mut(self.interpreter.get_data_mut(), &path[..])?;
            if *vref == Value::Undefined {
                *vref = Value::new_object();
            }
        }

        self.interpreter.check_default_rules()?;
        for module in self.modules.clone().iter() {
            for rule in &module.policy {
                self.interpreter.eval_rule(module, rule)?;
            }
        }
        // Defer the evaluation of the default rules to here
        for module in self.modules.clone().iter() {
            let prev_module = self.interpreter.set_current_module(Some(module.clone()))?;
            for rule in &module.policy {
                self.interpreter.eval_default_rule(rule)?;
            }
            self.interpreter.set_current_module(prev_module)?;
        }

        // Ensure that all modules are created.
        for m in self.modules.iter() {
            let path = Parser::get_path_ref_components(&m.package.refr)?;
            let path: Vec<&str> = path.iter().map(|s| s.text()).collect();
            let vref =
                Interpreter::make_or_get_value_mut(self.interpreter.get_data_mut(), &path[..])?;
            if *vref == Value::Undefined {
                *vref = Value::new_object();
            }
        }
        self.interpreter.create_rule_prefixes()?;
        Ok(self.interpreter.get_data_mut().clone())
    }

    /// Add a custom builtin (extension).
    ///
    /// * `path`: The fully qualified path of the builtin.
    /// * `nargs`: The number of arguments the builtin takes.
    /// * `extension`: The [`Extension`] instance.
    ///
    /// ```rust
    /// # use regorus::*;
    /// # use anyhow::{bail, Result};
    /// # fn main() -> Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // Policy uses `do_magic` custom builtin.
    /// engine.add_policy(
    ///    "test.rego".to_string(),
    ///    r#"package test
    ///       x = do_magic(1)
    ///    "#.to_string(),
    /// )?;
    ///
    /// // Evaluating fails since `do_magic` is not defined.
    /// assert!(engine.eval_query("data.test.x".to_string(), false).is_err());
    ///
    /// // Add extension to implement `do_magic`. The extension can be stateful.
    /// let mut magic = 8;
    /// engine.add_extension("do_magic".to_string(), 1 , Box::new(move | mut params: Vec<Value> | {
    ///   // params is mut and therefore individual values can be removed from it and modified.
    ///   // The number of parameters (1) has already been validated.
    ///
    ///   match &params[0].as_i64() {
    ///      Ok(i) => {
    ///         // Compute value
    ///         let v = *i + magic;
    ///         // Update extension state.
    ///         magic += 1;
    ///         Ok(Value::from(v))
    ///      }
    ///      // Extensions can raise errors. Regorus will add location information to
    ///      // the error.
    ///      _ => bail!("do_magic expects i64 value")
    ///   }
    /// }))?;
    ///
    /// // Evaluation will now succeed.
    /// let r = engine.eval_query("data.test.x".to_string(), false)?;
    /// assert_eq!(r.result[0].expressions[0].value.as_i64()?, 9);
    ///
    /// // Cloning the engine will also clone the extension.
    /// let mut engine1 = engine.clone();
    ///
    /// // Evaluating again will return a different value since the extension is stateful.
    /// let r = engine.eval_query("data.test.x".to_string(), false)?;
    /// assert_eq!(r.result[0].expressions[0].value.as_i64()?, 10);
    ///
    /// // The second engine has a clone of the extension.
    /// let r = engine1.eval_query("data.test.x".to_string(), false)?;
    /// assert_eq!(r.result[0].expressions[0].value.as_i64()?, 10);
    ///
    /// // Once added, the extension cannot be replaced or removed.
    /// assert!(engine.add_extension("do_magic".to_string(), 1, Box::new(|_:Vec<Value>| {
    ///   Ok(Value::Undefined)
    /// })).is_err());
    ///
    /// // Extensions don't support out-parameter syntax.
    /// engine.add_policy(
    ///   "policy.rego".to_string(),
    ///   r#"package invalid
    ///      x = y if {
    ///       # y = do_magic(2)
    ///       do_magic(2, y)  # y is supplied as an out parameter.
    ///     }
    ///    "#.to_string()
    /// )?;
    ///
    /// // Evaluation fails since rule x calls an extension with out parameter.
    /// assert!(engine.eval_query("data.invalid.x".to_string(), false).is_err());
    /// # Ok(())
    /// # }
    /// ```
    pub fn add_extension(
        &mut self,
        path: String,
        nargs: u8,
        extension: Box<dyn Extension>,
    ) -> Result<()> {
        self.interpreter.add_extension(path, nargs, extension)
    }

    #[cfg(feature = "coverage")]
    #[cfg_attr(docsrs, doc(cfg(feature = "coverage")))]
    /// Get the coverage report.
    ///
    /// ```rust
    /// # use regorus::*;
    /// # use anyhow::{bail, Result};
    /// # fn main() -> Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// engine.add_policy(
    ///    "policy.rego".to_string(),
    ///    r#"
    /// package test    # Line 2
    ///
    /// x = y if {         # Line 4
    ///   input.a > 2   # Line 5
    ///   y = 5         # Line 6
    /// }
    ///    "#.to_string()
    /// )?;
    ///
    /// // Enable coverage.
    /// engine.set_enable_coverage(true);
    ///
    /// engine.eval_query("data".to_string(), false)?;
    ///
    /// let report = engine.get_coverage_report()?;
    /// assert_eq!(report.files[0].path, "policy.rego");
    ///
    /// // Only line 5 is evaluated.
    /// assert_eq!(report.files[0].covered.iter().cloned().collect::<Vec<u32>>(), vec![5]);
    ///
    /// // Line 4 and 6 are not evaluated.
    /// assert_eq!(report.files[0].not_covered.iter().cloned().collect::<Vec<u32>>(), vec![4, 6]);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// See also [`crate::coverage::Report::to_colored_string`].
    pub fn get_coverage_report(&self) -> Result<crate::coverage::Report> {
        self.interpreter.get_coverage_report()
    }

    #[cfg(feature = "coverage")]
    #[cfg_attr(docsrs, doc(cfg(feature = "coverage")))]
    /// Enable/disable policy coverage.
    ///
    /// If `enable` is different from the current value, then any existing coverage
    /// information will be cleared.
    pub fn set_enable_coverage(&mut self, enable: bool) {
        self.interpreter.set_enable_coverage(enable);
    }

    #[cfg(feature = "coverage")]
    #[cfg_attr(docsrs, doc(cfg(feature = "coverage")))]
    /// Clear the gathered policy coverage data.
    pub fn clear_coverage_data(&mut self) {
        self.interpreter.clear_coverage_data();
    }

    /// Gather output from print statements instead of emiting to stderr.
    ///
    /// See [`Engine::take_prints`].
    pub fn set_gather_prints(&mut self, b: bool) {
        self.interpreter.set_gather_prints(b);
    }

    /// Take the gathered output of print statements.
    ///
    /// ```rust
    /// # use regorus::*;
    /// # use anyhow::{bail, Result};
    /// # fn main() -> Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // Print to stderr.
    /// engine.eval_query("print(\"Hello\")".to_string(), false)?;
    ///
    /// // Configure gathering print statements.
    /// engine.set_gather_prints(true);
    ///
    /// // Execute query.
    /// engine.eval_query("print(\"Hello\")".to_string(), false)?;
    ///
    /// // Take and clear prints.
    /// let prints = engine.take_prints()?;
    /// assert_eq!(prints.len(), 1);
    /// assert!(prints[0].contains("Hello"));
    ///
    /// for p in prints {
    ///   println!("{p}");
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn take_prints(&mut self) -> Result<Vec<String>> {
        self.interpreter.take_prints()
    }

    /// Get the policies and corresponding AST.
    ///
    ///
    /// ```rust
    /// # use regorus::*;
    /// # use anyhow::{bail, Result};
    /// # fn main() -> Result<()> {
    /// # let mut engine = Engine::new();
    /// engine.add_policy("test.rego".to_string(), "package test\n x := 1".to_string())?;
    ///
    /// let ast = engine.get_ast_as_json()?;
    /// let value = Value::from_json_str(&ast)?;
    ///
    /// assert_eq!(value[0]["ast"]["package"]["refr"]["Var"][1].as_string()?.as_ref(), "test");
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(feature = "ast")]
    #[cfg_attr(docsrs, doc(cfg(feature = "ast")))]
    pub fn get_ast_as_json(&self) -> Result<String> {
        #[derive(Serialize)]
        struct Policy<'a> {
            source: &'a Source,
            version: u32,
            ast: &'a Module,
        }
        let mut ast = vec![];
        for m in self.modules.iter() {
            ast.push(Policy {
                source: &m.package.span.source,
                version: 1,
                ast: m,
            });
        }

        serde_json::to_string_pretty(&ast).map_err(anyhow::Error::msg)
    }

    /// Get the package names of each policy added to the engine.
    ///
    ///
    /// ```rust
    /// # use regorus::*;
    /// # use anyhow::{bail, Result};
    /// # fn main() -> Result<()> {
    /// # let mut engine = Engine::new();
    /// engine.add_policy("test.rego".to_string(), "package test\n x := 1".to_string())?;
    /// engine.add_policy("test2.rego".to_string(), "package test.multi.segment\n x := 1".to_string())?;
    ///
    /// let package_names = engine.get_policy_package_names()?;
    ///
    /// assert_eq!("test", package_names[0].package_name);
    /// assert_eq!("test.multi.segment", package_names[1].package_name);
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(feature = "azure_policy")]
    #[cfg_attr(docsrs, doc(cfg(feature = "azure_policy")))]
    pub fn get_policy_package_names(&self) -> Result<Vec<PolicyPackageNameDefinition>> {
        let mut package_names = vec![];
        for m in self.modules.iter() {
            let package_name = Interpreter::get_path_string(&m.package.refr, None)?;
            package_names.push(PolicyPackageNameDefinition {
                source_file: m.package.span.source.file().to_string(),
                package_name,
            });
        }

        Ok(package_names)
    }

    /// Get the parameters defined in each policy.
    ///
    ///
    /// ```rust
    /// # use regorus::*;
    /// # use anyhow::{bail, Result};
    /// # fn main() -> Result<()> {
    /// # let mut engine = Engine::new();
    /// engine.add_policy("test.rego".to_string(), "package test default parameters.a = 5 parameters.b = 10\n x := 1".to_string())?;
    ///
    /// let parameters = engine.get_policy_parameters()?;
    ///
    /// assert_eq!("a", parameters[0].parameters[0].name);
    /// assert_eq!("b", parameters[0].modifiers[0].name);
    ///
    /// # Ok(())
    /// # }
    /// ```
    #[cfg(feature = "azure_policy")]
    #[cfg_attr(docsrs, doc(cfg(feature = "azure_policy")))]
    pub fn get_policy_parameters(&self) -> Result<Vec<PolicyParameters>> {
        let mut policy_parameter_definitions = vec![];
        for m in self.modules.iter() {
            let mut parameters = vec![];
            let mut modifiers = vec![];

            for rule in &m.policy {
                match *rule.as_ref() {
                    // Extract parameter definitions from the policy rule
                    // e.g. default parameters.a = 5
                    Rule::Default { ref refr, .. } => {
                        let path = Parser::get_path_ref_components(refr)?;
                        let paths: Vec<&str> = path.iter().map(|s| s.text()).collect();

                        if paths.len() == 2 && paths.first().is_some_and(|p| *p == "parameters") {
                            if let Some(name) = paths.get(1) {
                                // Todo: Fetch fields other than name from rego metadoc for the parameter
                                parameters.push(PolicyParameter {
                                    name: (*name).to_string(),
                                    modifiable: false,
                                    required: false,
                                });
                            }
                        }
                    }
                    // Extract modifiers to the parameters from the policy rule
                    // e.g. parameters.a = 5
                    Rule::Spec { ref head, .. } => {
                        match *head {
                            RuleHead::Compr { ref refr, .. } => {
                                let path = Parser::get_path_ref_components(refr)?;
                                let paths: Vec<&str> = path.iter().map(|s| s.text()).collect();

                                if paths.len() == 2
                                    && paths.first().is_some_and(|p| *p == "parameters")
                                {
                                    if let Some(name) = paths.get(1) {
                                        // Todo: Fetch fields other than name from rego metadoc for the parameter
                                        modifiers.push(PolicyModifier {
                                            name: (*name).to_string(),
                                        });
                                    }
                                }
                            }
                            RuleHead::Func { .. } => {}
                            RuleHead::Set { .. } => {}
                        }
                    }
                }
            }

            policy_parameter_definitions.push(PolicyParameters {
                source_file: m.package.span.source.file().to_string(),
                parameters,
                modifiers,
            });
        }

        Ok(policy_parameter_definitions)
    }

    /// Emit a warning if any modules contain target specifications but we're not using target-aware compilation.
    #[cfg(feature = "azure_policy")]
    fn warn_if_targets_present(&self) {
        let mut has_target = false;
        let mut target_files = Vec::new();

        for module in self.modules.iter() {
            if module.target.is_some() {
                has_target = true;
                target_files.push(module.package.span.source.get_path());
            }
        }

        if has_target {
            std::eprintln!("Warning: Target specifications found in policy modules but not using target-aware compilation.");
            std::eprintln!("         The following files contain __target__ declarations:");
            for file in target_files {
                std::eprintln!("         - {}", file);
            }
            std::eprintln!("         Consider using compile_for_target() instead of compile_with_entrypoint() for target-aware evaluation.");
        }
    }

    fn make_parser<'a>(&self, source: &'a Source) -> Result<Parser<'a>> {
        let mut parser = Parser::new(source)?;
        if self.rego_v1 {
            parser.enable_rego_v1()?;
        }
        Ok(parser)
    }

    /// Create a new Engine from a compiled policy.
    #[doc(hidden)]
    pub(crate) fn new_from_compiled_policy(
        compiled_policy: Rc<crate::compiled_policy::CompiledPolicyData>,
    ) -> Self {
        let modules = compiled_policy.modules.clone();
        let mut engine = Self {
            modules,
            interpreter: Interpreter::new_from_compiled_policy(compiled_policy),
            rego_v1: true, // Value doesn't matter since this is used only for policy parsing
            prepared: true,
            execution_timer_config: None,
        };
        engine.apply_effective_execution_timer_config();
        engine
    }
}
