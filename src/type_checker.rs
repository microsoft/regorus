// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! High-level type checker for Regorus policies.
//!
//! This module provides a convenient API for running type analysis on Rego policies
//! and querying the results. It's designed to be used both standalone and integrated
//! with the Engine.

use crate::ast::{Module, Ref};
use crate::compiler::hoist::HoistedLoopsLookup;
use crate::schema::Schema;
use crate::type_analysis::{TypeAnalysisOptions, TypeAnalysisResult, TypeAnalyzer};
use crate::value::Value;
use crate::Rc;

use alloc::string::String;
use alloc::vec::Vec;
use anyhow::Result;

/// High-level type checker for Rego policies.
///
/// The TypeChecker provides a convenient interface for performing type analysis
/// on Rego policies. It handles the necessary preparation steps (like loop hoisting)
/// automatically and caches results for efficiency.
///
/// # Example
///
/// ```no_run
/// # use regorus::*;
/// # fn main() -> anyhow::Result<()> {
/// let mut engine = Engine::new();
/// engine.add_policy(
///     "policy.rego".to_string(),
///     r#"
///     package example
///     allow = input.user == "admin"
///     "#.to_string()
/// )?;
///
/// let modules = engine.get_modules();
/// let modules = Rc::new(modules.clone());
/// let mut type_checker = TypeChecker::new(modules);
///
/// // Optionally set input schema
/// #[cfg(feature = "jsonschema")]
/// {
///     let input_schema = Schema::from_json_str(
///         r#"{"type": "object", "properties": {"user": {"type": "string"}}}"#
///     ).map_err(|e| anyhow::anyhow!("{e}"))?;
///     type_checker.set_input_schema(input_schema);
/// }
///
/// // Run type analysis
/// type_checker.check()?;
///
/// // Query results
/// if let Some(result) = type_checker.get_result() {
///     println!("Found {} diagnostics", result.diagnostics.len());
/// }
/// # Ok(())
/// # }
/// ```
#[derive(Debug, Clone)]
pub struct TypeChecker {
    modules: Rc<Vec<Ref<Module>>>,
    input_schema: Option<Schema>,
    data_schema: Option<Schema>,
    loop_lookup: Option<Rc<HoistedLoopsLookup>>,
    entrypoints: Option<Vec<String>>,
    result: Option<TypeAnalysisResult>,
}

impl TypeChecker {
    /// Create a new TypeChecker for the given modules.
    ///
    /// # Arguments
    ///
    /// * `modules` - The parsed Rego policy modules to analyze
    pub fn new(modules: Rc<Vec<Ref<Module>>>) -> Self {
        Self {
            modules,
            input_schema: None,
            data_schema: None,
            loop_lookup: None,
            entrypoints: None,
            result: None,
        }
    }

    /// Set the input schema for type analysis.
    ///
    /// The input schema is used to provide more precise type information
    /// for expressions that reference the `input` document.
    ///
    /// # Arguments
    ///
    /// * `schema` - JSON Schema describing the structure of the input document
    pub fn set_input_schema(&mut self, schema: Schema) {
        self.input_schema = Some(schema);
        // Invalidate cached result since schema changed
        self.result = None;
    }

    /// Set the data schema for type analysis.
    ///
    /// The data schema is used to provide more precise type information
    /// for expressions that reference the `data` document.
    ///
    /// # Arguments
    ///
    /// * `schema` - JSON Schema describing the structure of the data document
    pub fn set_data_schema(&mut self, schema: Schema) {
        self.data_schema = Some(schema);
        // Invalidate cached result since schema changed
        self.result = None;
    }

    /// Get the input schema if one has been set.
    pub fn get_input_schema(&self) -> Option<&Schema> {
        self.input_schema.as_ref()
    }

    /// Get the data schema if one has been set.
    pub fn get_data_schema(&self) -> Option<&Schema> {
        self.data_schema.as_ref()
    }

    /// Set entrypoints for filtered type analysis.
    ///
    /// When entrypoints are set, type analysis will only process rules
    /// reachable from the specified paths.
    ///
    /// # Arguments
    ///
    /// * `entrypoints` - List of rule paths (e.g., "data.package.rule")
    pub fn set_entrypoints(&mut self, entrypoints: Vec<String>) {
        self.entrypoints = Some(entrypoints);
        // Invalidate cached result since entrypoints changed
        self.result = None;
    }

    /// Get the entrypoints if any have been set.
    pub fn get_entrypoints(&self) -> Option<&[String]> {
        self.entrypoints.as_deref()
    }

    /// Run type checking/analysis on the policies.
    ///
    /// This method performs the following steps:
    /// 1. Runs loop hoisting if not already done (to extract output expressions)
    /// 2. Runs type analysis with the configured schemas
    /// 3. Caches the results for subsequent queries
    ///
    /// Returns an error if hoisting or type analysis fails.
    pub fn check(&mut self) -> Result<()> {
        // Run hoister if not already done
        if self.loop_lookup.is_none() {
            let hoister = crate::compiler::hoist::LoopHoister::new();
            let lookup = hoister.populate(&self.modules)?;
            self.loop_lookup = Some(Rc::new(lookup));
        }

        // Prepare type analysis options
        let options = TypeAnalysisOptions {
            input_schema: self.input_schema.clone(),
            data_schema: self.data_schema.clone(),
            loop_lookup: self.loop_lookup.clone(),
            entrypoints: self.entrypoints.clone(),
            disable_function_generic_pass: true,
        };

        // Run type analysis
        let analyzer = TypeAnalyzer::new(&self.modules, None, options);
        let result = analyzer.analyze_modules();

        // Cache the result
        self.result = Some(result);

        Ok(())
    }

    /// Get the type analysis result.
    ///
    /// Returns `None` if type checking hasn't been run yet via [`check()`](Self::check).
    pub fn get_result(&self) -> Option<&TypeAnalysisResult> {
        self.result.as_ref()
    }

    /// Get the hoisted loops lookup.
    ///
    /// This is useful for advanced use cases that need to access the
    /// output expressions and scope contexts from the hoister.
    ///
    /// Returns `None` if type checking hasn't been run yet.
    pub fn get_loop_lookup(&self) -> Option<&Rc<HoistedLoopsLookup>> {
        self.loop_lookup.as_ref()
    }

    /// Check if there are any type errors in the analysis result.
    ///
    /// Returns `None` if type checking hasn't been run yet.
    pub fn has_errors(&self) -> Option<bool> {
        self.result.as_ref().map(|r| !r.diagnostics.is_empty())
    }

    /// Get the number of diagnostics found.
    ///
    /// Returns `None` if type checking hasn't been run yet.
    pub fn diagnostic_count(&self) -> Option<usize> {
        self.result.as_ref().map(|r| r.diagnostics.len())
    }

    /// Get the type of a specific rule by its path.
    ///
    /// # Arguments
    ///
    /// * `module_idx` - The index of the module containing the rule
    /// * `rule_name` - The name of the rule (e.g., "allow", "violation")
    ///
    /// Returns the type descriptor for the rule if found and type checking has been run.
    pub fn get_rule_type(
        &self,
        _module_idx: usize,
        _rule_name: &str,
    ) -> Option<&crate::type_analysis::TypeDescriptor> {
        // This is a simplified implementation - a full implementation would
        // need to look up the rule by name in the module and get its type from the result
        self.result.as_ref()?;
        // TODO: Implement rule name lookup
        None
    }

    /// Get a constant value for a rule if it was determined to be constant.
    ///
    /// # Arguments
    ///
    /// * `module_idx` - The index of the module containing the rule
    /// * `rule_idx` - The index of the rule within the module
    ///
    /// Returns the constant value if the rule is constant and type checking has been run.
    pub fn get_rule_constant(&self, module_idx: usize, rule_idx: usize) -> Option<&Value> {
        let result = self.result.as_ref()?;
        // Note: For now we return None since RuleTable is not yet populated.
        // Once RuleTable is fully implemented, this will use:
        // let module_summary = result.rules.modules.get(module_idx)?;
        // let rule_path = module_summary.rule_paths.get(rule_idx)?;
        // let rule_summary = result.rules.by_path.get(rule_path)?;
        // match &rule_summary.constant_state { ... }
        let _ = (result, module_idx, rule_idx);
        None
    }

    /// Clear all cached results and force re-analysis on next check.
    pub fn invalidate(&mut self) {
        self.result = None;
        self.loop_lookup = None;
    }

    /// Update the modules being analyzed.
    ///
    /// This invalidates all cached results.
    pub fn set_modules(&mut self, modules: Rc<Vec<Ref<Module>>>) {
        self.modules = modules;
        self.invalidate();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    #[test]
    fn test_type_checker_basic() -> Result<()> {
        let mut engine = Engine::new();
        engine.add_policy(
            "test.rego".to_string(),
            r#"
            package test
            allow = true
            "#
            .to_string(),
        )?;

        let modules = Rc::new(engine.get_modules().clone());
        let mut checker = TypeChecker::new(modules);

        checker.check()?;

        assert!(checker.get_result().is_some());
        assert_eq!(checker.has_errors(), Some(false));
        assert_eq!(checker.diagnostic_count(), Some(0));

        Ok(())
    }

    #[cfg(feature = "jsonschema")]
    #[test]
    fn test_type_checker_with_schema() -> Result<()> {
        let mut engine = Engine::new();
        engine.add_policy(
            "test.rego".to_string(),
            r#"
            package test
            allow = input.value > 10
            "#
            .to_string(),
        )?;

        let modules = Rc::new(engine.get_modules().clone());
        let mut checker = TypeChecker::new(modules);

        let schema = Schema::from_json_str(
            r#"{"type": "object", "properties": {"value": {"type": "integer"}}}"#,
        )
        .map_err(|e| anyhow::anyhow!("{}", e))?;
        checker.set_input_schema(schema);

        checker.check()?;

        assert!(checker.get_result().is_some());

        Ok(())
    }

    #[cfg(feature = "jsonschema")]
    #[test]
    fn test_type_checker_invalidation() -> Result<()> {
        let mut engine = Engine::new();
        engine.add_policy(
            "test.rego".to_string(),
            r#"
            package test
            x = 1
            "#
            .to_string(),
        )?;

        let modules = Rc::new(engine.get_modules().clone());
        let mut checker = TypeChecker::new(modules);

        checker.check()?;
        assert!(checker.get_result().is_some());

        // Setting schema should invalidate
        let schema =
            Schema::from_json_str(r#"{"type": "object"}"#).map_err(|e| anyhow::anyhow!("{}", e))?;
        checker.set_input_schema(schema);
        assert!(checker.get_result().is_none());

        // Check again to rebuild cache
        checker.check()?;
        assert!(checker.get_result().is_some());

        Ok(())
    }
}
