// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::interpreter::*;
use crate::lexer::*;
use crate::parser::*;
use crate::scheduler::*;
use crate::utils::gather_functions;
use crate::value::*;
use crate::{Extension, QueryResults};

use std::convert::AsRef;
use std::path::Path;

use anyhow::{bail, Result};

/// The Rego evaluation engine.
///
#[derive(Debug, Clone)]
pub struct Engine {
    modules: Vec<Ref<Module>>,
    interpreter: Interpreter,
    prepared: bool,
}

/// Create a default engine.
impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    /// Create an instance of [Engine].
    pub fn new() -> Self {
        Self {
            modules: vec![],
            interpreter: Interpreter::new(),
            prepared: false,
        }
    }

    /// Add a policy.
    ///
    /// The policy file will be parsed and converted to AST representation.
    /// Multiple policy files may be added to the engine.
    ///
    /// * `path`: A filename to be associated with the policy.
    /// * `rego`: The rego policy code.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// engine.add_policy(
    ///    "test.rego".to_string(),
    ///    r#"
    ///    package test
    ///    allow = input.user == "root"
    ///    "#.to_string())?;
    /// # Ok(())
    /// # }
    /// ```
    ///
    pub fn add_policy(&mut self, path: String, rego: String) -> Result<()> {
        let source = Source::new(path, rego);
        let mut parser = Parser::new(&source)?;
        self.modules.push(Ref::new(parser.parse()?));
        // if policies change, interpreter needs to be prepared again
        self.prepared = false;
        Ok(())
    }

    /// Add a policy from a given file.
    ///
    /// The policy file will be parsed and converted to AST representation.
    /// Multiple policy files may be added to the engine.
    ///
    /// * `path`: Path to the policy file (.rego).
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// engine.add_policy_from_file("tests/aci/framework.rego")?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn add_policy_from_file<P: AsRef<Path>>(&mut self, path: P) -> Result<()> {
        let source = Source::from_file(path)?;
        let mut parser = Parser::new(&source)?;
        self.modules.push(Ref::new(parser.parse()?));
        self.prepared = false;
        Ok(())
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
        self.interpreter.set_data(Value::new_object());
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
        self.interpreter.get_data_mut().merge(data)
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
        self.interpreter.set_strict_builtin_errors(b)
    }

    #[doc(hidden)]
    pub fn get_modules(&mut self) -> &Vec<Ref<Module>> {
        &self.modules
    }

    /// Evaluate a Rego query.
    ///
    /// ```
    /// # use regorus::*;
    /// # fn main() -> anyhow::Result<()> {
    /// let mut engine = Engine::new();
    ///
    /// // Add policies
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
    pub fn eval_query(&mut self, query: String, enable_tracing: bool) -> Result<QueryResults> {
        self.eval_modules(enable_tracing)?;

        let query_module = {
            let source = Source::new(
                "<query_module.rego>".to_owned(),
                "package __internal_query_module".to_owned(),
            );
            Ref::new(Parser::new(&source)?.parse()?)
        };

        // Parse the query.
        let query_source = Source::new("<query.rego>".to_string(), query);
        let mut parser = Parser::new(&query_source)?;
        let query_node = parser.parse_user_query()?;
        let query_schedule = Analyzer::new().analyze_query_snippet(&self.modules, &query_node)?;
        self.interpreter.eval_user_query(
            &query_module,
            &query_node,
            &query_schedule,
            enable_tracing,
        )
    }

    pub fn eval_bool_query(&mut self, query: String, enable_tracing: bool) -> Result<bool> {
        let results = self.eval_query(query, enable_tracing)?;
        if results.result.len() != 1 || results.result[0].expressions.len() != 1 {
            bail!("query did not produce exactly one value");
        }
        results.result[0].expressions[0].value.as_bool().copied()
    }

    #[doc(hidden)]
    fn prepare_for_eval(&mut self, enable_tracing: bool) -> Result<()> {
        self.interpreter.set_traces(enable_tracing);

        // if the data/policies have changed or the interpreter has never been prepared
        if !self.prepared {
            // Analyze the modules and determine how statements must be scheduled.
            let analyzer = Analyzer::new();
            let schedule = analyzer.analyze(&self.modules)?;

            self.interpreter.set_schedule(Some(schedule));
            self.interpreter.set_modules(&self.modules);

            self.interpreter.clear_builtins_cache();
            // when the interpreter is prepared the initial data is saved
            // the data will be reset to init_data each time clean_internal_evaluation_state is called
            let init_data = self.interpreter.get_data_mut().clone();
            self.interpreter.set_init_data(init_data);

            // Initialize the with-document with initial data values.
            // with-modifiers will be applied to this document.
            self.interpreter.init_with_document()?;

            self.interpreter
                .set_functions(gather_functions(&self.modules)?);
            self.interpreter.gather_rules()?;
            self.interpreter.process_imports()?;
            self.prepared = true;
        }

        Ok(())
    }

    #[doc(hidden)]
    pub fn eval_rule(
        &mut self,
        module: &Ref<Module>,
        rule: &Ref<Rule>,
        enable_tracing: bool,
    ) -> Result<Value> {
        self.prepare_for_eval(enable_tracing)?;
        self.interpreter.clean_internal_evaluation_state();

        self.interpreter.eval_rule(module, rule)?;

        Ok(self.interpreter.get_data_mut().clone())
    }

    #[doc(hidden)]
    pub fn eval_modules(&mut self, enable_tracing: bool) -> Result<Value> {
        self.prepare_for_eval(enable_tracing)?;
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
        for module in self.modules.clone() {
            for rule in &module.policy {
                self.interpreter.eval_rule(&module, rule)?;
            }
        }
        // Defer the evaluation of the default rules to here
        for module in self.modules.clone() {
            let prev_module = self.interpreter.set_current_module(Some(module.clone()))?;
            for rule in &module.policy {
                self.interpreter.eval_default_rule(rule)?;
            }
            self.interpreter.set_current_module(prev_module)?;
        }

        // Ensure that all modules are created.
        for m in &self.modules {
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
    ///      x = y {
    ///       # y = do_magic(2)
    ///       do_magic(2, y)  # y is supplied as an out parameter.
    ///     }
    ///    "#.to_string()
    /// )?;
    ///
    /// // Evaluation fails since y is not defined.
    /// assert!(engine.eval_query("data.invalid.y".to_string(), false).is_err());
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
}
