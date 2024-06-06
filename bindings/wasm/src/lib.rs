// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(non_snake_case)]

use wasm_bindgen::prelude::*;

#[wasm_bindgen]
/// WASM wrapper for [`regorus::Engine`]
pub struct Engine {
    engine: regorus::Engine,
}

fn error_to_jsvalue<E: std::fmt::Display>(e: E) -> JsValue {
    JsValue::from_str(&format!("{e}"))
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for Engine {
    /// Clone a [`Engine`]
    ///
    /// To avoid having to parse same policy again, the engine can be cloned
    /// after policies and data have been added.
    fn clone(&self) -> Self {
        Self {
            engine: self.engine.clone(),
        }
    }
}

#[wasm_bindgen]
impl Engine {
    #[wasm_bindgen(constructor)]
    /// Construct a new Engine
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html
    pub fn new() -> Self {
        Self {
            engine: regorus::Engine::new(),
        }
    }

    /// Add a policy
    ///
    /// The policy is parsed into AST.
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_policy
    ///
    /// * `path`: A filename to be associated with the policy.
    /// * `rego`: Rego policy.
    pub fn addPolicy(&mut self, path: String, rego: String) -> Result<String, JsValue> {
        self.engine.add_policy(path, rego).map_err(error_to_jsvalue)
    }

    /// Add policy data.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_data
    /// * `data`: JSON encoded value to be used as policy data.
    pub fn addDataJson(&mut self, data: String) -> Result<(), JsValue> {
        let data = regorus::Value::from_json_str(&data).map_err(error_to_jsvalue)?;
        self.engine.add_data(data).map_err(error_to_jsvalue)
    }

    /// Get the list of packages defined by loaded policies.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_packages
    pub fn getPackages(&self) -> Result<Vec<String>, JsValue> {
        self.engine.get_packages().map_err(error_to_jsvalue)
    }

    /// Clear policy data.
    ///
    /// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.clear_data
    pub fn clearData(&mut self) -> Result<(), JsValue> {
        self.engine.clear_data();
        Ok(())
    }

    /// Set input.
    ///
    /// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.set_input
    /// * `input`: JSON encoded value to be used as input to query.
    pub fn setInputJson(&mut self, input: String) -> Result<(), JsValue> {
        let input = regorus::Value::from_json_str(&input).map_err(error_to_jsvalue)?;
        self.engine.set_input(input);
        Ok(())
    }

    /// Evaluate query.
    ///
    /// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.eval_query
    /// * `query`: Rego expression to be evaluate.
    pub fn evalQuery(&mut self, query: String) -> Result<String, JsValue> {
        let results = self
            .engine
            .eval_query(query, false)
            .map_err(error_to_jsvalue)?;
        serde_json::to_string_pretty(&results).map_err(error_to_jsvalue)
    }

    /// Evaluate rule(s) at given path.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.eval_rule
    ///
    /// * `path`: The full path to the rule(s).
    pub fn evalRule(&mut self, path: String) -> Result<String, JsValue> {
        let v = self.engine.eval_rule(path).map_err(error_to_jsvalue)?;
        v.to_json_str().map_err(error_to_jsvalue)
    }

    /// Gather output from print statements instead of emiting to stderr.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_gather_prints
    /// * `b`: Whether to enable gathering prints or not.
    pub fn setGatherPrints(&mut self, b: bool) {
        self.engine.set_gather_prints(b)
    }

    /// Take the gathered output of print statements.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.take_prints
    pub fn takePrints(&mut self) -> Result<Vec<String>, JsValue> {
        self.engine.take_prints().map_err(error_to_jsvalue)
    }

    /// Enable/disable policy coverage.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.set_enable_coverage
    /// * `b`: Whether to enable gathering coverage or not.
    #[cfg(feature = "coverage")]
    pub fn setEnableCoverage(&mut self, enable: bool) {
        self.engine.set_enable_coverage(enable)
    }

    /// Get the coverage report as json.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_coverage_report
    #[cfg(feature = "coverage")]
    pub fn getCoverageReport(&self) -> Result<String, JsValue> {
        let report = self
            .engine
            .get_coverage_report()
            .map_err(error_to_jsvalue)?;
        serde_json::to_string_pretty(&report).map_err(error_to_jsvalue)
    }

    /// Clear gathered coverage data.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.clear_coverage_data
    #[cfg(feature = "coverage")]
    pub fn clearCoverageData(&mut self) {
        self.engine.clear_coverage_data()
    }

    /// Get ANSI color coded coverage report.
    ///
    /// See https://docs.rs/regorus/latest/regorus/coverage/struct.Report.html#method.to_string_pretty
    #[cfg(feature = "coverage")]
    pub fn getCoverageReportPretty(&self) -> Result<String, JsValue> {
        let report = self
            .engine
            .get_coverage_report()
            .map_err(error_to_jsvalue)?;
        report.to_string_pretty().map_err(error_to_jsvalue)
    }

    /// Get AST of policies.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.get_ast_as_json
    #[cfg(feature = "ast")]
    pub fn getAstAsJson(&self) -> Result<String, JsValue> {
        self.engine.get_ast_as_json().map_err(error_to_jsvalue)
    }
}

#[cfg(test)]
mod tests {
    use wasm_bindgen::prelude::*;
    use wasm_bindgen_test::wasm_bindgen_test;

    #[wasm_bindgen_test]
    pub fn basic() -> Result<(), JsValue> {
        let mut engine = crate::Engine::new();
        engine.setEnableCoverage(true);

        // Exercise all APIs.
        engine.addDataJson(
            r#"
        {
           "foo" : "bar"
        }
        "#
            .to_string(),
        )?;

        engine.setInputJson(
            r#"
        {
           "message" : "Hello"
        }
        "#
            .to_string(),
        )?;

        let pkg = engine.addPolicy(
            "hello.rego".to_string(),
            r#"
            package test
            message = input.message"#
                .to_string(),
        )?;
        assert_eq!(pkg, "data.test");

        let results = engine.evalQuery("data".to_string())?;
        let r = regorus::Value::from_json_str(&results).map_err(crate::error_to_jsvalue)?;

        let v = &r["result"][0]["expressions"][0]["value"];

        // Ensure that input and policy were evaluated.
        assert_eq!(v["test"]["message"], regorus::Value::from("Hello"));

        // Test that data was set.
        assert_eq!(v["foo"], regorus::Value::from("bar"));

        // Use eval_rule to perform same query.
        let v = engine.evalRule("data.test.message".to_owned())?;
        let v = regorus::Value::from_json_str(&v).map_err(crate::error_to_jsvalue)?;

        // Ensure that input and policy were evaluated.
        assert_eq!(v, regorus::Value::from("Hello"));

        let pkgs = engine.getPackages()?;
        assert_eq!(pkgs, vec!["data.test"]);

        engine.setGatherPrints(true);
        let _ = engine.evalQuery("print(\"Hello\")".to_owned());
        let prints = engine.takePrints()?;
        assert_eq!(prints, vec!["<query.rego>:1: Hello"]);

        // Test clone.
        let mut engine1 = engine.clone();

        // Test code coverage.
        let report = engine1.getCoverageReport()?;
        let r = regorus::Value::from_json_str(&report).map_err(crate::error_to_jsvalue)?;

        assert_eq!(
            r["files"][0]["covered"]
                .as_array()
                .map_err(crate::error_to_jsvalue)?,
            &vec![regorus::Value::from(3)]
        );

        println!("{}", engine1.getCoverageReportPretty()?);

        engine1.clearCoverageData();
        Ok(())
    }
}
