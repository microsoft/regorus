// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

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
    pub fn add_policy(&mut self, path: String, rego: String) -> Result<String, JsValue> {
        self.engine.add_policy(path, rego).map_err(error_to_jsvalue)
    }

    /// Add policy data.
    ///
    /// See https://docs.rs/regorus/latest/regorus/struct.Engine.html#method.add_data
    /// * `data`: JSON encoded value to be used as policy data.
    pub fn add_data_json(&mut self, data: String) -> Result<(), JsValue> {
        let data = regorus::Value::from_json_str(&data).map_err(error_to_jsvalue)?;
        self.engine.add_data(data).map_err(error_to_jsvalue)
    }

    /// Clear policy data.
    ///
    /// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.clear_data
    pub fn clear_data(&mut self) -> Result<(), JsValue> {
        self.engine.clear_data();
        Ok(())
    }

    /// Set input.
    ///
    /// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.set_input
    /// * `input`: JSON encoded value to be used as input to query.
    pub fn set_input_json(&mut self, input: String) -> Result<(), JsValue> {
        let input = regorus::Value::from_json_str(&input).map_err(error_to_jsvalue)?;
        self.engine.set_input(input);
        Ok(())
    }

    /// Evaluate query.
    ///
    /// See https://docs.rs/regorus/0.1.0-alpha.2/regorus/struct.Engine.html#method.eval_query
    /// * `query`: Rego expression to be evaluate.
    pub fn eval_query(&mut self, query: String) -> Result<String, JsValue> {
        let results = self
            .engine
            .eval_query(query, false)
            .map_err(error_to_jsvalue)?;
        serde_json::to_string_pretty(&results).map_err(error_to_jsvalue)
    }
}

#[cfg(test)]
mod tests {
    use wasm_bindgen::prelude::*;
    use wasm_bindgen_test::wasm_bindgen_test;

    #[wasm_bindgen_test]
    pub fn basic() -> Result<(), JsValue> {
        let mut engine = crate::Engine::new();

        // Exercise all APIs.
        engine.add_data_json(
            r#"
        {
           "foo" : "bar"
        }
        "#
            .to_string(),
        )?;

        engine.set_input_json(
            r#"
        {
           "message" : "Hello"
        }
        "#
            .to_string(),
        )?;

        engine.add_policy(
            "hello.rego".to_string(),
            r#"
            package test
            message = input.message"#
                .to_string(),
        )?;

        let results = engine.eval_query("data".to_string())?;
        let r = regorus::Value::from_json_str(&results).map_err(crate::error_to_jsvalue)?;

        let v = &r["result"][0]["expressions"][0]["value"];

        // Ensure that input and policy were evaluated.
        assert_eq!(v["test"]["message"], regorus::Value::from("Hello"));

        // Test that data was set.
        assert_eq!(v["foo"], regorus::Value::from("bar"));

        Ok(())
    }
}
