use magnus::{exception::runtime_error, method, module, prelude::*, Error, Ruby};
use regorus::Engine as RegorusEngine;
use std::cell::RefCell;
use std::cmp::Ordering;

// `Value` exists under magnus, regorus, and serde_json, so be explicit

#[derive(Default)]
#[magnus::wrap(class = "Regorus::Engine")]
pub struct Engine {
    engine: RefCell<RegorusEngine>,
}

impl Clone for Engine {
    fn clone(&self) -> Self {
        Self {
            engine: self.engine.clone(),
        }
    }
}

impl Engine {
    fn initialize(&self) {
        let engine = RegorusEngine::new();
        *self.engine.borrow_mut() = engine;
    }

    fn compare(&self, other: &Self) -> Result<i32, Error> {
        let self_ptr: *const _ = &*self.engine.borrow();
        let other_ptr: *const _ = &*other.engine.borrow();
        match self_ptr.partial_cmp(&other_ptr) {
            Some(Ordering::Less) => Ok(-1),
            Some(Ordering::Equal) => Ok(0),
            Some(Ordering::Greater) => Ok(1),
            None => Err(Error::new(runtime_error(), "Comparison failed")),
        }
    }

    fn add_policy(&self, path: String, rego: String) -> Result<(), Error> {
        self.engine
            .borrow_mut()
            .add_policy(path, rego)
            .map_err(|e| Error::new(runtime_error(), format!("Failed to add policy: {}", e)))
    }

    fn add_policy_from_file(&self, path: String) -> Result<(), Error> {
        self.engine
            .borrow_mut()
            .add_policy_from_file(path)
            .map_err(|e| Error::new(runtime_error(), format!("Failed to add policy: {}", e)))
    }

    fn add_data(&self, ruby_hash: magnus::RHash) -> Result<(), Error> {
        let data_value: regorus::Value = serde_magnus::deserialize(ruby_hash).map_err(|e| {
            Error::new(
                runtime_error(),
                format!("Failed to deserialize Ruby value: {}", e),
            )
        })?;

        self.engine
            .borrow_mut()
            .add_data(data_value)
            .map_err(|e| Error::new(runtime_error(), format!("Failed to add data: {}", e)))
    }

    fn add_data_json(&self, json_string: String) -> Result<(), Error> {
        self.engine
            .borrow_mut()
            .add_data_json(&json_string)
            .map_err(|e| Error::new(runtime_error(), format!("Failed to add data json: {}", e)))
    }

    fn add_data_from_json_file(&self, path: String) -> Result<(), Error> {
        let json_data = regorus::Value::from_json_file(&path).map_err(|e| {
            Error::new(
                runtime_error(),
                format!("Failed to parse JSON data file: {}", e),
            )
        })?;

        self.engine.borrow_mut().add_data(json_data).map_err(|e| {
            Error::new(
                runtime_error(),
                format!("Failed to add data from file: {}", e),
            )
        })
    }

    fn clear_data(&self) -> Result<(), Error> {
        self.engine.borrow_mut().clear_data();
        Ok(())
    }

    fn set_input(&self, ruby_hash: magnus::RHash) -> Result<(), Error> {
        let input_value: regorus::Value = serde_magnus::deserialize(ruby_hash).map_err(|e| {
            Error::new(
                runtime_error(),
                format!("Failed to deserialize Ruby value: {}", e),
            )
        })?;

        self.engine.borrow_mut().set_input(input_value);
        Ok(())
    }

    fn set_input_json(&self, json_string: String) -> Result<(), Error> {
        self.engine
            .borrow_mut()
            .set_input_json(&json_string)
            .map_err(|e| Error::new(runtime_error(), format!("Failed to set input JSON: {}", e)))
    }

    fn add_input_from_json_file(&self, path: String) -> Result<(), Error> {
        let json_data = regorus::Value::from_json_file(&path).map_err(|e| {
            Error::new(
                runtime_error(),
                format!("Failed to parse JSON input file: {}", e),
            )
        })?;

        self.engine.borrow_mut().set_input(json_data);
        Ok(())
    }

    fn eval_query(&self, query: String) -> Result<magnus::Value, Error> {
        let results = self
            .engine
            .borrow_mut()
            .eval_query(query, false)
            .map_err(|e| Error::new(runtime_error(), format!("Failed to evaluate query: {}", e)))?;

        serde_magnus::serialize(&results).map_err(|e| {
            Error::new(
                runtime_error(),
                format!("Failed to serailzie query results: {}", e),
            )
        })
    }

    fn eval_query_as_json(&self, query: String) -> Result<String, Error> {
        let results = self
            .engine
            .borrow_mut()
            .eval_query(query, false)
            .map_err(|e| {
                Error::new(
                    runtime_error(),
                    format!("Failed to evaluate query as json: {}", e),
                )
            })?;

        serde_json::to_string(&results).map_err(|e| {
            Error::new(
                runtime_error(),
                format!("Failed to serialize query results: {}", e),
            )
        })
    }

    fn eval_rule(&self, path: String) -> Result<Option<magnus::Value>, Error> {
        let result =
            self.engine.borrow_mut().eval_rule(path).map_err(|e| {
                Error::new(runtime_error(), format!("Failed to evaluate rule: {}", e))
            })?;

        match result {
            regorus::Value::Undefined => Ok(None), // Convert undefined to Ruby's nil
            _ => serde_magnus::serialize(&result) // Serialize other results normally
                .map(Some)
                .map_err(|e| {
                    magnus::Error::new(
                        runtime_error(),
                        format!("Failed to serialize the rule evaluation result: {}", e),
                    )
                }),
        }
    }
}

#[magnus::init]
fn init(ruby: &Ruby) -> Result<(), Error> {
    let regorus_module = ruby.define_module("Regorus")?;
    let engine_class = regorus_module.define_class("Engine", ruby.class_object())?;

    // ruby object methods
    engine_class.define_alloc_func::<Engine>();
    engine_class.define_method("initialize", method!(Engine::initialize, 0))?;
    engine_class.define_method("clone", method!(Engine::clone, 0))?;
    engine_class.define_method("<=>", method!(Engine::compare, 1))?;
    // defines <, <=, >, >=, and == based on <=>
    engine_class.include_module(module::comparable())?;

    // policy operations
    engine_class.define_method("add_policy", method!(Engine::add_policy, 2))?;
    engine_class.define_method(
        "add_policy_from_file",
        method!(Engine::add_policy_from_file, 1),
    )?;

    // data operations
    engine_class.define_method("add_data", method!(Engine::add_data, 1))?;
    engine_class.define_method("add_data_json", method!(Engine::add_data_json, 1))?;
    engine_class.define_method(
        "add_data_from_json_file",
        method!(Engine::add_data_from_json_file, 1),
    )?;
    engine_class.define_method("clear_data", method!(Engine::clear_data, 0))?;

    // input operations
    engine_class.define_method("set_input", method!(Engine::set_input, 1))?;
    engine_class.define_method("set_input_json", method!(Engine::set_input_json, 1))?;
    engine_class.define_method(
        "add_input_from_json_file",
        method!(Engine::add_input_from_json_file, 1),
    )?;

    // query operations
    engine_class.define_method("eval_query", method!(Engine::eval_query, 1))?;
    engine_class.define_method("eval_query_as_json", method!(Engine::eval_query_as_json, 1))?;
    engine_class.define_method("eval_rule", method!(Engine::eval_rule, 1))?;

    Ok(())
}
