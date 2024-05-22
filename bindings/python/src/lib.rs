// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use anyhow::{anyhow, Result};
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use pyo3::types::*;

use std::collections::{BTreeMap, BTreeSet};

use ::regorus::Value;

/// Regorus engine.
#[pyclass(unsendable)]
pub struct Engine {
    engine: ::regorus::Engine,
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

fn from<'source>(ob: &Bound<'_, PyAny>) -> Result<Value, PyErr> {
    // dicts
    Ok(if let Ok(dict) = ob.downcast::<PyDict>() {
        let mut map = BTreeMap::new();
        for (k, v) in dict {
            map.insert(from(&k)?, from(&v)?);
        }
        map.into()
    }
    // set
    else if let Ok(pset) = ob.downcast::<PySet>() {
        let mut set = BTreeSet::new();
        for v in pset {
            set.insert(from(&v)?);
        }
        set.into()
    }
    // frozen set
    else if let Ok(pfset) = ob.downcast::<PyFrozenSet>() {
        //
        let mut set = BTreeSet::new();
        for v in pfset {
            set.insert(from(&v)?);
        }
        set.into()
    }
    // lists and tuples
    else if let Ok(plist) = ob.downcast::<PyList>() {
        let mut array = Vec::new();
        for v in plist {
            array.push(from(&v)?);
        }
        array.into()
    } else if let Ok(ptuple) = ob.downcast::<PyTuple>() {
        let mut array = Vec::new();
        for v in ptuple {
            array.push(from(&v)?);
        }
        array.into()
    }
    // String
    else if let Ok(s) = ob.extract::<String>() {
        s.into()
    }
    // Numeric
    else if let Ok(v) = ob.extract::<i64>() {
        v.into()
    } else if let Ok(v) = ob.extract::<u64>() {
        v.into()
    } else if let Ok(v) = ob.extract::<f64>() {
        v.into()
    }
    // Boolean
    else if let Ok(b) = ob.extract::<bool>() {
        b.into()
    }
    // None
    else if ob.downcast::<PyNone>().is_ok() {
        Value::Null
    }
    // Anything that is a sequence
    else if let Ok(pseq) = ob.downcast::<PySequence>() {
        let mut array = Vec::new();
        for i in 0..pseq.len()? {
            array.push(from(&pseq.get_item(i)?)?);
        }
        array.into()
    }
    // Anything that is a map
    else if let Ok(pmap) = ob.downcast::<PyMapping>() {
        let mut map = BTreeMap::new();
        let keys = pmap.keys()?;
        let values = pmap.values()?;
        for i in 0..keys.len()? {
            let key = keys.get_item(i)?;
            let value = values.get_item(i)?;
            map.insert(from(&key)?, from(&value)?);
        }
        map.into()
    } else {
        return Err(PyErr::new::<PyTypeError, _>(
            "object cannot be converted to RegoValue",
        ));
    })
}

fn to(mut v: Value, py: Python<'_>) -> Result<PyObject> {
    Ok(match v {
        Value::Null => None::<u64>.to_object(py),

        // TODO: Revisit this mapping
        Value::Undefined => None::<u64>.to_object(py),

        Value::Bool(b) => b.to_object(py),
        Value::String(s) => s.to_object(py),

        Value::Number(_) => {
            if let Ok(f) = v.as_f64() {
                f.to_object(py)
            } else if let Ok(u) = v.as_u64() {
                u.to_object(py)
            } else {
                v.as_i64()?.to_object(py)
            }
        }

        Value::Array(_) => {
            let list = PyList::empty_bound(py);
            for v in std::mem::replace(v.as_array_mut()?, Vec::new()) {
                list.append(to(v, py)?)?;
            }
            list.into()
        }

        Value::Set(_) => {
            let set = PySet::empty_bound(py)?;
            for v in std::mem::replace(v.as_set_mut()?, BTreeSet::new()) {
                set.add(to(v, py)?)?;
            }
            set.into()
        }

        Value::Object(_) => {
            let dict = PyDict::new_bound(py);
            for (k, v) in std::mem::replace(v.as_object_mut()?, BTreeMap::new()) {
                dict.set_item(to(k, py)?, to(v, py)?)?;
            }
            dict.into()
        }
    })
}

#[pymethods]
impl Engine {
    /// Construct a new Engine
    #[new]
    pub fn new() -> Self {
        Self {
            engine: ::regorus::Engine::new(),
        }
    }

    /// Add a policy
    ///
    /// The policy is parsed into AST.
    ///
    /// * `path`: A filename to be associated with the policy.
    /// * `rego`: Rego policy.
    pub fn add_policy(&mut self, path: String, rego: String) -> Result<String> {
        self.engine.add_policy(path, rego)
    }

    /// Add a policy from given file.
    ///
    /// The policy is parsed into AST.
    ///
    /// * `path`: Path to the policy file.
    pub fn add_policy_from_file(&mut self, path: String) -> Result<String> {
        self.engine.add_policy_from_file(path)
    }

    /// Get the list of packages defined by loaded policies.
    ///
    pub fn get_packages(&mut self) -> Result<Vec<String>> {
        self.engine.get_packages()
    }

    /// Add policy data.
    ///
    /// * `data`: Rego value. A Rego value is a number, bool, string, None
    ///           or a list/set/map whose items themselves are Rego values.
    pub fn add_data(&mut self, data: &Bound<'_, PyAny>) -> Result<()> {
        let data = from(data)?;
        self.engine.add_data(data)
    }

    /// Add policy data.
    ///
    /// * `data`: JSON encoded value to be used as policy data.
    pub fn add_data_json(&mut self, data: String) -> Result<()> {
        let data = Value::from_json_str(&data)?;
        self.engine.add_data(data)
    }

    /// Add policy data from file.
    ///
    /// * `path`: Path to JSON policy data.
    pub fn add_data_from_json_file(&mut self, path: String) -> Result<()> {
        let data = Value::from_json_file(&path)?;
        self.engine.add_data(data)
    }

    /// Clear policy data.
    pub fn clear_data(&mut self) -> Result<()> {
        self.engine.clear_data();
        Ok(())
    }

    /// Set input.
    ///
    /// * `input`: Rego value. A Rego value is a number, bool, string, None
    ///            or a list/set/map whose items themselves are Rego values.
    pub fn set_input(&mut self, input: &Bound<'_, PyAny>) -> Result<()> {
        let input = from(input)?;
        self.engine.set_input(input);
        Ok(())
    }

    /// Set input.
    ///
    /// * `input`: JSON encoded value to be used as input to query.
    pub fn set_input_json(&mut self, input: String) -> Result<()> {
        let input = Value::from_json_str(&input)?;
        self.engine.set_input(input);
        Ok(())
    }

    /// Set input.
    ///
    /// * `path`: Path to JSON input data.
    pub fn set_input_from_json_file(&mut self, path: String) -> Result<()> {
        let input = Value::from_json_file(&path)?;
        self.engine.set_input(input);
        Ok(())
    }

    /// Evaluate query.
    ///
    /// * `query`: Rego expression to be evaluate.
    pub fn eval_query(&mut self, query: String, py: Python<'_>) -> Result<PyObject> {
        let results = self.engine.eval_query(query, false)?;

        let rlist = PyList::empty_bound(py);
        for result in results.result.into_iter() {
            let rdict = PyDict::new_bound(py);

            let elist = PyList::empty_bound(py);
            for expr in result.expressions.into_iter() {
                let edict = PyDict::new_bound(py);
                edict.set_item("value".to_object(py), to(expr.value, py)?)?;
                edict.set_item("text".to_object(py), expr.text.as_ref().to_object(py))?;

                let ldict = PyDict::new_bound(py);
                ldict.set_item("row".to_object(py), expr.location.row.to_object(py))?;
                ldict.set_item("col".to_object(py), expr.location.col.to_object(py))?;

                edict.set_item("location".to_object(py), ldict)?;
                elist.append(edict)?;
            }

            rdict.set_item("expressions".to_object(py), elist)?;
            rdict.set_item("bindings".to_object(py), to(result.bindings, py)?)?;
            rlist.append(rdict)?;
        }
        let dict = PyDict::new_bound(py);
        dict.set_item("result".to_object(py), rlist)?;
        Ok(dict.into())
    }

    /// Evaluate query. Returns result as JSON.
    ///
    /// * `query`: Rego expression to be evaluate.
    pub fn eval_query_as_json(&mut self, query: String) -> Result<String> {
        let results = self.engine.eval_query(query, false)?;
        serde_json::to_string_pretty(&results).map_err(|e| anyhow!("{e}"))
    }
}

#[pymodule]
pub fn regorus(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<crate::Engine>()
}
