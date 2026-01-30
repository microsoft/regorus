// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
use anyhow::{anyhow, Result};
use pyo3::exceptions::PyTypeError;
use pyo3::prelude::*;
use pyo3::types::*;
use pyo3::IntoPyObjectExt;

use std::collections::{BTreeMap, BTreeSet};

use ::regorus::languages::rego::compiler::Compiler;
use ::regorus::rvm::program::{
    generate_assembly_listing, generate_tabular_assembly_listing, AssemblyListingConfig,
    DeserializationResult, Program as RvmProgram,
};
use ::regorus::rvm::vm::{ExecutionMode, RegoVM};
use ::regorus::{compile_policy_with_entrypoint, PolicyModule, Rc, Value};
use std::sync::Arc;

/// Regorus engine.
#[pyclass(unsendable)]
pub struct Engine {
    engine: ::regorus::Engine,
}

/// RVM program wrapper.
#[pyclass(unsendable)]
pub struct Program {
    program: Arc<RvmProgram>,
}

/// RVM runtime wrapper.
#[pyclass(unsendable)]
pub struct Rvm {
    vm: RegoVM,
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

fn from(ob: &Bound<'_, PyAny>) -> Result<Value, PyErr> {
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
        for i in 0..keys.len() {
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
    let obj = match v {
        Value::Null => None::<u64>.into_bound_py_any(py),

        // TODO: Revisit this mapping
        Value::Undefined => None::<u64>.into_bound_py_any(py),

        Value::Bool(b) => b.into_bound_py_any(py),
        Value::String(s) => s.into_bound_py_any(py),

        Value::Number(_) => {
            if let Ok(f) = v.as_f64() {
                f.into_bound_py_any(py)
            } else if let Ok(u) = v.as_u64() {
                u.into_bound_py_any(py)
            } else {
                v.as_i64()?.into_bound_py_any(py)
            }
        }

        Value::Array(_) => {
            let list = PyList::empty(py);
            for v in std::mem::take(v.as_array_mut()?) {
                list.append(to(v, py)?)?;
            }
            list.into_bound_py_any(py)
        }

        Value::Set(_) => {
            let set = PySet::empty(py)?;
            for v in std::mem::take(v.as_set_mut()?) {
                set.add(to(v, py)?)?;
            }
            set.into_bound_py_any(py)
        }

        Value::Object(_) => {
            let dict = PyDict::new(py);
            for (k, v) in std::mem::take(v.as_object_mut()?) {
                dict.set_item(to(k, py)?, to(v, py)?)?;
            }
            dict.into_bound_py_any(py)
        }
    };
    match obj {
        Ok(v) => Ok(v.into()),
        Err(e) => Err(anyhow!("{e}")),
    }
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

    /// Turn on rego v0.
    ///
    /// Regorus now defaults to v1.
    ///
    /// * `enable`: Whether to enable/disable v0.
    pub fn set_rego_v0(&mut self, enable: bool) {
        self.engine.set_rego_v0(enable)
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
    pub fn get_packages(&self) -> Result<Vec<String>> {
        self.engine.get_packages()
    }

    /// Get the list of policies.
    ///
    pub fn get_policies(&self) -> Result<String> {
        Ok(serde_json::to_string_pretty(
            &self.engine.get_policies_as_json()?,
        )?)
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
        let data = Value::from_json_file(path)?;
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
        let input = Value::from_json_file(path)?;
        self.engine.set_input(input);
        Ok(())
    }

    /// Evaluate query.
    ///
    /// * `query`: Rego expression to be evaluate.
    pub fn eval_query(&mut self, query: String, py: Python<'_>) -> Result<PyObject> {
        let results = self.engine.eval_query(query, false)?;

        let rlist = PyList::empty(py);
        for result in results.result.into_iter() {
            let rdict = PyDict::new(py);

            let elist = PyList::empty(py);
            for expr in result.expressions.into_iter() {
                let edict = PyDict::new(py);
                edict.set_item("value", to(expr.value, py)?)?;
                edict.set_item("text", expr.text.as_ref())?;

                let ldict = PyDict::new(py);
                ldict.set_item("row", expr.location.row)?;
                ldict.set_item("col", expr.location.col)?;

                edict.set_item("location", ldict)?;
                elist.append(edict)?;
            }

            rdict.set_item("expressions", elist)?;
            rdict.set_item("bindings", to(result.bindings, py)?)?;
            rlist.append(rdict)?;
        }
        let dict = PyDict::new(py);
        dict.set_item("result", rlist)?;
        Ok(dict.into())
    }

    /// Evaluate query. Returns result as JSON.
    ///
    /// * `query`: Rego expression to be evaluate.
    pub fn eval_query_as_json(&mut self, query: String) -> Result<String> {
        let results = self.engine.eval_query(query, false)?;
        serde_json::to_string_pretty(&results).map_err(|e| anyhow!("{e}"))
    }

    /// Evaluate rule.
    ///
    /// * `rule`: Full path to the rule.
    pub fn eval_rule(&mut self, rule: String, py: Python<'_>) -> Result<PyObject> {
        to(self.engine.eval_rule(rule)?, py)
    }

    /// Evaluate rule and return value as json.
    ///
    /// * `rule`: Full path to the rule.
    pub fn eval_rule_as_json(&mut self, rule: String) -> Result<String> {
        let v = self.engine.eval_rule(rule)?;
        v.to_json_str()
    }

    /// Enable code coverage
    ///
    /// * `enable`: Whether to enable coverage or not.
    pub fn set_enable_coverage(&mut self, enable: bool) {
        self.engine.set_enable_coverage(enable)
    }

    /// Get coverage report as json.
    ///
    #[cfg(feature = "coverage")]
    pub fn get_coverage_report_as_json(&self) -> Result<String> {
        let report = self.engine.get_coverage_report()?;
        serde_json::to_string_pretty(&report).map_err(|e| anyhow!("{e}"))
    }

    /// Get coverage report as pretty printable string.
    ///
    #[cfg(feature = "coverage")]
    pub fn get_coverage_report_pretty(&self) -> Result<String> {
        self.engine.get_coverage_report()?.to_string_pretty()
    }

    /// Clear coverage data.
    ///
    #[cfg(feature = "coverage")]
    pub fn clear_coverage_data(&mut self) {
        self.engine.clear_coverage_data();
    }

    /// Gather print statements instead of printing to stderr.
    ///
    pub fn set_gather_prints(&mut self, b: bool) {
        self.engine.set_gather_prints(b)
    }

    /// Take gathered prints.
    ///
    pub fn take_prints(&mut self) -> Result<Vec<String>> {
        self.engine.take_prints()
    }

    /// Clone a [`Engine`]
    ///
    /// To avoid having to parse same policy again, the engine can be cloned
    /// after policies and data have been added.
    fn clone(&self) -> Self {
        Self {
            engine: self.engine.clone(),
        }
    }

    /// Get AST of policies.
    ///
    #[cfg(feature = "ast")]
    pub fn get_ast_as_json(&self) -> Result<String> {
        self.engine.get_ast_as_json()
    }
}

#[pymethods]
impl Program {
    /// Compile an RVM program from modules and entry points.
    #[staticmethod]
    pub fn compile_from_modules(
        data_json: String,
        modules: Vec<(String, String)>,
        entry_points: Vec<String>,
    ) -> Result<Self> {
        if entry_points.is_empty() {
            return Err(anyhow!("entry_points must contain at least one entry"));
        }

        let data = Value::from_json_str(&data_json)?;
        let policy_modules: Vec<PolicyModule> = modules
            .into_iter()
            .map(|(id, content)| PolicyModule {
                id: Rc::from(id.as_str()),
                content: Rc::from(content.as_str()),
            })
            .collect();

        let entry_points_ref: Vec<&str> = entry_points.iter().map(|s| s.as_str()).collect();
        let entry_rule = Rc::from(entry_points_ref[0]);
        let compiled = compile_policy_with_entrypoint(data, &policy_modules, entry_rule)?;
        let program = Compiler::compile_from_policy(&compiled, &entry_points_ref)?;
        Ok(Self { program })
    }

    /// Deserialize an RVM program from binary data.
    #[staticmethod]
    pub fn deserialize_binary(data: Vec<u8>) -> Result<(Self, bool)> {
        let (program, is_partial) =
            match RvmProgram::deserialize_binary(&data).map_err(|e: String| anyhow!(e))? {
                DeserializationResult::Complete(program) => (program, false),
                DeserializationResult::Partial(program) => (program, true),
            };
        Ok((
            Self {
                program: Arc::new(program),
            },
            is_partial,
        ))
    }

    /// Serialize a program to binary format.
    pub fn serialize_binary(&self) -> Result<Vec<u8>> {
        self.program
            .serialize_binary()
            .map_err(|e: String| anyhow!(e))
    }

    /// Generate a readable assembly listing.
    pub fn generate_listing(&self) -> Result<String> {
        Ok(generate_assembly_listing(
            self.program.as_ref(),
            &AssemblyListingConfig::default(),
        ))
    }

    /// Generate a tabular assembly listing.
    pub fn generate_tabular_listing(&self) -> Result<String> {
        Ok(generate_tabular_assembly_listing(
            self.program.as_ref(),
            &AssemblyListingConfig::default(),
        ))
    }
}

impl Default for Rvm {
    fn default() -> Self {
        Self::new()
    }
}

#[pymethods]
impl Rvm {
    #[new]
    pub fn new() -> Self {
        Self { vm: RegoVM::new() }
    }

    /// Load an RVM program into the VM.
    pub fn load_program(&mut self, program: &Program) -> Result<()> {
        self.vm.load_program(program.program.clone());
        Ok(())
    }

    /// Set data JSON for the VM.
    pub fn set_data_json(&mut self, data_json: String) -> Result<()> {
        let data = Value::from_json_str(&data_json)?;
        self.vm.set_data(data)?;
        Ok(())
    }

    /// Set input JSON for the VM.
    pub fn set_input_json(&mut self, input_json: String) -> Result<()> {
        let input = Value::from_json_str(&input_json)?;
        self.vm.set_input(input);
        Ok(())
    }

    /// Set execution mode (0 = run-to-completion, 1 = suspendable).
    pub fn set_execution_mode(&mut self, mode: u8) -> Result<()> {
        let mode = match mode {
            0 => ExecutionMode::RunToCompletion,
            1 => ExecutionMode::Suspendable,
            _ => return Err(anyhow!("invalid execution mode")),
        };
        self.vm.set_execution_mode(mode);
        Ok(())
    }

    /// Execute the program and return the JSON result.
    pub fn execute(&mut self) -> Result<String> {
        self.vm.execute()?.to_json_str()
    }

    /// Execute an entry point by name and return the JSON result.
    pub fn execute_entry_point(&mut self, entry_point: String) -> Result<String> {
        self.vm
            .execute_entry_point_by_name(&entry_point)?
            .to_json_str()
    }

    /// Resume execution with an optional JSON value.
    pub fn resume(&mut self, resume_json: Option<String>) -> Result<String> {
        let value = if let Some(json) = resume_json {
            Some(Value::from_json_str(&json)?)
        } else {
            None
        };
        self.vm.resume(value)?.to_json_str()
    }

    /// Get the execution state as a string.
    pub fn get_execution_state(&self) -> Result<String> {
        Ok(format!("{:?}", self.vm.execution_state()))
    }
}

#[pymodule]
pub fn regorus(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<crate::Engine>()?;
    m.add_class::<crate::Program>()?;
    m.add_class::<crate::Rvm>()?;
    Ok(())
}
