// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::print_stderr, clippy::pattern_type_mismatch)]

use crate::ast::*;
use crate::builtins::{self, BuiltinFcn};
use crate::compiled_policy::CompiledPolicyData;
#[cfg(feature = "azure_policy")]
use crate::compiled_policy::TargetInfo;
use crate::compiler::destructuring_planner::{
    AssignmentPlan, BindingPlan, DestructuringPlan, WildcardSide,
};
use crate::compiler::hoist::{HoistedLoop, LoopType};
use crate::lexer::*;
use crate::lookup::Lookup;
use crate::parser::Parser;
use crate::scheduler::*;
use crate::utils::limits::{monotonic_now, ExecutionTimer, ExecutionTimerConfig};
#[cfg(feature = "std")]
use crate::utils::*;
#[cfg(not(feature = "std"))]
use crate::utils::{get_extra_arg, get_path_string, get_root_var, FunctionTable};
use crate::value::*;
use crate::*;
use crate::{Expression, Extension, Location, QueryResult, QueryResults};

#[cfg(feature = "coverage")]
use crate::query::traversal::traverse;

use crate::Rc;
use alloc::collections::btree_map::Entry as BTreeMapEntry;
use alloc::collections::{BTreeMap, BTreeSet};
use anyhow::{anyhow, bail, Result};
use core::ops::Bound::*;

type Scope = BTreeMap<SourceStr, Value>;
type ExprLookup = Lookup<Value>;

#[cfg(feature = "azure_policy")]
pub mod error;
#[cfg(feature = "azure_policy")]
pub mod target {
    pub mod infer;
    pub mod resolve;
}

type ContextExprs = (Option<Ref<Expr>>, Option<Ref<Expr>>);
type State = (
    Value,
    Value,
    Value,
    BTreeSet<Ref<Rule>>,
    Value,
    BTreeMap<String, FunctionModifier>,
    RuleValues,
);

#[derive(Debug, Clone)]
enum FunctionModifier {
    Function(String),
    Value(Value),
}

type RuleValues = BTreeMap<Vec<Value>, (Value, Ref<Expr>)>;

#[derive(Debug)]
pub struct Interpreter {
    compiled_policy: Rc<CompiledPolicyData>,

    data: Value,

    #[cfg(feature = "coverage")]
    coverage: Map<Source, Vec<bool>>,
    #[cfg(feature = "coverage")]
    enable_coverage: bool,

    traces: Option<Vec<Rc<str>>>,

    gather_prints: bool,
    prints: Vec<String>,

    extensions: Map<String, (u8, Rc<Box<dyn Extension>>)>,
    module: Option<Ref<Module>>,
    current_module_path: String,
    current_module_index: u32,
    query_schedule: Option<Schedule>,
    query_module: Option<NodeRef<Module>>,
    input: Value,

    init_data: Value,
    with_document: Value,
    with_functions: BTreeMap<String, FunctionModifier>,
    scopes: Vec<Scope>,
    // TODO: handle recursive calls where same expr could have different values.
    loop_var_values: ExprLookup,
    contexts: Vec<Context>,

    processed: BTreeSet<Ref<Rule>>,
    processed_paths: Value,
    rule_values: RuleValues,
    active_rules: Vec<Ref<Rule>>,
    builtins_cache: BTreeMap<(&'static str, Vec<Value>), Value>,
    no_rules_lookup: bool,
    execution_timer: ExecutionTimer,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

impl Clone for Interpreter {
    fn clone(&self) -> Self {
        Self {
            compiled_policy: self.compiled_policy.clone(),

            data: self.data.clone(),
            init_data: self.init_data.clone(),
            input: self.input.clone(),
            with_document: self.with_document.clone(),
            with_functions: self.with_functions.clone(),

            gather_prints: self.gather_prints,
            prints: self.prints.clone(),
            traces: self.traces.clone(),

            extensions: self.extensions.clone(),

            #[cfg(feature = "coverage")]
            coverage: self.coverage.clone(),
            #[cfg(feature = "coverage")]
            enable_coverage: self.enable_coverage,

            // The following fields always get cleared during an evaluation.
            // Hence, they need not be copied.
            processed: BTreeSet::default(),
            processed_paths: Value::new_object(),
            loop_var_values: ExprLookup::new(),
            scopes: Vec::default(),
            rule_values: BTreeMap::default(),

            builtins_cache: BTreeMap::default(),
            active_rules: Vec::default(),
            contexts: Vec::default(),
            current_module_path: String::default(),
            current_module_index: 0,
            query_schedule: None,
            query_module: None,
            module: None,
            no_rules_lookup: false,
            execution_timer: ExecutionTimer::new(self.execution_timer.config()),
        }
    }
}

#[derive(Debug, Clone)]
struct Context {
    key_expr: Option<ExprRef>,
    output_expr: Option<ExprRef>,
    value: Value,
    result: Option<QueryResult>,
    results: QueryResults,
    is_compr: bool,
    rule_ref: Option<ExprRef>,
    rule_value: Value,
    is_set: bool,
    is_old_style_set: bool,
    output_constness_determined: bool,
    early_return: bool,
}

impl Default for Context {
    fn default() -> Self {
        Self {
            key_expr: None,
            output_expr: None,
            value: Value::Undefined,
            result: None,
            results: QueryResults::default(),
            is_compr: false,
            rule_ref: None,
            rule_value: Value::new_object(),
            is_set: false,
            is_old_style_set: false,
            output_constness_determined: false,
            early_return: false,
        }
    }
}

impl Interpreter {
    pub fn new() -> Interpreter {
        let compiled_policy = compiled_policy::CompiledPolicyData {
            strict_builtin_errors: true, // Preserve current behavior
            ..Default::default()
        };
        Interpreter {
            compiled_policy: Rc::new(compiled_policy),

            data: Value::new_object(),
            module: None,

            current_module_path: String::default(),
            current_module_index: 0,
            query_schedule: None,
            query_module: None,
            input: Value::Undefined,

            init_data: Value::new_object(),
            with_document: Value::new_object(),
            with_functions: BTreeMap::default(),
            scopes: Vec::default(),
            contexts: Vec::default(),
            loop_var_values: Lookup::default(),

            processed: BTreeSet::default(),
            processed_paths: Value::new_object(),
            rule_values: BTreeMap::default(),
            active_rules: Vec::default(),
            builtins_cache: BTreeMap::default(),
            no_rules_lookup: false,
            traces: None,
            extensions: Map::default(),

            #[cfg(feature = "coverage")]
            coverage: Map::default(),
            #[cfg(feature = "coverage")]
            enable_coverage: false,

            gather_prints: false,
            prints: Vec::default(),
            execution_timer: ExecutionTimer::new(None),
        }
    }

    /// Create a new Interpreter from a compiled policy.
    pub fn new_from_compiled_policy(compiled_policy: Rc<CompiledPolicyData>) -> Self {
        Self {
            data: Value::new_object(),
            module: None,

            current_module_path: String::default(),
            current_module_index: 0,
            query_module: None,
            query_schedule: None,
            input: Value::Undefined,

            with_document: Value::new_object(),
            with_functions: BTreeMap::default(),
            scopes: Vec::default(),
            contexts: Vec::default(),
            loop_var_values: Lookup::default(),

            processed: BTreeSet::default(),
            processed_paths: Value::new_object(),
            rule_values: BTreeMap::default(),
            active_rules: Vec::default(),
            builtins_cache: BTreeMap::default(),
            no_rules_lookup: false,
            traces: None,

            #[cfg(feature = "coverage")]
            coverage: Map::default(),
            #[cfg(feature = "coverage")]
            enable_coverage: false,

            gather_prints: false,
            prints: Vec::default(),

            extensions: compiled_policy.extensions.clone(),
            compiled_policy: compiled_policy.clone(),
            init_data: compiled_policy
                .data
                .clone()
                .unwrap_or_else(Value::new_object),
            execution_timer: ExecutionTimer::new(None),
        }
    }

    fn reset_execution_timer_state(&mut self) {
        self.execution_timer.reset();
        if self.execution_timer.limit().is_none() {
            return;
        }
        if let Some(now) = monotonic_now() {
            self.execution_timer.start(now);
        }
    }

    fn execution_timer_tick(&mut self, work_units: u32) -> Result<()> {
        if self.execution_timer.limit().is_none() {
            return Ok(());
        }

        let Some(now) = monotonic_now() else {
            return Ok(());
        };

        self.execution_timer.tick(work_units, now)?;
        Ok(())
    }

    #[inline]
    fn check_execution_time(&mut self) -> Result<()> {
        self.execution_timer_tick(1)
    }

    fn compiled_policy_mut(&mut self) -> &mut CompiledPolicyData {
        Rc::make_mut(&mut self.compiled_policy)
    }

    pub fn set_schedule(&mut self, schedule: Option<Rc<Schedule>>) {
        self.compiled_policy_mut().schedule = schedule;
    }

    pub fn set_functions(&mut self, functions: FunctionTable) {
        self.compiled_policy_mut().functions = functions;
    }

    pub fn set_modules(&mut self, modules: Rc<Vec<Ref<Module>>>) {
        self.compiled_policy_mut().modules = modules;
    }

    pub fn set_loop_hoisting_table(&mut self, table: crate::compiler::hoist::HoistedLoopsLookup) {
        self.compiled_policy_mut().loop_hoisting_table = table;
    }

    pub fn take_loop_hoisting_table(&mut self) -> crate::compiler::hoist::HoistedLoopsLookup {
        core::mem::replace(
            &mut self.compiled_policy_mut().loop_hoisting_table,
            crate::compiler::hoist::HoistedLoopsLookup::new(),
        )
    }

    pub const fn get_data_mut(&mut self) -> &mut Value {
        &mut self.data
    }

    pub fn set_init_data(&mut self, data: Value) {
        self.init_data = data;
    }

    pub const fn get_init_data(&self) -> &Value {
        &self.init_data
    }

    pub const fn get_init_data_mut(&mut self) -> &mut Value {
        &mut self.init_data
    }

    // Used by tests.
    #[allow(dead_code)]
    pub const fn get_compiled_policy(&self) -> &Rc<CompiledPolicyData> {
        &self.compiled_policy
    }

    pub fn set_traces(&mut self, enable_tracing: bool) {
        self.traces = match enable_tracing {
            true => Some(vec![]),
            false => None,
        };
    }

    pub fn set_strict_builtin_errors(&mut self, b: bool) {
        self.compiled_policy_mut().strict_builtin_errors = b;
    }

    pub fn set_execution_timer_config(&mut self, config: Option<ExecutionTimerConfig>) {
        self.execution_timer = ExecutionTimer::new(config);
        self.reset_execution_timer_state();
    }

    pub fn set_input(&mut self, input: Value) {
        self.input = input.clone();
        // Update with_document["input"] too, in case if engine is being reused and was already prepared
        if let Ok(with_input) = Self::make_or_get_value_mut(&mut self.with_document, &["input"]) {
            *with_input = input;
        }
    }

    pub fn init_with_document(&mut self) -> Result<()> {
        *Self::make_or_get_value_mut(&mut self.with_document, &["data"])? = self.init_data.clone();
        *Self::make_or_get_value_mut(&mut self.with_document, &["input"])? = self.input.clone();

        Ok(())
    }

    pub fn clear_builtins_cache(&mut self) {
        self.builtins_cache.clear();
    }

    pub fn clean_internal_evaluation_state(&mut self) {
        self.data = self.init_data.clone();
        self.processed.clear();
        self.processed_paths = Value::new_object();
        self.ensure_loop_var_values_capacity();
        self.scopes = vec![Scope::new()];
        self.contexts = vec![];
        self.rule_values.clear();
        self.builtins_cache.clear();
        self.reset_execution_timer_state();
    }

    #[cfg(feature = "allocator-memory-limits")]
    fn memory_check(&mut self) -> Result<()> {
        let _ = self; // quiet clippy::unused_self; retained for symmetry with VM path
        crate::utils::limits::check_memory_limit_if_needed().map_err(|err| anyhow!(err))
    }

    #[cfg(not(feature = "allocator-memory-limits"))]
    const fn memory_check(&mut self) -> Result<()> {
        let _ = self; // quiet clippy::unused_self; retained for symmetry with VM path
        Ok(())
    }

    // Helper methods for working with ExprLookup
    fn set_loop_var_value(&mut self, expr: &ExprRef, value: Value) -> Result<()> {
        let module_idx = self.current_module_index;
        let expr_idx = expr.eidx();
        self.loop_var_values
            .set_checked(module_idx, expr_idx, value)
            .map_err(|err| anyhow!("internal error: loop var indices out of bounds: {err}"))
    }

    fn get_loop_var_value(&self, expr: &ExprRef) -> Result<Option<&Value>> {
        let module_idx = self.current_module_index;
        let expr_idx = expr.eidx();
        self.loop_var_values
            .get_checked(module_idx, expr_idx)
            .map_err(|err| anyhow!("internal error: loop var indices out of bounds: {err}"))
    }

    fn remove_loop_var_value(&mut self, expr: &ExprRef) {
        let module_idx = self.current_module_index;
        let expr_idx = expr.eidx();
        self.loop_var_values.clear(module_idx, expr_idx);
    }

    #[inline]
    fn loop_assignment_expr(loop_info: &HoistedLoop) -> &ExprRef {
        loop_info.loop_expr.as_ref().unwrap_or(&loop_info.value)
    }

    #[inline]
    fn loop_index_expr(loop_info: &HoistedLoop) -> Option<&ExprRef> {
        loop_info.key.as_ref().or(None)
    }

    #[inline]
    const fn loop_collection_expr(loop_info: &HoistedLoop) -> &ExprRef {
        &loop_info.collection
    }

    #[inline]
    fn loop_span(loop_info: &HoistedLoop) -> Span {
        loop_info.value.span().clone()
    }

    fn get_walk_binding_plan(&self, loop_info: &HoistedLoop) -> Result<Option<DestructuringPlan>> {
        if loop_info.loop_type != LoopType::Walk {
            return Ok(None);
        }

        if let Expr::Call { params, .. } = Self::loop_assignment_expr(loop_info).as_ref() {
            if let Some(last_param) = params.last() {
                let module_idx = self.current_module_index;
                let expr_idx = last_param.as_ref().eidx();
                let binding_plan = self
                    .compiled_policy
                    .loop_hoisting_table
                    .get_expr_binding_plan(module_idx, expr_idx)
                    .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?;

                return match binding_plan.cloned() {
                    Some(BindingPlan::Parameter {
                        destructuring_plan, ..
                    }) => Ok(Some(destructuring_plan)),
                    Some(other_plan) => bail!(
                        "internal error: expected Parameter for walk output parameter, got {:?}",
                        other_plan
                    ),
                    None => bail!("internal error: missing binding plan for walk output parameter"),
                };
            }
        }

        bail!("internal error: walk loop missing output parameter expression")
    }

    fn ensure_loop_var_values_capacity(&mut self) {
        for (module_idx, module) in self.compiled_policy.modules.iter().enumerate() {
            if let Ok(idx_u32) = u32::try_from(module_idx) {
                self.loop_var_values
                    .ensure_capacity(idx_u32, module.num_expressions);
            }
        }
        if let Some(query_module) = &self.query_module {
            let query_module_idx = self.compiled_policy.modules.len();
            let eidx = query_module.num_expressions;
            if let Ok(idx_u32) = u32::try_from(query_module_idx) {
                self.loop_var_values.ensure_capacity(idx_u32, eidx);
            }
        }
    }

    fn current_module(&self) -> Result<Ref<Module>> {
        self.module
            .clone()
            .ok_or_else(|| anyhow!("internal error: current module not set"))
    }

    fn current_scope(&mut self) -> Result<&Scope> {
        self.scopes
            .last()
            .ok_or_else(|| anyhow!("internal error: no active scope"))
    }

    fn current_scope_mut(&mut self) -> Result<&mut Scope> {
        self.scopes
            .last_mut()
            .ok_or_else(|| anyhow!("internal error: no active scope"))
    }

    #[inline(always)]
    fn add_variable(&mut self, name: &SourceStr, value: Value) -> Result<()> {
        // Only add the variable if the key is not "_"
        if name.text() != "_" {
            self.current_scope_mut()?.insert(name.clone(), value);
        }

        Ok(())
    }

    fn add_variable_or(&mut self, name: &SourceStr) -> Result<Value> {
        for scope in self.scopes.iter().rev() {
            if let Some(variable) = scope.get(name) {
                return Ok(variable.clone());
            }
        }

        self.add_variable(name, Value::Undefined)?;
        Ok(Value::Undefined)
    }

    fn eval_chained_ref_dot_or_brack(&mut self, mut expr: &ExprRef) -> Result<Value> {
        // Collect a chaing of '.field' or '["field"]'
        let mut path = vec![];
        loop {
            if let Some(v) = self.get_loop_var_value(expr)? {
                path.reverse();
                return Ok(Self::get_value_chained(v.clone(), &path[..]));
            }
            match expr.as_ref() {
                // Stop path collection upon encountering the leading variable.
                Expr::Var { span, .. } => {
                    path.reverse();
                    return self.lookup_var(span, &path[..], false);
                }
                // Accumulate chained . field accesses.
                Expr::RefDot { refr, field, .. } => {
                    expr = refr;
                    path.push(field.0.text());
                }
                Expr::RefBrack { refr, index, .. } => match index.as_ref() {
                    // refr["field"] is the same as refr.field
                    Expr::String { span, .. } => {
                        expr = refr;
                        path.push(span.text());
                    }
                    // Handle other forms of refr.
                    // Note, we have the choice to evaluate a non-string index
                    _ => {
                        path.reverse();

                        let index = self.eval_expr(index)?;

                        // Handle indexing into data.
                        if let Ok(ref_path) = get_path_string(refr, None) {
                            if get_root_var(refr)?.text() == "data" && index != Value::Undefined {
                                let index = match &index {
                                    Value::String(s) => s.to_string(),
                                    _ => index.to_string(),
                                };
                                let ref_path = if path.is_empty() {
                                    format!("{ref_path}.{index}")
                                } else {
                                    format!("{ref_path}.{index}.{}", path.join("."))
                                };
                                self.ensure_rule_evaluated(ref_path)?;
                            }
                        }

                        let obj = self.eval_expr(refr)?;

                        let mut v = obj[&index].clone();
                        // Qualified references starting with data (e.g data.p.q) can
                        // be indexed using numbers. The number will be converted to string
                        // if a matching key exists.
                        if v == Value::Undefined
                            && matches!(index, Value::Number(_))
                            && get_root_var(refr)?.text() == "data"
                        {
                            let index = index.to_string();
                            v = obj[index].clone();
                        }
                        return Ok(Self::get_value_chained(v, &path[..]));
                    }
                },
                _ => {
                    path.reverse();
                    return Ok(Self::get_value_chained(self.eval_expr(expr)?, &path[..]));
                }
            }
        }
    }

    fn eval_bool_expr(
        &mut self,
        op: &BoolOp,
        lhs_expr: &ExprRef,
        rhs_expr: &ExprRef,
    ) -> Result<Value> {
        let lhs = self.eval_expr(lhs_expr)?;
        let rhs = self.eval_expr(rhs_expr)?;

        if lhs == Value::Undefined || rhs == Value::Undefined {
            return Ok(Value::Undefined);
        }

        builtins::comparison::compare(op, &lhs, &rhs)
    }

    fn eval_bin_expr(&mut self, op: &BinOp, lhs: &ExprRef, rhs: &ExprRef) -> Result<Value> {
        let lhs_value = self.eval_expr(lhs)?;
        let rhs_value = self.eval_expr(rhs)?;

        if lhs_value == Value::Undefined || rhs_value == Value::Undefined {
            return Ok(Value::Undefined);
        }

        match op {
            BinOp::Union => builtins::sets::union(lhs, rhs, lhs_value, rhs_value),
            BinOp::Intersection => builtins::sets::intersection(lhs, rhs, lhs_value, rhs_value),
        }
    }

    fn eval_arith_expr(
        &mut self,
        span: &Span,
        op: &ArithOp,
        lhs: &ExprRef,
        rhs: &ExprRef,
    ) -> Result<Value> {
        let lhs_value = self.eval_expr(lhs)?;
        let rhs_value = self.eval_expr(rhs)?;

        if lhs_value == Value::Undefined || rhs_value == Value::Undefined {
            return Ok(Value::Undefined);
        }

        match (op, &lhs_value, &rhs_value) {
            (ArithOp::Sub, Value::Set(_), _) | (ArithOp::Sub, _, Value::Set(_)) => {
                builtins::sets::difference(lhs, rhs, lhs_value, rhs_value)
            }
            _ => builtins::numbers::arithmetic_operation(
                span,
                op,
                lhs,
                rhs,
                lhs_value,
                rhs_value,
                self.compiled_policy.strict_builtin_errors,
            ),
        }
    }

    fn eval_every(
        &mut self,
        _span: &Span,
        key: &Option<Span>,
        value: &Span,
        domain: &ExprRef,
        query: &Ref<Query>,
    ) -> Result<bool> {
        self.check_execution_time()?;
        let domain = self.eval_expr(domain)?;

        self.scopes.push(Scope::new());
        self.contexts.push(Context {
            value: Value::new_set(),
            ..Context::default()
        });
        let mut r = true;
        match domain {
            Value::Array(a) => {
                for (idx, v) in a.iter().enumerate() {
                    self.add_variable(&value.source_str(), v.clone())?;
                    if let Some(key) = key {
                        self.add_variable(&key.source_str(), Value::from(idx))?;
                    }
                    if !self.eval_query(query)? {
                        r = false;
                        break;
                    }
                }
            }
            Value::Set(s) => {
                for v in s.iter() {
                    self.add_variable(&value.source_str(), v.clone())?;
                    if let Some(key) = key {
                        self.add_variable(&key.source_str(), v.clone())?;
                    }
                    if !self.eval_query(query)? {
                        r = false;
                        break;
                    }
                }
            }
            Value::Object(o) => {
                for (k, v) in o.iter() {
                    self.add_variable(&value.source_str(), v.clone())?;
                    if let Some(key) = key {
                        self.add_variable(&key.source_str(), k.clone())?;
                    }
                    if !self.eval_query(query)? {
                        r = false;
                        break;
                    }
                }
            }
            _ => {
                r = false;
            }
        };
        self.contexts.pop();
        self.scopes.pop();
        Ok(r)
    }

    /// Execute a destructuring plan against a value, binding variables as needed
    pub fn execute_destructuring_plan(
        &mut self,
        plan: &DestructuringPlan,
        value: &Value,
    ) -> Result<Value> {
        self.check_execution_time()?;
        if value == &Value::Undefined {
            return Ok(Value::Undefined);
        }

        fn compare(v1: &Value, v2: &Value) -> Result<Value> {
            if v1 != v2 || v1 == &Value::Undefined {
                Ok(Value::Undefined)
            } else {
                Ok(Value::from(true))
            }
        }

        match plan {
            DestructuringPlan::Var(var_name) => {
                // Bind the variable to the value
                self.add_variable(&var_name.source_str(), value.clone())?;
                Ok(Value::Bool(true))
            }

            DestructuringPlan::Ignore => Ok(Value::Bool(true)),

            DestructuringPlan::EqualityExpr(expected_expr) => {
                let expected = self.eval_expr(expected_expr)?;
                compare(value, &expected)
            }

            DestructuringPlan::EqualityValue(expected) => Ok(Value::from(value == expected)),

            DestructuringPlan::Array { element_plans } => {
                // Value must be an array with matching length
                if let Value::Array(arr) = value {
                    if arr.len() != element_plans.len() {
                        return Ok(Value::Undefined);
                    }

                    // Recursively execute each element plan
                    for (i, element_plan) in element_plans.iter().enumerate() {
                        let Some(element) = arr.get(i) else {
                            return Ok(Value::Undefined);
                        };

                        if self.execute_destructuring_plan(element_plan, element)?
                            != Value::from(true)
                        {
                            return Ok(Value::Undefined);
                        }
                    }
                    Ok(Value::from(true))
                } else {
                    Ok(Value::Undefined) // Not an array
                }
            }

            DestructuringPlan::Object {
                field_plans,
                dynamic_fields,
            } => {
                // Value must be an object with matching fields
                if let Value::Object(obj) = value {
                    // Check that all required fields are present and match
                    for (key, field_plan) in field_plans {
                        if let Some(field_value) = obj.get(key) {
                            if self.execute_destructuring_plan(field_plan, field_value)?
                                != Value::from(true)
                            {
                                return Ok(Value::Undefined);
                            }
                        } else {
                            return Ok(Value::Undefined); // Required field missing
                        }
                    }

                    if !dynamic_fields.is_empty() {
                        for (key_expr, field_plan) in dynamic_fields {
                            let key_value = self.eval_expr(key_expr)?;
                            if key_value == Value::Undefined {
                                return Ok(Value::Undefined);
                            }

                            if let Some(field_value) = obj.get(&key_value) {
                                if self.execute_destructuring_plan(field_plan, field_value)?
                                    != Value::from(true)
                                {
                                    return Ok(Value::Undefined);
                                }
                            } else {
                                return Ok(Value::Undefined);
                            }
                        }
                    }
                    Ok(Value::from(true))
                } else {
                    Ok(Value::Undefined) // Not an object
                }
            }
        }
    }

    fn execute_assignment_plan(&mut self, plan: &AssignmentPlan) -> Result<Value> {
        self.check_execution_time()?;
        match plan {
            AssignmentPlan::ColonEquals {
                lhs_expr: _,
                rhs_expr,
                lhs_plan,
            } => {
                // For :=, evaluate RHS and bind to LHS pattern
                let rhs_value = self.eval_expr(rhs_expr)?;
                self.execute_destructuring_plan(lhs_plan, &rhs_value)
            }

            AssignmentPlan::EqualsBindLeft {
                lhs_expr: _,
                rhs_expr,
                lhs_plan,
            } => {
                // For = with LHS binding, evaluate RHS and bind to LHS pattern
                let rhs_value = self.eval_expr(rhs_expr)?;
                self.execute_destructuring_plan(lhs_plan, &rhs_value)
            }

            AssignmentPlan::EqualsBindRight {
                lhs_expr,
                rhs_expr: _,
                rhs_plan,
            } => {
                // For = with RHS binding, evaluate LHS and bind to RHS pattern
                let lhs_value = self.eval_expr(lhs_expr)?;
                self.execute_destructuring_plan(rhs_plan, &lhs_value)
            }

            AssignmentPlan::EqualsBothSides {
                lhs_expr: _,
                rhs_expr: _,
                element_pairs,
            } => {
                // For = with both sides having patterns, execute each flattened pair
                for (value_expr, pattern_plan) in element_pairs {
                    let value = self.eval_expr(value_expr)?;
                    if self.execute_destructuring_plan(pattern_plan, &value)? != Value::from(true) {
                        return Ok(Value::Undefined);
                    }
                }
                Ok(Value::from(true))
            }

            AssignmentPlan::WildcardMatch {
                lhs_expr,
                rhs_expr,
                wildcard_side,
            } => match wildcard_side {
                WildcardSide::Both => Ok(Value::Bool(true)),
                WildcardSide::Lhs => {
                    let rhs_value = self.eval_expr(rhs_expr)?;
                    if rhs_value == Value::Undefined {
                        Ok(Value::Undefined)
                    } else {
                        Ok(Value::Bool(true))
                    }
                }
                WildcardSide::Rhs => {
                    let lhs_value = self.eval_expr(lhs_expr)?;
                    if lhs_value == Value::Undefined {
                        Ok(Value::Undefined)
                    } else {
                        Ok(Value::Bool(true))
                    }
                }
            },

            AssignmentPlan::EqualityCheck { lhs_expr, rhs_expr } => {
                let lhs_value = self.eval_expr(lhs_expr)?;
                let rhs_value = self.eval_expr(rhs_expr)?;

                if lhs_value == Value::Undefined || rhs_value == Value::Undefined {
                    return Ok(Value::Undefined);
                }

                if lhs_value == rhs_value {
                    Ok(Value::Bool(true))
                } else {
                    Ok(Value::Undefined)
                }
            }
        }
    }

    fn eval_some_in(
        &mut self,
        _span: &Span,
        _key_expr: &Option<ExprRef>,
        _value_expr: &ExprRef,
        collection: &ExprRef,
        stmts: &[&LiteralStmt],
    ) -> Result<bool> {
        self.check_execution_time()?;
        let scope_saved = self.current_scope()?.clone();
        let mut count: usize = 0;

        // Fetch the binding plan for this some..in expression
        let module_idx = self.current_module_index;
        let expr_idx = collection.as_ref().eidx();

        let binding_plan = self
            .compiled_policy
            .loop_hoisting_table
            .get_expr_binding_plan(module_idx, expr_idx)
            .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?;

        let Some(BindingPlan::SomeIn {
            key_plan,
            value_plan,
            ..
        }) = binding_plan.cloned()
        else {
            bail!("internal error: missing binding plan for some..in expression");
        };

        match self.eval_expr(collection)? {
            Value::Array(a) => {
                for (idx, value) in a.iter().enumerate() {
                    *self.current_scope_mut()? = scope_saved.clone();

                    let mut success = if let Some(key_plan) = &key_plan {
                        self.execute_destructuring_plan(key_plan, &Value::from(idx))?
                            == Value::from(true)
                    } else {
                        true
                    };

                    // Execute value binding
                    success = success
                        && self.execute_destructuring_plan(&value_plan, value)?
                            == Value::from(true);

                    if !success {
                        *self.current_scope_mut()? = scope_saved.clone();
                        continue;
                    }

                    let mut should_break = false;
                    if self.eval_stmts(stmts)? {
                        count = count.saturating_add(1);
                        if let Some(ctx) = self.contexts.last() {
                            if ctx.early_return {
                                should_break = true;
                            }
                        }
                    }
                    *self.current_scope_mut()? = scope_saved.clone();

                    if should_break {
                        break;
                    }
                }
            }
            Value::Set(s) => {
                for value in s.iter() {
                    *self.current_scope_mut()? = scope_saved.clone();

                    let mut success = if let Some(key_plan) = &key_plan {
                        self.execute_destructuring_plan(key_plan, value)? == Value::from(true)
                    } else {
                        true
                    };

                    // Execute value binding
                    success = success
                        && self.execute_destructuring_plan(&value_plan, value)?
                            == Value::from(true);

                    if !success {
                        *self.current_scope_mut()? = scope_saved.clone();
                        continue;
                    }

                    let mut should_break = false;
                    if self.eval_stmts(stmts)? {
                        count = count.saturating_add(1);
                        if let Some(ctx) = self.contexts.last() {
                            if ctx.early_return {
                                should_break = true;
                            }
                        }
                    }
                    *self.current_scope_mut()? = scope_saved.clone();

                    if should_break {
                        break;
                    }
                }
            }

            Value::Object(o) => {
                for (key, value) in o.iter() {
                    *self.current_scope_mut()? = scope_saved.clone();

                    let mut success = if let Some(key_plan) = &key_plan {
                        self.execute_destructuring_plan(key_plan, key)? == Value::from(true)
                    } else {
                        true
                    };

                    // Execute value binding
                    success = success
                        && self.execute_destructuring_plan(&value_plan, value)?
                            == Value::from(true);

                    if !success {
                        *self.current_scope_mut()? = scope_saved.clone();
                        continue;
                    }

                    let mut should_break = false;
                    if self.eval_stmts(stmts)? {
                        count = count.saturating_add(1);
                        if let Some(ctx) = self.contexts.last() {
                            if ctx.early_return {
                                should_break = true;
                            }
                        }
                    }
                    *self.current_scope_mut()? = scope_saved.clone();

                    if should_break {
                        break;
                    }
                }
            }
            Value::Undefined => (),
            v => {
                bail!(collection.span().error(
                    format!("`some .. in collection` expects array/set/object. Got `{v}`").as_str()
                ))
            }
        }

        Ok(count > 0)
    }

    fn make_expression_result(span: &Span, v: &Value) -> Expression {
        Expression {
            value: v.clone(),
            text: span.text().to_string().into(),
            location: Location {
                row: span.line,
                col: span.col,
            },
        }
    }

    fn eval_stmt_impl(&mut self, stmt: &LiteralStmt, stmts: &[&LiteralStmt]) -> Result<bool> {
        self.memory_check()?;
        self.check_execution_time()?;
        Ok(match &stmt.literal {
            Literal::Expr { span, expr, .. } => {
                let value = match expr.as_ref() {
                    Expr::Call {
                        span: call_span,
                        fcn,
                        params,
                        ..
                    } => self.eval_call(
                        call_span,
                        expr,
                        fcn,
                        params,
                        get_extra_arg(
                            expr,
                            Some(self.current_module_path.as_str()),
                            &self.compiled_policy.functions,
                        ),
                        true,
                    )?,
                    _ => self.eval_expr(expr)?,
                };

                if let Some(ctx) = self.contexts.last_mut() {
                    if let Some(result) = &mut ctx.result {
                        if value != Value::Undefined {
                            result
                                .expressions
                                .push(Self::make_expression_result(span, &value));
                        } else {
                            result.bindings = Value::new_object();
                            result.expressions.clear();
                        }
                    }
                }

                if let Value::Bool(bool) = value {
                    bool
                } else {
                    // panic!();
                    // TODO: confirm this
                    // For non-booleans, treat anything other than undefined as true
                    value != Value::Undefined
                }
            }
            Literal::NotExpr { span, expr, .. } => {
                let value = match expr.as_ref() {
                    // Extra parameter is allowed; but a return argument is not allowed.
                    Expr::Call {
                        span: call_span,
                        fcn,
                        params,
                        ..
                    } => self.eval_call(
                        call_span,
                        expr,
                        fcn,
                        params,
                        get_extra_arg(
                            expr,
                            Some(self.current_module_path.as_str()),
                            &self.compiled_policy.functions,
                        ),
                        false,
                    )?,
                    _ => self.eval_expr(expr)?,
                };

                if let Some(ctx) = self.contexts.last_mut() {
                    if let Some(result) = &mut ctx.result {
                        result
                            .expressions
                            .push(Self::make_expression_result(span, &Value::Bool(true)));
                    }
                }

                // https://github.com/open-policy-agent/opa/issues/1622#issuecomment-520547385
                matches!(value, Value::Bool(false) | Value::Undefined)
            }
            Literal::SomeVars { span, vars, .. } => {
                for var in vars {
                    let name = var.source_str();
                    if self.current_scope()?.get(&name).is_some() {
                        bail!("duplicated definition of local variable {}", name);
                    }
                    self.add_variable_or(&name)?;
                }
                if let Some(ctx) = self.contexts.last_mut() {
                    if let Some(result) = &mut ctx.result {
                        result
                            .expressions
                            .push(Self::make_expression_result(span, &Value::Bool(true)));
                    }
                }
                true
            }
            Literal::SomeIn {
                span,
                key,
                value,
                collection,
            } => {
                if let Some(ctx) = self.contexts.last_mut() {
                    if let Some(result) = &mut ctx.result {
                        result
                            .expressions
                            .push(Self::make_expression_result(span, &Value::Bool(true)));
                    }
                }
                self.eval_some_in(span, key, value, collection, stmts)?
            }
            Literal::Every {
                span,
                key,
                value,
                domain,
                query,
            } => {
                if let Some(ctx) = self.contexts.last_mut() {
                    if let Some(result) = &mut ctx.result {
                        result
                            .expressions
                            .push(Self::make_expression_result(span, &Value::Bool(true)));
                    }
                }
                self.eval_every(span, key, value, domain, query)?
            }
        })
    }

    fn apply_with_modifiers(&mut self, stmt: &LiteralStmt) -> Result<(Option<State>, bool)> {
        if !stmt.with_mods.is_empty() {
            // Save state;
            let with_document = self.with_document.clone();
            let input = self.input.clone();
            let data = self.data.clone();
            let processed = self.processed.clone();
            let with_functions = self.with_functions.clone();
            let rule_values = self.rule_values.clone();

            self.processed.clear();
            let processed_paths =
                core::mem::replace(&mut self.processed_paths, Value::new_object());
            self.rule_values.clear();

            let mut skip_exec = false;
            // Apply with modifiers.
            for wm in &stmt.with_mods {
                let path = Parser::get_path_ref_components(&wm.refr)?;
                let path: Vec<&str> = path.iter().map(|s| s.text()).collect();
                let mut target = path.join(".");

                let mut target_is_function = self.lookup_function_by_name(&target).is_some()
                    || Self::is_builtin(wm.refr.span(), &target);

                if !target_is_function
                    && !target.starts_with("data.")
                    && !target.starts_with("input.")
                    && target != "input"
                {
                    // target must be a function.
                    if self.lookup_function_by_name(&target).is_none()
                        && !Self::is_builtin(wm.refr.span(), &target)
                    {
                        // Prefix target with current module path.
                        target = format!("{}.{}", self.current_module_path, target);
                        if self.lookup_function_by_name(&target).is_none() {
                            bail!(wm.refr.span().error("undefined rule"));
                        }
                        target_is_function = true;
                    }
                }

                if target_is_function {
                    match self.eval_expr(&wm.r#as) {
                        Ok(v) if v != Value::Undefined => {
                            // Function replaced by value.
                            self.with_functions
                                .insert(target, FunctionModifier::Value(v));
                        }
                        _ => {
                            // Function replaced by another function.
                            // Lookup by with current module path prefixed.
                            let mut function_path =
                                get_path_string(&wm.r#as, Some(&self.current_module_path))?;
                            if self.lookup_function_by_name(&function_path).is_none() {
                                // Lookup without current module path prefixed.
                                function_path = get_path_string(&wm.r#as, None)?;
                                if self.lookup_function_by_name(&function_path).is_none()
                                    && !Self::is_builtin(wm.r#as.span(), &function_path)
                                {
                                    // bail!(wm.r#as.span().error("could not evaluate expression"));
                                    skip_exec = true;
                                }
                            }
                            self.with_functions
                                .insert(target, FunctionModifier::Function(function_path));
                        }
                    }
                } else {
                    let value = self.eval_expr(&wm.r#as)?;
                    skip_exec = value == Value::Undefined;
                    let Some(first) = path.first() else {
                        bail!(wm.refr.span().error("empty path in with modifier"));
                    };
                    if *first == "input" || *first == "data" {
                        // Override existing values in case of conflict.
                        let mut obj = &mut self.with_document;
                        for p in &path {
                            if !matches!(obj, Value::Object(_)) {
                                *obj = Value::new_object();
                            }

                            obj = obj
                                .as_object_mut()?
                                .entry(Value::String(p.to_string().into()))
                                .or_insert(Value::new_object());
                        }
                        *obj = value;
                        // Mark modified rules as processed.
                        if let Some(rules) = self.compiled_policy.rules.get(&target) {
                            for r in rules {
                                self.processed.insert(r.clone());
                            }
                        }
                    } else {
                        bail!(wm.refr.span().error("not a valid target for with modifier"));
                    }
                }
            }

            self.data = self.with_document["data"].clone();
            self.input = self.with_document["input"].clone();
            Ok((
                Some((
                    with_document,
                    input,
                    data,
                    processed,
                    processed_paths,
                    with_functions,
                    rule_values,
                )),
                skip_exec,
            ))
        } else {
            Ok((None, false))
        }
    }

    fn restore_state(&mut self, saved_state: Option<State>) -> Result<()> {
        if let Some(s) = saved_state {
            (
                self.with_document,
                self.input,
                self.data,
                self.processed,
                self.processed_paths,
                self.with_functions,
                self.rule_values,
            ) = s;
        }
        Ok(())
    }

    fn eval_stmt(&mut self, stmt: &LiteralStmt, stmts: &[&LiteralStmt]) -> Result<bool> {
        let (saved_state, skip_exec) = self.apply_with_modifiers(stmt)?;
        let r = if !skip_exec {
            self.eval_stmt_impl(stmt, stmts)
        } else {
            Ok(false)
        };

        self.restore_state(saved_state)?;

        r
    }

    fn clear_scope(scope: &mut Scope) {
        // Set each value to undefined. This is equivalent to removing the key.
        for (_, v) in scope.iter_mut() {
            *v = Value::Undefined;
        }
    }

    fn eval_stmts_in_loop(
        &mut self,
        stmts: &[&LiteralStmt],
        loops: &[HoistedLoop],
    ) -> Result<bool> {
        self.memory_check()?;
        self.check_execution_time()?;
        if loops.is_empty() {
            if let Some((first_stmt, tail_stmts)) = stmts.split_first() {
                // Evaluate the current statement whose loop expressions have been hoisted.
                if self.eval_stmt(first_stmt, tail_stmts)? {
                    if !matches!(&first_stmt.literal, Literal::SomeIn { .. }) {
                        self.eval_stmts(tail_stmts)
                    } else {
                        Ok(true)
                    }
                } else {
                    Ok(false)
                }
            } else {
                self.eval_stmts(stmts)
            }
        } else {
            let (loop_info, loop_tail) = loops
                .split_first()
                .ok_or_else(|| anyhow!("internal error: expected loop info"))?;
            let (first_stmt, _tail_stmts) = stmts
                .split_first()
                .ok_or_else(|| anyhow!("internal error: expected statements for loop"))?;
            let mut result = false;

            // Apply with modifiers before evaluating the loop expression.
            let (saved_state, _) = self.apply_with_modifiers(first_stmt)?;

            let collection_expr = Self::loop_collection_expr(loop_info).clone();
            let loop_value = if let Expr::Call {
                span, fcn, params, ..
            } = collection_expr.as_ref()
            {
                // Handle walk(obj, output_param)
                let extra_arg = get_extra_arg(
                    &collection_expr,
                    Some(self.current_module_path.as_str()),
                    &self.compiled_policy.functions,
                );
                // If there is an extra arg, ignore it while computing the loop value.
                let params_slice: &[ExprRef] = if extra_arg.is_some() {
                    let (_, prefix) = params
                        .split_last()
                        .ok_or_else(|| anyhow!("internal error: expected params"))?;
                    prefix
                } else {
                    params.as_slice()
                };
                self.eval_call_impl(span, &collection_expr, fcn, params_slice)?
            } else {
                self.eval_expr(&collection_expr)?
            };

            // Restore with modifiers.
            // TODO: Delay this restore so that the stmt doesn't have to apply with modifiers again.
            self.restore_state(saved_state)?;

            // If the loop's index variable h<as already been assigned a value
            // (this can happen if the same index is used for two different collections),
            // then evaluate statements only if the index applies to this collection.
            if let Some(walk_plan) = self.get_walk_binding_plan(loop_info)? {
                let loop_target_expr = Self::loop_assignment_expr(loop_info);
                self.scopes.push(Scope::default());

                let query_result = self.get_current_context()?.result.clone();

                let mut walk_result = false;
                match loop_value {
                    Value::Array(items) => {
                        for item in items.iter() {
                            self.memory_check()?;
                            self.set_loop_var_value(loop_target_expr, item.clone())?;

                            if self.execute_destructuring_plan(&walk_plan, item)?
                                == Value::from(true)
                            {
                                walk_result =
                                    self.eval_stmts_in_loop(stmts, loop_tail)? || walk_result;
                            }

                            Self::clear_scope(self.current_scope_mut()?);
                            if let Some(ctx) = self.contexts.last_mut() {
                                ctx.result.clone_from(&query_result);
                                if ctx.early_return {
                                    break;
                                }
                            }
                        }
                    }
                    Value::Undefined => (),
                    other => {
                        let span = Self::loop_span(loop_info);
                        bail!(span
                            .error(format!("walk expected array result, got `{other}`").as_str()));
                    }
                }

                self.scopes.pop();
                self.remove_loop_var_value(loop_target_expr);
                return Ok(walk_result);
            }

            let index_expr = Self::loop_index_expr(loop_info);
            if let Some(Expr::Var {
                span: index_var, ..
            }) = index_expr.map(|r| r.as_ref())
            {
                if let Some(idx) = self.lookup_local_var(&index_var.source_str()) {
                    if loop_value[&idx] != Value::Undefined {
                        result = self.eval_stmts_in_loop(stmts, loop_tail)? || result;
                        return Ok(result);
                    } else if idx != Value::Undefined {
                        // The index is not valid for this collection.
                        return Ok(false);
                    }
                }
            }

            let index_plan = if let Some(index) = index_expr {
                let module_idx = self.current_module_index;
                let expr_idx = index.as_ref().eidx();
                let plan = self
                    .compiled_policy
                    .loop_hoisting_table
                    .get_expr_binding_plan(module_idx, expr_idx)
                    .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?;

                match plan.cloned() {
                    Some(BindingPlan::LoopIndex {
                        destructuring_plan, ..
                    }) => destructuring_plan,
                    Some(other_plan) => {
                        bail!("internal error: expected LoopIndex for loop index expression, got {:?}", other_plan);
                    }
                    None => {
                        bail!("internal error: no binding plan found for loop index expression");
                    }
                }
            } else {
                bail!("internal error: no binding plan found for loop index expression");
            };

            // Create a new scope.
            self.scopes.push(Scope::default());

            let query_result = self.get_current_context()?.result.clone();
            let loop_target_expr = Self::loop_assignment_expr(loop_info);
            match loop_value {
                Value::Array(items) => {
                    for (idx, v) in items.iter().enumerate() {
                        self.memory_check()?;
                        self.set_loop_var_value(loop_target_expr, v.clone())?;

                        if self.execute_destructuring_plan(&index_plan, &Value::from(idx))?
                            == Value::from(true)
                        {
                            result = self.eval_stmts_in_loop(stmts, loop_tail)? || result;
                        }

                        Self::clear_scope(self.current_scope_mut()?);
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result.clone_from(&query_result);
                            if ctx.early_return {
                                break;
                            }
                        }
                    }

                    self.remove_loop_var_value(loop_target_expr);
                }
                Value::Set(items) => {
                    for v in items.iter() {
                        self.memory_check()?;
                        self.set_loop_var_value(loop_target_expr, v.clone())?;

                        // For sets, index is also the value.
                        if self.execute_destructuring_plan(&index_plan, v)? == Value::from(true) {
                            result = self.eval_stmts_in_loop(stmts, loop_tail)? || result;
                        }

                        Self::clear_scope(self.current_scope_mut()?);
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result.clone_from(&query_result);
                            if ctx.early_return {
                                break;
                            }
                        }
                    }
                    self.remove_loop_var_value(loop_target_expr);
                }
                Value::Object(obj) => {
                    for (k, v) in obj.iter() {
                        self.memory_check()?;
                        self.set_loop_var_value(loop_target_expr, v.clone())?;
                        // For objects, index is key.
                        if self.execute_destructuring_plan(&index_plan, k)? == Value::from(true) {
                            result = self.eval_stmts_in_loop(stmts, loop_tail)? || result;
                        }

                        Self::clear_scope(self.current_scope_mut()?);
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result.clone_from(&query_result);
                            if ctx.early_return {
                                break;
                            }
                        }
                    }
                    self.remove_loop_var_value(loop_target_expr);
                }
                Value::Undefined => {
                    result = false;
                }
                _ => {
                    // The item is not a collection.
                    result = false;
                }
            }

            self.scopes.pop();

            // Return true if at least on iteration returned true
            Ok(result)
        }
    }

    fn eval_rule_ref(&mut self, rule_refr: &ExprRef) -> Result<Vec<Value>> {
        self.check_execution_time()?;
        let mut comps = vec![];
        let mut expr = rule_refr;
        loop {
            match expr.as_ref() {
                Expr::Var { span: v, .. } => {
                    comps.push(Value::String(v.text().into()));
                    break;
                }
                Expr::RefBrack {
                    refr: nested_refr,
                    index,
                    ..
                } => {
                    comps.push(self.eval_expr(index)?);
                    expr = nested_refr;
                }
                Expr::RefDot {
                    refr: nested_refr,
                    field,
                    ..
                } => {
                    comps.push(Value::String(field.0.text().into()));
                    expr = nested_refr;
                }
                _ => {
                    bail!(expr.span().error("not a valid rule ref"));
                }
            }
        }
        comps.reverse();
        Ok(comps)
    }

    fn update_rule_value(
        &mut self,
        span: &Span,
        path: Vec<Value>,
        mut value: Value,
        is_set: bool,
    ) -> Result<()> {
        // If rule's value already exists in initial document, prefer it.
        {
            let mut init_obj = &self.init_data;
            for p in path.iter() {
                init_obj = &init_obj[p];
            }

            if init_obj != &Value::Undefined {
                return Ok(());
            }
        }

        let mut obj = &mut self.data;
        let len = path.len();
        for (idx, p) in path.into_iter().enumerate() {
            // Stop at the first undefined component in the path
            if p == Value::Undefined {
                break;
            }
            if idx == len.saturating_sub(1) {
                // last key.
                if is_set {
                    let set = obj
                        .as_object_mut()
                        .map_err(|_| anyhow!(span.error("previous value is not an object")))?
                        .entry(p)
                        .or_insert(Value::new_set())
                        .as_set_mut()
                        .map_err(|_| anyhow!(span.error("previous value is not a set")))?;
                    set.append(value.as_set_mut()?);
                } else {
                    let obj = obj
                        .as_object_mut()
                        .map_err(|_| anyhow!(span.error("previous value is not an object")))?;
                    match obj.entry(p) {
                        BTreeMapEntry::Vacant(v) => {
                            if value != Value::Undefined {
                                v.insert(value);
                            } else {
                                // TODO: clean this assumption between Undefined vs Object.
                                v.insert(Value::new_object());
                            }
                        }
                        BTreeMapEntry::Occupied(o) => {
                            if o.get() != &value && value != Value::Undefined {
                                bail!(span
                                    .error("complete rules should not produce multiple outputs"))
                            }
                        }
                    }
                }
                break;
            } else {
                obj = obj
                    .as_object_mut()
                    .map_err(|_| anyhow!(span.error("previous value is not an object")))?
                    .entry(p)
                    .or_insert(Value::new_object());
            }
        }
        Ok(())
    }

    // A ref is a constant ref, if it does not contain any local variables.
    // For now, we restrict constant refs to those that contain only simple literals.
    fn is_constant_ref(mut expr: &Ref<Expr>) -> Result<bool> {
        loop {
            match expr.as_ref() {
                Expr::Var { .. } => break,
                Expr::RefDot { refr, .. } => expr = refr,
                Expr::RefBrack { refr, index, .. } if Self::is_simple_literal(index)? => {
                    expr = refr;
                }
                _ => return Ok(false),
            }
        }
        Ok(true)
    }

    fn is_simple_literal(expr: &Ref<Expr>) -> Result<bool> {
        Ok(matches!(
            expr.as_ref(),
            Expr::String { .. }
                | Expr::RawString { .. }
                | Expr::Bool { .. }
                | Expr::Null { .. }
                | Expr::Number { .. }
        ))
    }

    // A rule's output expression is constant if it does not contain local variables.
    // For now, we restrict output expressions to those that contain only simple literals.
    fn is_constant_output(key_expr: &Option<Ref<Expr>>, output_expr: &Ref<Expr>) -> Result<bool> {
        let is_const = if let Some(key_expr) = key_expr {
            Self::is_simple_literal(key_expr)?
        } else {
            true
        };
        Ok(is_const && Self::is_simple_literal(output_expr)?)
    }

    fn eval_output_expr_in_loop(&mut self, loops: &[HoistedLoop]) -> Result<bool> {
        self.check_execution_time()?;
        if loops.is_empty() {
            let (key_expr, output_expr) = self.get_exprs_from_context()?;

            let ctx = self.get_current_context()?;
            let (is_set, is_old_style_set, is_rule, constness_determined) = (
                ctx.is_set,
                ctx.is_old_style_set,
                !ctx.is_compr,
                ctx.output_constness_determined,
            );

            if let Some(rule_ref) = ctx.rule_ref.clone() {
                let mut is_const_rule = if is_rule && !constness_determined {
                    Self::is_constant_ref(&rule_ref)?
                } else {
                    // Constness has already been determined or is not a rule.
                    // Treat the expression as not constant.
                    false
                };

                let mut comps = self.eval_rule_ref(&rule_ref)?;
                if let Some(ke) = &key_expr {
                    comps.push(self.eval_expr(ke)?);
                }
                let output = if let Some(oe) = &output_expr {
                    // Rule is constant only if its ref, key and output are constant.
                    is_const_rule = is_const_rule && Self::is_constant_output(&key_expr, oe)?;
                    self.eval_expr(oe)?
                } else if is_old_style_set && !comps.is_empty() {
                    // Rule's constness is determined only by its ref.
                    let output = comps
                        .last()
                        .cloned()
                        .ok_or_else(|| anyhow!("internal error: missing comps output"))?;
                    comps.pop();
                    output
                } else {
                    // Rule's constness is determined only by its ref.
                    Value::Bool(true)
                };

                let comps_defined = comps.iter().all(|v| v != &Value::Undefined);
                let ctx_mut = self.get_current_context_mut()?;

                if is_const_rule {
                    ctx_mut.early_return = true;
                }
                if is_rule {
                    ctx_mut.output_constness_determined = true;
                }

                if output == Value::Undefined || !comps_defined {
                    ctx_mut.rule_value = Value::Undefined;
                    return Ok(false);
                }

                if is_set {
                    // Ensure that set rule is created even if the element is undefined.
                    let set = ctx_mut
                        .rule_value
                        .as_object_mut()?
                        .entry(Value::from_array(comps))
                        .or_insert(Value::new_set());
                    if output != Value::Undefined {
                        set.as_set_mut()?.insert(output);
                        return Ok(true);
                    }
                    return Ok(false);
                }

                // Non-set rule.
                match ctx_mut
                    .rule_value
                    .as_object_mut()?
                    .entry(Value::from_array(comps))
                {
                    BTreeMapEntry::Vacant(v) => {
                        v.insert(output);
                    }
                    BTreeMapEntry::Occupied(o) if o.get() != &output => bail!(rule_ref
                        .span()
                        .error("rules must not produce multiple outputs")),
                    _ => {
                        // Rule produced same value.
                    }
                }

                return Ok(true);
            }

            match (key_expr, output_expr) {
                (Some(ke), Some(oe)) => {
                    let key = self.eval_expr(&ke)?;
                    let value = self.eval_expr(&oe)?;

                    let ctx_mut = self.get_current_context_mut()?;
                    if key != Value::Undefined && value != Value::Undefined {
                        let map = ctx_mut.value.as_object_mut()?;
                        match map.get(&key) {
                            Some(pv) if *pv != value => {
                                let span = ke.span();
                                return Err(span.source.error(
                                    span.line,
                                    span.col,
                                    format!(
					"value for key `{}` generated multiple times: `{}` and `{}`",
					serde_json::to_string_pretty(&key).map_err(anyhow::Error::msg)?,
					serde_json::to_string_pretty(&pv).map_err(anyhow::Error::msg)?,
					serde_json::to_string_pretty(&value).map_err(anyhow::Error::msg)?,
                                    )
                                    .as_str(),
                                ));
                            }
                            _ => map.insert(key, value),
                        };
                    } else {
                        match &ctx_mut.value {
                            Value::Object(_) => (),
                            _ => ctx_mut.value = Value::Undefined,
                        }
                    };
                }
                (None, Some(oe)) => {
                    let output = self.eval_expr(&oe)?;
                    let ctx_mut = self.get_current_context_mut()?;
                    if output != Value::Undefined {
                        match &mut ctx_mut.value {
                            Value::Array(a) => {
                                Rc::make_mut(a).push(output);
                            }
                            Value::Set(ref mut s) => {
                                Rc::make_mut(s).insert(output);
                            }
                            a => bail!("internal error: invalid context value {a}"),
                        }
                    } else if !ctx_mut.is_compr {
                        match &ctx_mut.value {
                            Value::Set(_) => (),
                            _ => ctx_mut.value = Value::Undefined,
                        }
                    }
                }
                // No output expression.
                // TODO: should we just push a Bool(true)?
                _ => (),
            }

            // If a query snippet is being run, gather results.
            let result_opt = {
                let current_ctx = self.get_current_context_mut()?;
                current_ctx.result.clone()
            };

            if let Some(mut current_result) = result_opt {
                if let Some(scope) = self.scopes.last() {
                    for (name, value) in scope.iter() {
                        current_result
                            .bindings
                            .as_object_mut()?
                            .insert(Value::String(name.to_string().into()), value.clone());
                    }
                }
                if current_result.expressions.len() == 1 // Single expression query
                    || current_result // Multi expression query where no value is false
                       .expressions
                       .iter()
                       .all(|v| v.value != Value::Undefined && v.value != Value::Bool(false))
                       && !current_result.expressions.is_empty()
                {
                    let ctx_mut = self.get_current_context_mut()?;
                    ctx_mut.results.result.push(current_result);
                }
            }

            return Ok(true);
        }

        // Try out values in current loop expr.
        let (loop_info, loop_tail) = loops
            .split_first()
            .ok_or_else(|| anyhow!("internal error: expected loop info"))?;
        let mut result = false;
        let loop_target_expr = Self::loop_assignment_expr(loop_info);
        match self.eval_expr(Self::loop_collection_expr(loop_info))? {
            Value::Array(items) => {
                for v in items.iter() {
                    self.set_loop_var_value(loop_target_expr, v.clone())?;
                    result = self.eval_output_expr_in_loop(loop_tail)? || result;
                }
            }
            Value::Set(items) => {
                for v in items.iter() {
                    self.set_loop_var_value(loop_target_expr, v.clone())?;
                    result = self.eval_output_expr_in_loop(loop_tail)? || result;
                }
            }
            Value::Object(obj) => {
                for (_, v) in obj.iter() {
                    self.set_loop_var_value(loop_target_expr, v.clone())?;
                    result = self.eval_output_expr_in_loop(loop_tail)? || result;
                }
            }
            _ => {
                let span = Self::loop_span(loop_info);
                return Err(span
                    .source
                    .error(span.line, span.col, "item cannot be indexed"));
            }
        }
        self.remove_loop_var_value(loop_target_expr);
        Ok(result)
    }

    fn get_current_context(&self) -> Result<&Context> {
        match self.contexts.last() {
            Some(ctx) => Ok(ctx),
            _ => bail!("internal error: no active context found"),
        }
    }

    fn get_current_context_mut(&mut self) -> Result<&mut Context> {
        match self.contexts.last_mut() {
            Some(ctx) => Ok(ctx),
            _ => bail!("internal error: no active context found"),
        }
    }

    fn get_exprs_from_context(&self) -> Result<ContextExprs> {
        let ctx = self.get_current_context()?;
        Ok((ctx.key_expr.clone(), ctx.output_expr.clone()))
    }

    fn eval_output_expr(&mut self) -> Result<bool> {
        self.check_execution_time()?;
        // Evaluate output expression after all the statements have been executed.

        let (key_expr, output_expr) = self.get_exprs_from_context()?;
        let mut loops: Vec<HoistedLoop> = Vec::new();

        // Get pre-computed loops for key expression
        if let Some(ke) = &key_expr {
            match self
                .compiled_policy
                .loop_hoisting_table
                .get_expr_loops(self.current_module_index, ke.as_ref().eidx())
                .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?
            {
                Some(hoisted_loops) => {
                    loops.extend(hoisted_loops.clone());
                }
                None => {
                    bail!(ke.span().error("Loop hoisting information not found for key expression. This is likely a bug in the compilation phase."));
                }
            }
        }

        // Get pre-computed loops for output expression
        if let Some(oe) = &output_expr {
            match self
                .compiled_policy
                .loop_hoisting_table
                .get_expr_loops(self.current_module_index, oe.as_ref().eidx())
                .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?
            {
                Some(hoisted_loops) => {
                    loops.extend(hoisted_loops.clone());
                }
                None => {
                    bail!(oe.span().error("Loop hoisting information not found for output expression. This is likely a bug in the compilation phase."));
                }
            }
        }

        let r = self.eval_output_expr_in_loop(&loops[..])?;

        let ctx = self.get_current_context()?;
        ctx.output_expr
            .as_ref()
            .map_or_else(|| Ok(r), |_oe| Ok(ctx.rule_value != Value::Undefined))
    }

    fn eval_stmts(&mut self, stmts: &[&LiteralStmt]) -> Result<bool> {
        let mut eval_success = true;

        for (idx, stmt) in stmts.iter().enumerate() {
            self.memory_check()?;

            if !eval_success {
                break;
            }

            // Get pre-computed hoisted loops from compilation phase
            let loop_exprs: Vec<HoistedLoop> = match self
                .compiled_policy
                .loop_hoisting_table
                .get_statement_loops(self.current_module_index, stmt.sidx)
                .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?
            {
                Some(hoisted_loops) => {
                    // Use pre-computed loops from compilation phase
                    hoisted_loops.clone()
                }
                None => {
                    // Loop hoisting should have been done during compilation
                    // If we reach here, it means the hoisting pass didn't process this statement
                    bail!(stmt.span.error("Loop hoisting information not found for statement. This is likely a bug in the compilation phase."));
                }
            };

            if !loop_exprs.is_empty() {
                // If there are hoisted loop expressions, execute subsequent statements
                // within loops.
                let remaining = stmts.get(idx..).unwrap_or(&[]);
                return self.eval_stmts_in_loop(remaining, &loop_exprs[..]);
            }

            let tail = idx
                .checked_add(1)
                .and_then(|n| stmts.get(n..))
                .unwrap_or(&[]);

            eval_success = self.eval_stmt(stmt, tail)?;

            if matches!(&stmt.literal, Literal::SomeIn { .. }) {
                return Ok(eval_success);
            }
        }

        if eval_success {
            eval_success = self.eval_output_expr()?;
        } else {
            // If a query snippet is being run, gather results.
            let result_opt = {
                let ctx = self.get_current_context_mut()?;
                ctx.result.clone()
            };

            if let Some(mut gathered_result) = result_opt {
                if let Some(scope) = self.scopes.last() {
                    for (name, value) in scope.iter() {
                        gathered_result
                            .bindings
                            .as_object_mut()?
                            .insert(Value::String(name.to_string().into()), value.clone());
                    }
                }

                if gathered_result.expressions.len() == 1 // Single expression query
                    || gathered_result // Multi expression query where no value is false
                    .expressions
                    .iter()
                    .all(|v| v.value != Value::Undefined && v.value != Value::Bool(false))
                        && !gathered_result.expressions.is_empty()
                {
                    let ctx = self.get_current_context_mut()?;
                    ctx.results.result.push(gathered_result);
                }
            }
        }

        Ok(eval_success)
    }

    fn eval_query(&mut self, query: &Ref<Query>) -> Result<bool> {
        self.check_execution_time()?;
        // Execute the query in a new scope
        self.scopes.push(Scope::new());
        let order_indices = {
            let query_module_index = u32::try_from(self.compiled_policy.modules.len())
                .map_err(|err| anyhow!("query module index overflow: {err}"))?;
            if self.current_module_index == query_module_index {
                // Use query schedule for the current module
                let schedule = match self.query_schedule.as_ref() {
                    Some(s) => s
                        .queries
                        .get_checked(query_module_index, query.qidx)
                        .map_err(|err| anyhow!("schedule out of bounds: {err}"))?,
                    None => None,
                };
                match schedule {
                    Some(schedule) => Some(&schedule.order),
                    None => {
                        if self.query_schedule.is_some() {
                            bail!(query
                                .span
                                .error("statements not scheduled in query {query:?}"));
                        }
                        None
                    }
                }
            } else {
                // Use compiled policy schedule for other modules
                let schedule = match self.compiled_policy.schedule.as_ref() {
                    Some(s) => s
                        .queries
                        .get_checked(self.current_module_index, query.qidx)
                        .map_err(|err| anyhow!("schedule out of bounds: {err}"))?,
                    None => None,
                };

                match schedule {
                    Some(schedule) => Some(&schedule.order),
                    None => {
                        if self.compiled_policy.schedule.is_some() {
                            bail!(query
                                .span
                                .error("statements not scheduled in query {query:?}"));
                        }
                        None
                    }
                }
            }
        };

        let ordered_stmts: Vec<&LiteralStmt> = match order_indices {
            Some(order) => {
                let stmts_len = query.stmts.len();
                if order.len() != stmts_len {
                    let msg = format!(
                        "invalid schedule: expected {stmts_len} statement indices, found {}",
                        order.len()
                    );
                    bail!(query.span.error(msg.as_str()));
                }

                let mut ordered = Vec::with_capacity(stmts_len);
                for idx in order {
                    let stmt_idx = usize::from(*idx);
                    let stmt = query.stmts.get(stmt_idx).ok_or_else(|| {
                        let msg = format!(
                            "invalid schedule index {stmt_idx} for {} statements",
                            stmts_len
                        );
                        query.span.error(msg.as_str())
                    })?;
                    ordered.push(stmt);
                }
                ordered
            }
            None => query.stmts.iter().collect(),
        };

        let r = self.eval_stmts(&ordered_stmts);
        self.scopes.pop();
        r
    }

    fn eval_array(&mut self, items: &Vec<ExprRef>) -> Result<Value> {
        self.check_execution_time()?;
        let mut array = Vec::new();

        for item in items {
            let term = self.eval_expr(item)?;
            if term == Value::Undefined {
                return Ok(Value::Undefined);
            }

            array.push(term);
        }

        Ok(Value::from_array(array))
    }

    fn eval_object(&mut self, fields: &Vec<(Span, ExprRef, ExprRef)>) -> Result<Value> {
        self.check_execution_time()?;
        let mut object = BTreeMap::new();

        for (_, key, value) in fields {
            // TODO: check this
            // While the grammar defines a object-item as
            // ( scalar | ref | var ) ":" term, the OPA
            // implementation is more like expr ":" expr
            let key = self.eval_expr(key)?;
            if key == Value::Undefined {
                return Ok(Value::Undefined);
            }
            let value = self.eval_expr(value)?;
            if value == Value::Undefined {
                return Ok(Value::Undefined);
            }
            object.insert(key, value);
        }

        Ok(Value::from_map(object))
    }

    fn eval_set(&mut self, items: &Vec<ExprRef>) -> Result<Value> {
        self.check_execution_time()?;
        let mut set = BTreeSet::new();

        for item in items {
            let term = self.eval_expr(item)?;
            if term == Value::Undefined {
                return Ok(Value::Undefined);
            }
            set.insert(term);
        }

        Ok(Value::from_set(set))
    }

    fn eval_membership(
        &mut self,
        key: &Option<ExprRef>,
        value: &ExprRef,
        collection: &ExprRef,
    ) -> Result<Value> {
        self.check_execution_time()?;
        let value = self.eval_expr(value)?;
        let collection = self.eval_expr(collection)?;

        let result = match &collection {
            Value::Array(array) => {
                if let Some(key) = key {
                    let key = self.eval_expr(key)?;
                    collection[&key] == value
                } else {
                    array.contains(&value)
                }
            }
            Value::Object(object) => {
                if let Some(key) = key {
                    let key = self.eval_expr(key)?;
                    collection[&key] == value
                } else {
                    object.values().any(|item| *item == value)
                }
            }
            Value::Set(set) => {
                if key.is_some() {
                    false
                } else {
                    set.contains(&value)
                }
            }
            _ => {
                false
                //bail!(collection_expr.span().error("collection must be array, object or set"));
            }
        };

        Ok(Value::Bool(result))
    }

    fn eval_array_compr(&mut self, term: &ExprRef, query: &Ref<Query>) -> Result<Value> {
        self.check_execution_time()?;
        // Push new context
        self.contexts.push(Context {
            output_expr: Some(term.clone()),
            value: Value::new_array(),
            is_compr: true,
            ..Context::default()
        });

        // Evaluate body first.
        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn eval_set_compr(&mut self, term: &ExprRef, query: &Ref<Query>) -> Result<Value> {
        self.check_execution_time()?;
        // Push new context
        self.contexts.push(Context {
            output_expr: Some(term.clone()),
            value: Value::new_set(),
            is_compr: true,
            ..Context::default()
        });

        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn eval_object_compr(
        &mut self,
        key: &ExprRef,
        value: &ExprRef,
        query: &Ref<Query>,
    ) -> Result<Value> {
        self.check_execution_time()?;
        // Push new context
        self.contexts.push(Context {
            key_expr: Some(key.clone()),
            output_expr: Some(value.clone()),
            value: Value::new_object(),
            is_compr: true,
            ..Context::default()
        });

        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn lookup_function_by_name(&self, path: &str) -> Option<(&Vec<Ref<Rule>>, &Ref<Module>)> {
        let mut path = path.to_owned();
        if !path.starts_with("data.") {
            path = format!("{}.{}", self.current_module_path, path);
        }

        match self.compiled_policy.functions.get(&path) {
            Some((f, _, m)) => Some((f, m)),
            _ => None,
        }
    }

    fn eval_builtin_call(
        &mut self,
        span: &Span,
        name: &str,
        builtin: builtins::BuiltinFcn,
        params: &[ExprRef],
        args: Vec<Value>,
    ) -> Result<Value> {
        self.check_execution_time()?;
        // If any argument is undefined, then the call is undefined.
        if args.iter().any(|a| a == &Value::Undefined) {
            return Ok(Value::Undefined);
        }

        let cache = builtins::must_cache(name);
        if let Some(cached_key) = &cache {
            if let Some(v) = self.builtins_cache.get(&(cached_key, args.clone())) {
                return Ok(v.clone());
            }
        }

        let v = match builtin.0(
            span,
            params,
            &args[..],
            self.compiled_policy.strict_builtin_errors,
        ) {
            Ok(v) => v,
            // Ignore errors if we are not evaluating in strict mode.
            Err(_) if !self.compiled_policy.strict_builtin_errors => return Ok(Value::Undefined),
            Err(e) => Err(e)?,
        };

        // Handle trace function.
        // TODO: with modifier.
        if name == "trace" {
            if let (Some(traces), Value::String(msg)) = (&mut self.traces, &v) {
                traces.push(msg.clone());
                self.memory_check()?;
                return Ok(Value::Bool(true));
            }
        }

        if let Some(cached_key) = cache {
            self.builtins_cache.insert((cached_key, args), v.clone());
        }

        self.memory_check()?;
        Ok(v)
    }

    #[allow(unused_variables)]
    fn lookup_builtin(span: &Span, path: &str) -> Result<Option<&'static BuiltinFcn>> {
        if let Some(builtin) = builtins::BUILTINS.get(path) {
            return Ok(Some(builtin));
        }
        Ok(None)
    }

    fn is_builtin(span: &Span, path: &str) -> bool {
        path == "print" || matches!(Self::lookup_builtin(span, path), Ok(Some(_)))
    }

    fn to_printable(value: &Value, s: &mut String) {
        match value {
            Value::Array(array) => {
                s.push('[');
                for (idx, e) in array.iter().enumerate() {
                    if idx > 0 {
                        s.push_str(", ");
                    }
                    Self::to_printable(e, s);
                }
                s.push(']');
            }
            Value::Set(set) => {
                s.push('{');
                for (idx, e) in set.iter().enumerate() {
                    if idx > 0 {
                        s.push_str(", ");
                    }
                    Self::to_printable(e, s);
                }
                s.push('}');
            }
            Value::Object(map) => {
                s.push('{');
                for (idx, (k, entry_value)) in map.iter().enumerate() {
                    if idx > 0 {
                        s.push_str(", ");
                    }
                    Self::to_printable(k, s);
                    s.push_str(": ");
                    Self::to_printable(entry_value, s);
                }
                s.push('}');
            }
            other => s.push_str(&format!("{other}")),
        }
    }

    fn eval_print(&mut self, span: &Span, params: &[ExprRef], args: Vec<Value>) -> Result<Value> {
        const MAX_ARGS: u8 = 100;
        if args.len() > usize::from(MAX_ARGS) {
            bail!(span.error(&format!("print supports upto {MAX_ARGS} arguments")));
        }

        // If not compiling for std target, return early if gathering is not
        // requested.
        #[cfg(not(feature = "std"))]
        if !self.gather_prints {
            return Ok(Value::Bool(true));
        }

        let mut msg = String::default();
        for (i, p) in params.iter().enumerate() {
            if i > 0 {
                msg.push(' ');
            }
            match self.eval_expr(p)? {
                Value::Undefined => msg.push_str("<undefined>"),
                // Do not print quotes for string values.
                Value::String(s) => msg.push_str(&format!("{s}")),
                a => Self::to_printable(&a, &mut msg),
            }
        }

        if self.gather_prints {
            // Prefix location information.
            self.prints
                .push(format!("{}:{}: {msg}", span.source.file(), span.line));
        }

        // Print to stderr only if not gathering.
        #[cfg(feature = "std")]
        if !self.gather_prints {
            std::eprintln!("{msg}");
        }

        Ok(Value::Bool(true))
    }

    fn eval_call_impl(
        &mut self,
        span: &Span,
        expr: &ExprRef,
        fcn: &ExprRef,
        params: &[ExprRef],
    ) -> Result<Value> {
        self.check_execution_time()?;
        // Return generated values of walk builtin.
        if let Some(v) = self.get_loop_var_value(expr)? {
            return Ok(v.clone());
        }

        let fcn_path = match get_path_string(fcn, None) {
            Ok(p) => p,
            _ => bail!(span.error("invalid function expression")),
        };

        let mut param_values = Vec::with_capacity(params.len());
        for p in params {
            param_values.push(self.eval_expr(p)?);
        }

        let orig_fcn_path = fcn_path.clone();

        let mut with_functions_saved = None;
        let selected_fcn_path = match self.with_functions.get(&orig_fcn_path) {
            Some(FunctionModifier::Function(p)) => {
                let p = p.clone();
                with_functions_saved = Some(self.with_functions.clone());
                self.with_functions.clear();
                p
            }
            Some(FunctionModifier::Value(value_override)) => {
                if param_values
                    .iter()
                    .any(|evaluated_value| evaluated_value == &Value::Undefined)
                {
                    return Ok(Value::Undefined);
                }
                return Ok(value_override.clone());
            }
            _ => orig_fcn_path.clone(),
        };

        let mut extension = None;
        let empty: Vec<Ref<Rule>> = vec![];
        let (fcns_rules, fcn_module) = match self.lookup_function_by_name(&selected_fcn_path) {
            Some((fcns, m)) => (fcns, Some(m.clone())),
            _ => {
                if self
                    .compiled_policy
                    .default_rules
                    .contains_key(&selected_fcn_path)
                    || self
                        .compiled_policy
                        .default_rules
                        .contains_key(&get_path_string(fcn, Some(&self.current_module_path))?)
                {
                    // process default functions later.
                    (&empty, self.module.clone())
                }
                // Look up extension.
                else if let Some(ext) = self.extensions.get_mut(&selected_fcn_path) {
                    extension = Some(ext);
                    (&empty, None)
                } else if selected_fcn_path == "print" {
                    return self.eval_print(span, params, param_values);
                }
                // Look up builtin function.
                else if let Some(builtin) = Self::lookup_builtin(span, &selected_fcn_path)? {
                    let r = self.eval_builtin_call(
                        span,
                        &selected_fcn_path.clone(),
                        *builtin,
                        params,
                        param_values,
                    );
                    if let Some(with_functions) = with_functions_saved {
                        self.with_functions = with_functions;
                    }
                    return r;
                } else {
                    bail!(
                        span.error(format!("could not find function {selected_fcn_path}").as_str())
                    );
                }
            }
        };
        if param_values.iter().any(|v| v == &Value::Undefined) {
            if let Some(with_functions) = with_functions_saved {
                self.with_functions = with_functions;
            }
            return Ok(Value::Undefined);
        }

        if let Some((nargs, ext)) = extension {
            if param_values.len() != usize::from(*nargs) {
                bail!(span.error("incorrect number of parameters supplied to extension"));
            }
            let r = Rc::make_mut(ext)(param_values);
            // Restore with_functions.
            if let Some(with_functions) = with_functions_saved {
                self.with_functions = with_functions;
            }
            match r {
                Ok(v) => return Ok(v),
                Err(e) => bail!(span.error(&format!("{e}"))),
            }
        }

        let fcns = fcns_rules.clone();

        let mut results: Vec<Value> = Vec::new();
        let mut errors: Vec<anyhow::Error> = Vec::new();

        'outer: for fcn_rule in fcns {
            let (args, output_expr, bodies) = match fcn_rule.as_ref() {
                Rule::Spec {
                    head: RuleHead::Func { args, assign, .. },
                    bodies,
                    ..
                } => (args, assign.as_ref().map(|a| a.value.clone()), bodies),
                _ => bail!("internal error not a function"),
            };

            if args.len() != params.len() {
                return Err(span.source.error(
                    span.line,
                    span.col,
                    format!(
                        "mismatch in number of arguments. supplied {}, expected {}",
                        params.len(),
                        args.len()
                    )
                    .as_str(),
                ));
            }

            // Back up local variables of current function and empty
            // the local variables of callee function.
            let scopes = core::mem::take(&mut self.scopes);

            // Set the arguments scope.
            let args_scope = Scope::new();
            self.scopes.push(args_scope);

            // Determine the module index for the callee so we can fetch binding plans
            let callee_module_idx = fcn_module
                .as_ref()
                .map(|module| self.find_module_index(module))
                .unwrap_or(self.current_module_index);

            for (idx, a) in args.iter().enumerate() {
                // Fetch the binding plan for this function parameter
                let module_idx = callee_module_idx;
                let expr_idx = a.as_ref().eidx();

                let param_value = param_values
                    .get(idx)
                    .ok_or_else(|| anyhow!("internal error: missing param value"))?;

                let binding_success = if let Some(BindingPlan::Parameter {
                    destructuring_plan,
                    ..
                }) = self
                    .compiled_policy
                    .loop_hoisting_table
                    .get_expr_binding_plan(module_idx, expr_idx)
                    .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?
                    .cloned()
                {
                    // Execute the destructuring plan with the parameter value
                    self.execute_destructuring_plan(&destructuring_plan, param_value)?
                        == Value::from(true)
                } else {
                    // Raise error if binding plan is not found
                    return Err(span.error(&format!(
                        "binding plan not found for parameter {}",
                        a.span().text()
                    )));
                };

                if !binding_success {
                    self.scopes = scopes;
                    continue 'outer;
                }
            }

            let ctx = Context {
                output_expr: output_expr.clone(),
                value: Value::new_set(),
                ..Context::default()
            };

            let prev_module = self.set_current_module(fcn_module.clone())?;
            let value = match self.eval_rule_bodies(ctx, span, bodies) {
                Ok(v) => v,
                Err(e) => {
                    // If the rule produces an error, save the error.
                    errors.push(e);
                    self.scopes = scopes;
                    continue;
                }
            };
            self.set_current_module(prev_module)?;

            let result = match &value {
                Value::Set(s) if s.len() == 1 => {
                    let Some(v) = s.iter().next() else {
                        return Err(anyhow!("internal error: expected single value in set"));
                    };
                    v.clone()
                }
                Value::Set(s) if !s.is_empty() => {
                    return Err(span.source.error(
                        span.line,
                        span.col,
                        format!("function produced multiple outputs {value:?}").as_str(),
                    ))
                }
                // If the function successfully executed, but did not return any value, then return true.
                Value::Set(s) if s.is_empty() && output_expr.is_none() => Value::Bool(true),

                Value::Set(s) if s.is_empty() => Value::Undefined,

                // If the function execution resulted in undefined, then propagate it.
                Value::Undefined => Value::Undefined,

                // Function returned a non set value
                v => v.clone(),
            };

            // Restore local variables for current context.
            self.scopes = scopes;

            if result != Value::Undefined {
                results.push(result);
            }
        }

        if self.compiled_policy.strict_builtin_errors && !errors.is_empty() {
            return Err(errors
                .first()
                .map(|e| anyhow!(e.to_string()))
                .unwrap_or_else(|| anyhow!("internal error: missing error entry")));
        }

        if results.is_empty() {
            // Back up local variables of current function and empty
            // the local variables of callee function.
            let scopes = core::mem::take(&mut self.scopes);
            if errors.is_empty() {
                // Check if any default rules can be evaluated.
                // TODO: with mod
                let rules = match self
                    .compiled_policy
                    .default_rules
                    .get(&selected_fcn_path)
                    .cloned()
                {
                    Some(rules) => Some(rules),
                    None => {
                        let alt_fcn_path = get_path_string(fcn, Some(&self.current_module_path))?;
                        self.compiled_policy
                            .default_rules
                            .get(&alt_fcn_path)
                            .cloned()
                    }
                };

                if let Some(rules) = rules {
                    for (rule, _) in rules.iter() {
                        if let Rule::Default { value, .. } = rule.as_ref() {
                            match self.eval_expr(value) {
                                Ok(v) => results.push(v),
                                Err(e) => errors.push(e),
                            }
                        }
                    }
                }
            }
            self.scopes = scopes;
        }

        if let Some(with_functions) = with_functions_saved {
            self.with_functions = with_functions;
        }

        if results.is_empty() {
            if errors.is_empty() {
                return Ok(Value::Undefined);
            } else {
                return Err(errors
                    .first()
                    .map(|e| anyhow!(e.to_string()))
                    .unwrap_or_else(|| anyhow!("internal error: missing error entry")));
            }
        }

        // all defined values should be the equal to the same value that should be returned
        if results.windows(2).any(|w| matches!(w, [a, b] if a != b)) {
            return Err(span.source.error(
                span.line,
                span.col,
                "functions must not produce multiple outputs for same inputs",
            ));
        }

        results
            .first()
            .cloned()
            .ok_or_else(|| anyhow!("internal error: expected function result"))
    }

    fn eval_call(
        &mut self,
        span: &Span,
        expr: &ExprRef,
        fcn: &ExprRef,
        params: &[ExprRef],
        extra_arg: Option<ExprRef>,
        allow_return_arg: bool,
    ) -> Result<Value> {
        self.check_execution_time()?;
        // TODO: global var check; interop with `some var`
        if extra_arg.is_some() {
            let (last_param, arg_prefix) = params
                .split_last()
                .ok_or_else(|| anyhow!("internal error: expected at least one param"))?;

            let value = self.eval_call_impl(span, expr, fcn, arg_prefix)?;
            if allow_return_arg {
                let module_idx = self.current_module_index;
                let expr_idx = last_param.as_ref().eidx();
                if let Some(BindingPlan::Parameter {
                    destructuring_plan, ..
                }) = self
                    .compiled_policy
                    .loop_hoisting_table
                    .get_expr_binding_plan(module_idx, expr_idx)
                    .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?
                    .cloned()
                {
                    // Execute the destructuring plan with the return value
                    let result = self.execute_destructuring_plan(&destructuring_plan, &value)?;
                    Ok(result)
                } else {
                    // Raise error if binding plan is not found
                    Err(span.error(&format!(
                        "binding plan not found for parameter {}",
                        last_param.span().text()
                    )))
                }
            } else {
                let expected = self.eval_expr(last_param)?;
                Ok(Value::Bool(value == expected))
            }
        } else {
            self.eval_call_impl(span, expr, fcn, params)
        }
    }

    fn lookup_local_var(&self, name: &SourceStr) -> Option<Value> {
        // Lookup local variables and arguments.
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v.clone());
            }
        }
        None
    }

    fn ensure_module_evaluated(&mut self, path: String) -> Result<()> {
        self.check_execution_time()?;
        for module in self.compiled_policy.modules.clone().iter().cloned() {
            if Some(&module) == self.module.as_ref() {
                // Prevent cyclic evaluation.
                continue;
            }
            let module_path_str = get_path_string(&module.package.refr, Some("data"))?;
            let has_dot_after_prefix = module_path_str
                .get(path.len()..)
                .is_some_and(|suffix| suffix.starts_with('.'));

            if module_path_str.starts_with(&path)
                && (module_path_str.len() == path.len() || has_dot_after_prefix)
            {
                // Ensure that the module is created.
                let module_path_components = Parser::get_path_ref_components(&module.package.refr)?;
                let module_path_components: Vec<&str> =
                    module_path_components.iter().map(|s| s.text()).collect();
                let vref = Self::make_or_get_value_mut(&mut self.data, &module_path_components)?;
                if *vref == Value::Undefined {
                    *vref = Value::new_object();
                }

                for rule in &module.policy {
                    if !self.processed.contains(rule) {
                        self.eval_rule(&module, rule)?;
                    }
                }

                let prev_module = self.set_current_module(Some(module.clone()))?;
                for rule in &module.policy {
                    if !self.processed.contains(rule) {
                        self.eval_default_rule(rule)?;
                    }
                }
                self.set_current_module(prev_module)?;
                self.mark_processed(&module_path_components)?;
            }
        }

        Ok(())
    }

    fn ensure_rule_evaluated(&mut self, path: String) -> Result<()> {
        self.check_execution_time()?;
        let mut matched = false;
        if let Some(rules) = self.compiled_policy.rules.get(&path) {
            matched = true;
            for r in rules.clone() {
                if !self.processed.contains(&r) {
                    let module = self.get_rule_module(&r)?;
                    self.eval_rule(&module, &r)?;
                }
            }
        }

        // Evaluate the associated default rules after non-default rules
        if let Some(rules) = self.compiled_policy.default_rules.get(&path) {
            matched = true;
            for (r, _) in rules.clone() {
                if !self.processed.contains(&r) {
                    let module = self.get_rule_module(&r)?;
                    let prev_module = self.set_current_module(Some(module))?;
                    self.eval_default_rule(&r)?;
                    self.set_current_module(prev_module)?;
                }
            }
        }

        if matched {
            let comps: Vec<&str> = path.split('.').collect();
            if let Some((_, tail)) = comps.split_first() {
                self.mark_processed(tail)?;
            }
        }
        Ok(())
    }

    fn is_processed(&self, path: &[&str]) -> Result<bool> {
        let mut obj = &self.processed_paths;
        for p in path {
            // Prefix has already been processed.
            if obj[&Value::Undefined] == Value::Null {
                return Ok(true);
            }

            match &obj[*p] {
                // Prefix and its suffixes including path have not been processed.
                Value::Undefined => return Ok(false),
                v => obj = v,
            }
        }

        Ok(obj[&Value::Undefined] == Value::Null)
    }

    fn mark_processed(&mut self, path: &[&str]) -> Result<()> {
        let obj = self.processed_paths.make_or_get_value_mut(path)?;
        if obj == &Value::Undefined {
            *obj = Value::new_object();
        }
        obj.as_object_mut()?.insert(Value::Undefined, Value::Null);
        Ok(())
    }

    fn lookup_var(&mut self, span: &Span, fields: &[&str], no_error: bool) -> Result<Value> {
        let name = span.source_str();

        // Return local variable/argument.
        if let Some(v) = self.lookup_local_var(&name) {
            return Ok(Self::get_value_chained(v, fields));
        }

        // Handle input.
        if name.text() == "input" {
            return Ok(Self::get_value_chained(self.input.clone(), fields));
        }

        // TODO: should we return before checking for input?
        if self.no_rules_lookup {
            if no_error {
                return Ok(Value::Undefined);
            }
            return Err(span.error("undefined var"));
        }

        // Ensure that rules are evaluated
        if name.text() == "data" {
            if self.is_processed(fields)? {
                return Ok(Self::get_value_chained(self.data.clone(), fields));
            }

            // If "data" is used in a query, without any fields, then evaluate all the modules.
            if fields.is_empty() && self.active_rules.is_empty() {
                for module in self.compiled_policy.modules.clone().iter() {
                    for rule in &module.policy {
                        self.eval_rule(module, rule)?;
                    }
                }
            }

            // With modifiers may be used to specify part of a module that that not yet been
            // evaluated. Therefore ensure that module is evaluated first.
            let requested_path = format!("data.{}", fields.join("."));
            self.ensure_module_evaluated(requested_path.clone())?;

            for i in (1..=fields.len()).rev() {
                let prefix = fields.iter().take(i).copied().collect::<Vec<_>>();
                let prefix_path = format!("data.{}", prefix.join("."));
                if self.compiled_policy.rules.contains_key(&prefix_path)
                    || self
                        .compiled_policy
                        .default_rules
                        .contains_key(&prefix_path)
                {
                    self.ensure_rule_evaluated(prefix_path)?;
                    break;
                }
            }

            Ok(Self::get_value_chained(self.data.clone(), fields))
        } else if !self.compiled_policy.modules.is_empty() {
            let module = self.current_module()?;
            let parsed_path = Parser::get_path_ref_components(&module.package.refr)?;
            let mut module_var_path: Vec<&str> = parsed_path.iter().map(|s| s.text()).collect();
            module_var_path.push(name.text());

            if self.is_processed(&module_var_path)? {
                let value = Self::get_value_chained(self.data.clone(), &module_var_path);
                return Ok(Self::get_value_chained(value, fields));
            }

            // Ensure that all the rules having common prefix (name) are evaluated.
            let rule_path = format!("data.{}", module_var_path.join("."));

            if !no_error
                && !self.compiled_policy.rules.contains_key(&rule_path)
                && !self.compiled_policy.default_rules.contains_key(&rule_path)
                && !self.compiled_policy.imports.contains_key(&rule_path)
            {
                bail!(span.error(&format!(
                    "var {} is unsafe (path {:?}, scopes {:?})",
                    name.text(),
                    module_var_path,
                    self.scopes
                )));
            }

            // Find the rule to which the var being looked up corresponds to. This is the prefix for
            // which rules exist.
            let mut found = false;
            for i in (0..=fields.len()).rev() {
                let comps = fields.iter().take(i).copied().collect::<Vec<_>>();
                let path = if comps.is_empty() {
                    rule_path.clone()
                } else {
                    format!("{}.{}", rule_path, comps.join("."))
                };

                if self.compiled_policy.rules.contains_key(&path)
                    || self.compiled_policy.default_rules.contains_key(&path)
                {
                    self.ensure_rule_evaluated(path)?;
                    found = true;
                    break;
                }
            }

            if !found {
                if let Some(imported_var) = self.compiled_policy.imports.get(&rule_path).cloned() {
                    return Ok(Self::get_value_chained(
                        self.eval_expr(&imported_var)?,
                        fields,
                    ));
                }
            }

            let value = Self::get_value_chained(self.data.clone(), &module_var_path[..]);
            Ok(Self::get_value_chained(value, fields))
        } else {
            Ok(Value::Undefined)
        }
    }

    fn eval_expr(&mut self, expr: &ExprRef) -> Result<Value> {
        self.check_execution_time()?;
        #[cfg(feature = "coverage")]
        if self.enable_coverage {
            let span = expr.span();
            let source = &span.source;
            let line = usize::try_from(span.line).unwrap_or(usize::MAX);
            if line > 0 {
                // Check if coverage table already exists for source.
                match self.coverage.get_mut(source) {
                    Some(c) => {
                        // Ensure that current line is valid.
                        let needed = line.saturating_add(1);
                        if c.len() < needed {
                            c.resize(needed, false);
                        }
                        if let Some(slot) = c.get_mut(line) {
                            *slot = true;
                        }
                    }
                    _ => {
                        // Create new table.
                        let size = line.saturating_add(1);
                        let mut c = vec![false; size];
                        if let Some(slot) = c.get_mut(line) {
                            *slot = true;
                        }
                        self.coverage.insert(source.clone(), c);
                    }
                }
            }
        }

        match expr.as_ref() {
            Expr::Null { value: v, .. }
            | Expr::Bool { value: v, .. }
            | Expr::Number { value: v, .. } => Ok(v.clone()),
            // TODO: Handle string vs rawstring
            Expr::String { value: v, .. } => Ok(v.clone()),
            Expr::RawString { value: v, .. } => Ok(v.clone()),
            // TODO: Handle undefined variables
            Expr::Var { .. } => self.eval_chained_ref_dot_or_brack(expr),
            Expr::RefDot { .. } => self.eval_chained_ref_dot_or_brack(expr),
            Expr::RefBrack { .. } => self.eval_chained_ref_dot_or_brack(expr),

            // Expressions with operators
            Expr::ArithExpr { op, lhs, rhs, .. } => self.eval_arith_expr(expr.span(), op, lhs, rhs),
            Expr::AssignExpr { .. } => {
                let module_idx = self.current_module_index;
                let expr_idx = expr.as_ref().eidx();
                let expr_text = expr.span().text().to_string();
                let binding_plan = self
                    .compiled_policy
                    .loop_hoisting_table
                    .get_expr_binding_plan(module_idx, expr_idx)
                    .map_err(|err| anyhow!("loop hoisting table out of bounds: {err}"))?
                    .cloned()
                    .ok_or_else(|| {
                        expr.span().error(
                            format!(
                                "binding plan missing for assignment expression (module_idx={module_idx}, expr_idx={expr_idx}, expr='{expr_text}')"
                            )
                            .as_str(),
                        )
                    })?;
                let BindingPlan::Assignment { plan } = binding_plan else {
                    bail!(expr.span().error("internal error: not an assignment plan"));
                };
                self.execute_assignment_plan(&plan)
            }
            Expr::BinExpr { op, lhs, rhs, .. } => self.eval_bin_expr(op, lhs, rhs),
            Expr::BoolExpr { op, lhs, rhs, .. } => self.eval_bool_expr(op, lhs, rhs),
            Expr::Membership {
                key,
                value,
                collection,
                ..
            } => self.eval_membership(key, value, collection),

            #[cfg(feature = "rego-extensions")]
            Expr::OrExpr { lhs, rhs, .. } => {
                let lhs = self.eval_expr(lhs)?;
                match lhs {
                    Value::Bool(false) | Value::Null | Value::Undefined => self.eval_expr(rhs),
                    _ => Ok(lhs),
                }
            }

            // Creation expression
            Expr::Array { items, .. } => self.eval_array(items),
            Expr::Object { fields, .. } => self.eval_object(fields),
            Expr::Set { items, .. } => self.eval_set(items),

            // Comprehensions
            Expr::ArrayCompr { term, query, .. } => self.eval_array_compr(term, query),
            Expr::ObjectCompr {
                key, value, query, ..
            } => self.eval_object_compr(key, value, query),
            Expr::SetCompr { term, query, .. } => self.eval_set_compr(term, query),
            Expr::UnaryExpr {
                span, expr: uexpr, ..
            } => match uexpr.as_ref() {
                Expr::Number { .. } if !uexpr.span().text().starts_with('-') => {
                    builtins::numbers::arithmetic_operation(
                        span,
                        &ArithOp::Sub,
                        expr,
                        uexpr,
                        Value::from(0),
                        self.eval_expr(uexpr)?,
                        self.compiled_policy.strict_builtin_errors,
                    )
                }
                _ => bail!(expr
                    .span()
                    .error("unary - can only be used with numeric literals")),
            },
            Expr::Call {
                span, fcn, params, ..
            } => self.eval_call(span, expr, fcn, params, None, false),
        }
    }

    fn make_rule_context(&self, head: &RuleHead) -> Result<(Context, Vec<Span>)> {
        let module = self.current_module()?;
        let mut path = Parser::get_path_ref_components(&module.package.refr)?;
        match head {
            RuleHead::Compr { refr, assign, .. } => {
                let output_expr = assign.as_ref().map(|assign| assign.value.clone());
                let (refr, key_expr, value) = match refr.as_ref() {
                    Expr::RefBrack { refr, index, .. } => {
                        (refr, Some(index.clone()), Value::new_object())
                    }
                    _ => (refr, None, Value::new_array()),
                };

                Parser::get_path_ref_components_into(refr, &mut path)?;
                Ok((
                    Context {
                        key_expr,
                        output_expr,
                        value,
                        rule_ref: Some(refr.clone()),
                        ..Context::default()
                    },
                    path,
                ))
            }
            RuleHead::Set { refr, key, .. } => {
                Parser::get_path_ref_components_into(refr, &mut path)?;
                let is_old_style_set = key.is_none();
                Ok((
                    Context {
                        output_expr: key.clone(),
                        value: Value::new_set(),
                        rule_ref: Some(refr.clone()),
                        is_set: true,
                        is_old_style_set,
                        ..Context::default()
                    },
                    path,
                ))
            }
            other => bail!("internal error: unhandled rule ref type: {other:?}"),
        }
    }

    fn get_rule_module(&self, rule: &Ref<Rule>) -> Result<Ref<Module>> {
        for m in self.compiled_policy.modules.iter() {
            if m.policy.iter().any(|r| r == rule) {
                return Ok(m.clone());
            }
        }
        bail!("internal error: could not find module for rule");
    }

    fn eval_rule_bodies(
        &mut self,
        ctx: Context,
        span: &Span,
        bodies: &[RuleBody],
    ) -> Result<Value> {
        self.check_execution_time()?;
        let n_scopes = self.scopes.len();
        let result = if bodies.is_empty() {
            self.contexts.push(ctx.clone());
            self.eval_output_expr()
        } else {
            let mut result = Ok(true);
            for (idx, body) in bodies.iter().enumerate() {
                if idx == 0 {
                    self.contexts.push(ctx.clone());
                } else {
                    self.contexts.pop();
                    let output_expr = body.assign.as_ref().map(|e| e.value.clone());
                    self.contexts.push(Context {
                        output_expr,
                        //                        value: Value::new_array(),
                        //                        ..Context::default()
                        ..ctx.clone()
                    });
                }
                result = self.eval_query(&body.query);
                if matches!(&result, Ok(true) | Err(_)) {
                    break;
                }
            }
            result
        };

        let popped_ctx = match self.contexts.pop() {
            Some(current_ctx) => current_ctx,
            _ => bail!("internal error: rule's context already popped"),
        };

        let result = result?;

        if self.scopes.len() != n_scopes {
            return Err(anyhow!("internal error: scope leak after eval_rule_bodies"));
        }

        if popped_ctx.rule_ref.is_some() {
            if result {
                return Ok(popped_ctx.rule_value);
            } else {
                return Ok(Value::Undefined);
            }
        }

        Ok(match result {
            true => match &popped_ctx.value {
                Value::Object(_) => popped_ctx.value,
                Value::Array(a) if a.len() == 1 => a
                    .first()
                    .cloned()
                    .ok_or_else(|| anyhow!("internal error: expected array element"))?,
                Value::Array(a) if a.is_empty() => Value::Bool(true),
                Value::Array(_) => {
                    return Err(span.source.error(
                        span.line,
                        span.col,
                        "complete rules should not produce multiple outputs",
                    ))
                }
                Value::Set(_) => popped_ctx.value,
                _ => {
                    return Err(anyhow!(
                        "internal error: unexpected ctx.value for rule evaluation: {:?}",
                        popped_ctx.value
                    ));
                }
            },
            false => Value::Undefined,
        })
    }

    fn get_value_chained(mut obj: Value, path: &[&str]) -> Value {
        for p in path {
            obj = obj[&Value::String(p.to_string().into())].clone();
        }
        obj
    }

    #[inline]
    pub fn make_or_get_value_mut<'a>(obj: &'a mut Value, paths: &[&str]) -> Result<&'a mut Value> {
        let (first, tail) = match paths.split_first() {
            Some(v) => v,
            None => return Ok(obj),
        };

        let key = Value::String((*first).into());
        if obj == &Value::Undefined {
            *obj = Value::new_object();
        }
        if let Value::Object(map) = obj {
            if map.get(&key).is_none() {
                Rc::make_mut(map).insert(key.clone(), Value::Undefined);
            }
        }

        match obj {
            Value::Object(map) => match Rc::make_mut(map).get_mut(&key) {
                Some(v) if tail.is_empty() => Ok(v),
                Some(v) => Self::make_or_get_value_mut(v, tail),
                _ => bail!("internal error: unexpected"),
            },
            Value::Undefined if !tail.is_empty() => {
                *obj = Value::new_object();
                Self::make_or_get_value_mut(obj, paths)
            }
            Value::Undefined => Ok(obj),
            _ => bail!("internal error: make: not an object {obj:?}"),
        }
    }

    pub fn merge_rule_value(span: &Span, value: &mut Value, new: Value) -> Result<()> {
        match value.merge(new) {
            Ok(()) => Ok(()),
            Err(_) => Err(span.error("rules should not produce multiple outputs.")),
        }
    }

    pub fn get_path_string(refr: &Expr, document: Option<&str>) -> Result<String> {
        let mut comps = vec![];
        let mut expr_opt = Some(refr);
        while let Some(expr) = expr_opt {
            match expr {
                Expr::RefDot {
                    refr: nested_refr,
                    field,
                    ..
                } => {
                    comps.push(field.0.text());
                    expr_opt = Some(nested_refr);
                }
                Expr::RefBrack {
                    refr: nested_refr,
                    index,
                    ..
                } if matches!(index.as_ref(), Expr::String { .. }) => {
                    if let Expr::String { span: s, .. } = index.as_ref() {
                        comps.push(s.text());
                        expr_opt = Some(nested_refr);
                    }
                }
                Expr::Var { span: v, .. } => {
                    comps.push(v.text());
                    expr_opt = None;
                }
                _ => bail!(expr.span().error("invalid ref expression")),
            }
        }
        if let Some(doc_component) = document {
            comps.push(doc_component);
        };
        comps.reverse();
        Ok(comps.join("."))
    }

    pub fn set_current_module(
        &mut self,
        module: Option<Ref<Module>>,
    ) -> Result<Option<Ref<Module>>> {
        let previous_module = self.module.clone();
        if let Some(new_module) = &module {
            self.current_module_path =
                Self::get_path_string(&new_module.package.refr, Some("data"))?;
            self.current_module_index = self.find_module_index(new_module);
        }
        self.module = module;
        Ok(previous_module)
    }

    fn find_module_index(&self, module: &Ref<Module>) -> u32 {
        self.compiled_policy
            .modules
            .iter()
            .position(|m| core::ptr::eq(m.as_ref(), module.as_ref()))
            .map_or_else(
                || {
                    self.query_module.as_ref().map_or(0, |query_module| {
                        if core::ptr::eq(query_module.as_ref(), module.as_ref()) {
                            u32::try_from(self.compiled_policy.modules.len()).unwrap_or(u32::MAX)
                        } else {
                            0
                        }
                    })
                },
                |idx| u32::try_from(idx).unwrap_or(u32::MAX),
            )
    }

    const fn get_rule_refr(rule: &Rule) -> &ExprRef {
        match rule {
            Rule::Spec { head, .. } => match &head {
                RuleHead::Compr { refr, .. }
                | RuleHead::Set { refr, .. }
                | RuleHead::Func { refr, .. } => refr,
            },
            Rule::Default { refr, .. } => refr,
        }
    }

    fn check_default_value(expr: &ExprRef) -> Result<()> {
        use Expr::*;
        let (kind, span) = match expr.as_ref() {
            // Scalars are supported
            String { .. } | RawString { .. } | Number { .. } | Bool { .. } | Null { .. } => {
                return Ok(())
            }

            // Uminus of number is treated as a single expression,
            UnaryExpr { expr, .. } if matches!(expr.as_ref(), Number { .. }) => return Ok(()),

            // Comprehensions are supported since they won't evaluate to undefined.
            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => return Ok(()),

            // Check each item in array/set.
            Array { items, .. } | Set { items, .. } => {
                for item in items {
                    Self::check_default_value(item)?;
                }
                return Ok(());
            }

            // Check each field in object
            Object { fields, .. } => {
                for (_, key, value) in fields {
                    Self::check_default_value(key)?;
                    Self::check_default_value(value)?;
                }
                return Ok(());
            }

            // The following may evaluate to undefined.
            Var { span, .. } => ("var", span),
            Call { span, .. } => ("call", span),
            UnaryExpr { span, .. } => ("unaryexpr", span),
            RefDot { span, .. } => ("ref", span),
            RefBrack { span, .. } => ("ref", span),
            BinExpr { span, .. } => ("binexpr", span),
            BoolExpr { span, .. } => ("boolexpr", span),
            ArithExpr { span, .. } => ("arithexpr", span),
            AssignExpr { span, .. } => ("assignexpr", span),
            Membership { span, .. } => ("membership", span),
            #[cfg(feature = "rego-extensions")]
            OrExpr { span, .. } => ("orexpr", span),
        };

        Err(span.error(format!("invalid `{kind}` in default value").as_str()))
    }

    pub fn check_default_rules(&self) -> Result<()> {
        for module in self.compiled_policy.modules.iter() {
            for rule in &module.policy {
                if let Rule::Default { value, .. } = rule.as_ref() {
                    Self::check_default_value(value)?;
                }
            }
        }
        Ok(())
    }

    pub fn eval_default_rule(&mut self, rule: &Ref<Rule>) -> Result<()> {
        self.check_execution_time()?;
        // Skip reprocessing rule.
        if self.processed.contains(rule) {
            return Ok(());
        }

        if let Rule::Default {
            span,
            refr,
            value,
            args,
            ..
        } = rule.as_ref()
        {
            if !args.is_empty() {
                // Non-zero function defaults are evaluated differently.
                return Ok(());
            }

            let scopes = core::mem::take(&mut self.scopes);

            let module = self.current_module()?;
            let mut path = Parser::get_path_ref_components(&module.package.refr)?;

            let (refr, index) = match refr.as_ref() {
                Expr::RefBrack { refr, index, .. } => (refr, Some(index.clone())),
                Expr::RefDot { .. } => (refr, None),
                Expr::Var { .. } => (refr, None),
                _ => bail!(refr
                    .span()
                    .error(&format!("invalid token {refr:?} with the default keyword"))),
            };

            Parser::get_path_ref_components_into(refr, &mut path)?;
            let paths: Vec<&str> = path.iter().map(|s| s.text()).collect();

            Self::check_default_value(value)?;
            let value = self.eval_expr(value)?;

            // Assume at this point that all the non-default rules have been evaluated.
            // Merge the default value only if
            // 1. The corresponding variable does not have value yet
            // 2. The corresponding index in the object does not have value yet
            if let Some(index) = index {
                let index = self.eval_expr(&index)?;
                let mut object = Value::new_object();
                object.as_object_mut()?.insert(index.clone(), value);

                let vref = Self::make_or_get_value_mut(&mut self.data, &paths)?;

                if let Value::Object(btree) = &vref {
                    if !btree.contains_key(&index) {
                        Self::merge_rule_value(span, vref, object)?;
                    }
                } else if let Value::Undefined = vref {
                    Self::merge_rule_value(span, vref, object)?;
                }
            } else {
                let vref = Self::make_or_get_value_mut(&mut self.data, &paths)?;
                if let Value::Undefined = &vref {
                    Self::merge_rule_value(span, vref, value)?;
                }
            };

            self.scopes = scopes;
            self.processed.insert(rule.clone());
        }

        Ok(())
    }

    /// Evaluate a default rule and return the resulting value for compiler consumers.
    #[cfg(feature = "rvm")]
    pub fn eval_default_rule_for_compiler(&mut self, rule_path: &str) -> Result<Value> {
        self.check_execution_time()?;
        self.input = Value::Undefined;
        self.data = Value::Undefined;
        self.ensure_loop_var_values_capacity();

        let default_rules = self.compiled_policy.default_rules.get(rule_path).cloned();

        if let Some(rules) = default_rules {
            for (rule, _) in rules {
                for module in self.compiled_policy.modules.iter() {
                    if module.policy.contains(&rule) {
                        let prev_module = self.set_current_module(Some(module.clone()))?;
                        let result = self.eval_default_rule(&rule);
                        self.set_current_module(prev_module)?;

                        if result.is_ok() {
                            let components: Vec<&str> = rule_path.split('.').skip(1).collect();
                            let value = Self::get_value_chained(self.data.clone(), &components);

                            if value != Value::Undefined {
                                return Ok(value);
                            }
                        }

                        return result.map(|_| Value::Undefined);
                    }
                }
            }
        }

        bail!("Could not find default rule for path: {}", rule_path);
    }

    fn update_data(
        &mut self,
        span: &Span,
        _refr: &Expr,
        path: &[&str],
        value: Value,
    ) -> Result<()> {
        if value == Value::Undefined {
            return Ok(());
        }
        // Ensure that path is created.
        let vref = Self::make_or_get_value_mut(&mut self.data, path)?;
        if Self::get_value_chained(self.init_data.clone(), path) == Value::Undefined {
            Self::merge_rule_value(span, vref, value)
        } else {
            // Retain specified value.
            Ok(())
        }
    }

    fn check_rule_path(
        &mut self,
        refr: &ExprRef,
        path: &[Value],
        value: &Value,
        is_set: bool,
    ) -> Result<()> {
        // TODO: can copying of path be avoided below?
        let range = self.rule_values.range((Unbounded, Included(path.to_vec())));

        // Check whether any rules evaluated so far is a parent of given rule.
        let mut conflict = None;
        for (k, (v, r)) in range.rev() {
            if path.starts_with(k) {
                if k == path && (is_set || v == value) {
                    // rule evaluated to same value again.
                } else {
                    conflict = Some((v, r));
                }
            } else {
                break;
            }
        }

        if let Some((_, r)) = conflict {
            bail!(refr.span().error(&format!(
                "rule conflicts with the following rule:\n{}",
                r.span().message("", "defined here")
            )));
        }
        self.rule_values
            .insert(path.to_vec(), (value.clone(), refr.clone()));

        Ok(())
    }

    fn eval_rule_impl(&mut self, module: &Ref<Module>, rule: &Ref<Rule>) -> Result<()> {
        self.check_execution_time()?;
        match rule.as_ref() {
            Rule::Spec {
                span,
                head: rule_head,
                bodies: rule_body,
            } => {
                match rule_head {
                    RuleHead::Compr { refr, .. } | RuleHead::Set { refr, .. } => {
                        let (ctx, _) = self.make_rule_context(rule_head)?;
                        let is_set = ctx.is_set;
                        let is_object = ctx.key_expr.is_some() && !is_set;

                        let value = self.eval_rule_bodies(ctx, span, rule_body)?;
                        let package_components = self.eval_rule_ref(&module.package.refr)?;

                        if value != Value::Undefined {
                            for (path, value_in_map) in value.as_object()? {
                                let mut full_path = package_components.clone();
                                full_path.append(&mut path.as_array()?.clone());
                                self.check_rule_path(refr, &full_path, value_in_map, is_set)?;
                                self.update_rule_value(
                                    span,
                                    full_path,
                                    value_in_map.clone(),
                                    is_set,
                                )?;
                            }
                        } else if is_set {
                            if let Ok(mut comps) = self.eval_rule_ref(refr) {
                                let mut full_path = package_components;
                                full_path.append(&mut comps);
                                self.update_rule_value(span, full_path, Value::new_set(), true)?;
                            }
                        } else if is_object {
                            // Fetch the rule, ignoring the key.
                            if let Expr::RefBrack { refr, .. } = refr.as_ref() {
                                if let Ok(mut comps) = self.eval_rule_ref(refr) {
                                    let mut full_path = package_components;
                                    full_path.append(&mut comps);
                                    self.update_rule_value(
                                        span,
                                        full_path,
                                        Value::Undefined,
                                        false,
                                    )?;
                                }
                            }
                        }
                        self.processed.insert(rule.clone());
                    }
                    RuleHead::Func {
                        refr, args, assign, ..
                    } => {
                        let mut path =
                            Parser::get_path_ref_components(&self.current_module()?.package.refr)?;

                        Parser::get_path_ref_components_into(refr, &mut path)?;
                        let path: Vec<&str> = path.iter().map(|s| s.text()).collect();

                        // Ensure that for functions with a nesting level (e.g: a.foo),
                        // `a` is created as an empty object.
                        if let Some((_, prefix)) = path.split_last() {
                            if !prefix.is_empty() {
                                self.update_data(span, refr, prefix, Value::new_object())?;
                            }
                        }

                        if args.is_empty() {
                            let ctx = Context {
                                output_expr: assign.as_ref().map(|a| a.value.clone()),
                                value: Value::new_array(),
                                ..Context::default()
                            };

                            let value = self.eval_rule_bodies(ctx, span, rule_body)?;
                            self.update_data(refr.span(), refr, &path[..], value)?;
                        }
                    }
                }
            }
            _ => bail!("internal error: unexpected"),
        }
        Ok(())
    }

    pub fn eval_rule(&mut self, module: &Ref<Module>, rule: &Ref<Rule>) -> Result<()> {
        self.check_execution_time()?;
        // Set current module index
        self.current_module_index = self.find_module_index(module);

        // Skip reprocessing rule
        if self.processed.contains(rule) {
            return Ok(());
        }

        // Skip default rules
        if let Rule::Default { .. } = rule.as_ref() {
            return Ok(());
        }

        self.active_rules.push(rule.clone());
        if self.active_rules.iter().filter(|&r| r == rule).count() == 2 {
            let mut msg = String::default();
            for r in &self.active_rules {
                let refr = Self::get_rule_refr(r);
                let span = refr.span();
                msg.push_str(
                    span.source
                        .message(span.line, span.col, "depends on", "")
                        .as_str(),
                );
            }
            msg.push_str("cyclic evaluation");
            self.active_rules.pop();
            let refr = Self::get_rule_refr(rule);
            let span = refr.span();
            return Err(span.source.error(
                span.line,
                span.col,
                format!("recursion detected when evaluating rule:{msg}").as_str(),
            ));
        }

        // Back up local variables of current function and empty
        // the local variables of callee function.
        let scopes = core::mem::take(&mut self.scopes);
        let prev_module = self.set_current_module(Some(module.clone()))?;

        let res = self.eval_rule_impl(module, rule);

        self.set_current_module(prev_module)?;
        self.scopes = scopes;
        match self.active_rules.pop() {
            Some(ref r) if r == rule => res,
            _ => bail!("internal error: current rule not active"),
        }
    }

    pub fn eval_user_query(
        &mut self,
        module: &Ref<Module>,
        query: &Ref<Query>,
        query_schedule: Schedule,
        enable_tracing: bool,
    ) -> Result<QueryResults> {
        self.check_execution_time()?;
        self.traces = match enable_tracing {
            true => Some(vec![]),
            false => None,
        };

        self.memory_check()?;

        // Store the query schedule for lookup during evaluation
        self.query_schedule = Some(query_schedule);

        // Push new context.
        self.contexts.push(Context {
            value: Value::new_set(),
            // Request that results be gathered.
            result: Some(QueryResult::default()),
            ..Context::default()
        });

        self.query_module = Some(module.clone());
        let prev_module = self.set_current_module(Some(module.clone()))?;

        // For user queries, set the module index to match the schedule
        // Query snippets are scheduled as if they're in a module at the end
        let prev_module_index = self.current_module_index;
        let compiled_modules_len =
            u32::try_from(self.compiled_policy.modules.len()).unwrap_or(u32::MAX);
        self.current_module_index = compiled_modules_len;

        self.ensure_loop_var_values_capacity();
        // Eval the query.
        let query_r = self.eval_query(query);
        self.query_module = None;

        let mut results = match self.contexts.pop() {
            Some(ctx) => ctx.results,
            _ => bail!("internal error: no context"),
        };

        // Apply expression ordering from the schedule when it is safe to do so.
        // If the schedule references statements that did not produce expressions, the lengths
        // will differ; in that case we keep the collected order to avoid spurious errors.
        // Example: a schedule for `1 == 2; 1 == 1` may list both statements. The first produces
        // an expression (false), but evaluation stops and the second never runs, so only one
        // expression is collected. In that case `order.len()` can be 2 while one expression is
        // available. In these cases, we avoid reordering - doing so requires maintaining additional
        // data during evaluation and is not worth the complexity for now.
        let current_module_idx = compiled_modules_len;
        let current_query_idx = query.qidx;
        if let Some(ref self_schedule) = &self.query_schedule {
            if let Some(active_schedule) = self_schedule
                .queries
                .get_checked(current_module_idx, current_query_idx)
                .map_err(|err| anyhow!("schedule out of bounds: {err}"))?
            {
                for result in results.result.iter_mut() {
                    let exprs_len = result.expressions.len();
                    // Skip reordering when the schedule length does not match produced expressions.
                    if active_schedule.order.len() != exprs_len {
                        continue;
                    }

                    let placeholder = Expression {
                        value: Value::Undefined,
                        text: "".into(),
                        location: Location { row: 0, col: 0 },
                    };
                    let mut ordered_expressions = vec![placeholder; exprs_len];
                    let mut invalid = false;
                    for (expr_idx, value) in result.expressions.iter().enumerate() {
                        let Some(&order_idx) = active_schedule.order.get(expr_idx) else {
                            invalid = true;
                            break;
                        };

                        let orig_idx = usize::from(order_idx);
                        if let Some(slot) = ordered_expressions.get_mut(orig_idx) {
                            *slot = value.clone();
                        } else {
                            invalid = true;
                            break;
                        }
                    }

                    if !invalid
                        && !ordered_expressions
                            .iter()
                            .any(|v| v.value == Value::Undefined)
                    {
                        result.expressions = ordered_expressions;
                    }
                }
            }
        }

        // Clear the query schedule
        self.query_schedule = None;

        self.set_current_module(prev_module)?;
        self.current_module_index = prev_module_index;

        if let Some(r) = results.result.last() {
            if matches!(&r.bindings, Value::Object(obj) if obj.is_empty())
                && (r.expressions.len() > 1
                    && r.expressions.iter().any(|e| e.value == Value::Bool(false)))
            {
                results = QueryResults::default();
            }
        }

        match query_r {
            Ok(_) => Ok(results),
            Err(e) => Err(e),
        }
    }

    fn get_rule_path_components(mut refr: &Ref<Expr>) -> Result<Vec<Rc<str>>> {
        let mut components: Vec<Rc<str>> = vec![];
        loop {
            refr = match refr.as_ref() {
                Expr::Var { span: v, .. } => {
                    components.push(v.text().into());
                    break;
                }
                Expr::RefBrack { refr, index, .. } => {
                    if let Expr::String { span: s, .. } = index.as_ref() {
                        components.push(s.text().into());
                    } else {
                        components.clear();
                    }
                    refr
                }
                Expr::RefDot { refr, field, .. } => {
                    components.push(field.0.text().into());
                    refr
                }
                _ => break,
            }
        }
        components.reverse();
        Ok(components)
    }

    pub fn create_rule_prefixes(&mut self) -> Result<()> {
        for module in self.compiled_policy.modules.clone().iter() {
            let module_path = Self::get_rule_path_components(&module.package.refr)?;

            for rule in &module.policy {
                let rule_refr = Self::get_rule_refr(rule);
                let mut prefix_path = module_path.clone();
                let mut components = Self::get_rule_path_components(rule_refr)?;
                let is_old_set = matches!(
                    rule.as_ref(),
                    Rule::Spec {
                        head: RuleHead::Set { key: None, .. },
                        ..
                    }
                );

                if components.len() >= 2 && is_old_set {
                    components.pop();
                }

                if components.len() <= 1 {
                    continue;
                }

                components.pop();

                prefix_path.append(&mut components);
                let prefix_path: Vec<&str> = prefix_path.iter().map(|s| s.as_ref()).collect();
                if Self::get_value_chained(self.data.clone(), &prefix_path) == Value::Undefined {
                    self.update_data(
                        rule_refr.span(),
                        rule_refr,
                        &prefix_path,
                        Value::new_object(),
                    )?;
                }
            }
        }

        Ok(())
    }

    fn record_rule(&mut self, refr: &Ref<Expr>, rule: Ref<Rule>) -> Result<()> {
        let comps = Parser::get_path_ref_components(refr)?;
        let comps: Vec<&str> = comps.iter().map(|s| s.text()).collect();
        for (c, _) in comps.iter().enumerate() {
            let path = format!(
                "{}.{}",
                self.current_module_path,
                comps
                    .iter()
                    .take(c.saturating_add(1))
                    .copied()
                    .collect::<Vec<_>>()
                    .join(".")
            );
            if c == comps.len().saturating_sub(1) {
                self.compiled_policy_mut().rule_paths.insert(path.clone());
            }

            match self.compiled_policy_mut().rules.entry(path) {
                MapEntry::Occupied(o) => {
                    o.into_mut().push(rule.clone());
                }
                MapEntry::Vacant(v) => {
                    v.insert(vec![rule.clone()]);
                }
            }
        }

        Ok(())
    }

    fn record_default_rule(
        &mut self,
        refr: &Ref<Expr>,
        rule: &Ref<Rule>,
        index: Option<String>,
    ) -> Result<()> {
        let comps = Parser::get_path_ref_components(refr)?;
        let comps: Vec<&str> = comps.iter().map(|s| s.text()).collect();
        for (idx, comp_idx) in (0..comps.len()).enumerate() {
            let path = format!(
                "{}.{}",
                self.current_module_path,
                comps
                    .iter()
                    .take(comp_idx.saturating_add(1))
                    .copied()
                    .collect::<Vec<_>>()
                    .join(".")
            );
            if comp_idx == comps.len().saturating_sub(1) {
                self.compiled_policy_mut().rule_paths.insert(path.clone());
            }

            match self.compiled_policy_mut().default_rules.entry(path) {
                MapEntry::Occupied(o) => {
                    if idx == comps.len().saturating_sub(1) {
                        for (_, i) in o.get() {
                            if let (Some(old), Some(new)) = (i, &index) {
                                if old == new {
                                    bail!(refr.span().error("multiple default rules for the variable with the same index"));
                                }
                            } else if index.is_some() || i.is_some() {
                                bail!(refr.span().error("conflict type with the default rules"));
                            }
                        }
                    }
                    o.into_mut().push((rule.clone(), index.clone()));
                }
                MapEntry::Vacant(v) => {
                    v.insert(vec![(rule.clone(), index.clone())]);
                }
            }
        }

        Ok(())
    }

    pub fn process_imports(&mut self) -> Result<()> {
        for module in self.compiled_policy.modules.clone().iter() {
            let module_path = get_path_string(&module.package.refr, Some("data"))?;
            for import in &module.imports {
                let target = match &import.r#as {
                    Some(s) => s.text(),
                    _ => match import.refr.as_ref() {
                        Expr::RefDot { field, .. } => field.0.text(),
                        Expr::RefBrack { index, .. } => match index.as_ref() {
                            Expr::String { span: s, .. } => s.text(),
                            _ => "",
                        },
                        Expr::Var { span: v, .. } if v.text() == "input" => {
                            // Warn redundant import of input. Ignore it.
                            #[cfg(feature = "std")]
                            std::eprintln!(
                                "{}",
                                import
                                    .refr
                                    .span()
                                    .message("warning", "redundant import of `input`")
                            );
                            continue;
                        }
                        _ => "",
                    },
                };
                if target.is_empty() {
                    bail!(import
                        .refr
                        .span()
                        .message("warning", "invalid ref in import"));
                }
                self.compiled_policy_mut()
                    .imports
                    .insert(format!("{}.{}", module_path, target), import.refr.clone());
            }
        }
        Ok(())
    }

    pub fn gather_rules(&mut self) -> Result<()> {
        for module in self.compiled_policy.modules.clone().iter() {
            let prev_module = self.set_current_module(Some(module.clone()))?;
            for rule in &module.policy {
                let refr = Self::get_rule_refr(rule);

                if let Rule::Spec { .. } = rule.as_ref() {
                    // Adjust refr to ensure simple ref.
                    // TODO: refactor.
                    let refr = match refr.as_ref() {
                        Expr::RefBrack { index, .. }
                            if matches!(index.as_ref(), Expr::String { .. }) =>
                        {
                            refr
                        }
                        Expr::RefBrack { refr, .. } => refr,
                        _ => refr,
                    };
                    self.record_rule(refr, rule.clone())?;
                } else if let Rule::Default { .. } = rule.as_ref() {
                    let (refr, index) = match refr.as_ref() {
                        // TODO: Validate the index
                        Expr::RefBrack { refr, index, .. } => {
                            if !matches!(
                                index.as_ref(),
                                Expr::Bool { .. } | Expr::Number { .. } | Expr::String { .. }
                            ) {
                                // OPA's behavior is ignoring the non-scalar index
                                bail!(index.span().error("index is not a scalar value"));
                            }

                            let index = self.eval_expr(index)?;

                            (refr, Some(index.to_string()))
                        }
                        _ => (refr, None),
                    };

                    self.record_default_rule(refr, rule, index)?;
                }
            }
            self.set_current_module(prev_module)?;
        }
        Ok(())
    }

    pub fn add_extension(
        &mut self,
        path: String,
        nargs: u8,
        extension: Box<dyn Extension>,
    ) -> Result<()> {
        if let MapEntry::Vacant(v) = self.extensions.entry(path) {
            v.insert((nargs, Rc::new(extension)));
            Ok(())
        } else {
            bail!("extension already added");
        }
    }

    #[cfg(feature = "coverage")]
    fn gather_coverage_in_query(
        &self,
        query: &Ref<Query>,
        covered: &Vec<bool>,
        file: &mut crate::coverage::File,
    ) -> Result<()> {
        for stmt in &query.stmts {
            // TODO: with mods
            match &stmt.literal {
                Literal::SomeVars { .. } => (),
                Literal::SomeIn {
                    value, collection, ..
                } => {
                    self.gather_coverage_in_expr(value, covered, file)?;
                    self.gather_coverage_in_expr(collection, covered, file)?;
                }
                Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => {
                    self.gather_coverage_in_expr(expr, covered, file)?;
                }
                Literal::Every {
                    domain,
                    query: nested_query,
                    ..
                } => {
                    self.gather_coverage_in_expr(domain, covered, file)?;
                    self.gather_coverage_in_query(nested_query, covered, file)?;
                }
            }
        }
        Ok(())
    }

    #[cfg(feature = "coverage")]
    fn gather_coverage_in_expr(
        &self,
        expr: &Ref<Expr>,
        covered: &Vec<bool>,
        file: &mut crate::coverage::File,
    ) -> Result<()> {
        use Expr::*;
        traverse(expr, &mut |e| {
            Ok(match e.as_ref() {
                ArrayCompr { query, .. } | SetCompr { query, .. } | ObjectCompr { query, .. } => {
                    self.gather_coverage_in_query(query, covered, file)?;
                    false
                }
                _ => {
                    let line_usize = usize::try_from(e.span().line).unwrap_or(usize::MAX);
                    match covered.get(line_usize) {
                        Some(true) => {
                            let line_u32 = u32::try_from(line_usize).unwrap_or(u32::MAX);
                            file.covered.insert(line_u32);
                        }
                        Some(false) | None => {
                            let line_u32 = u32::try_from(line_usize).unwrap_or(u32::MAX);
                            file.not_covered.insert(line_u32);
                        }
                    }
                    true
                }
            })
        })?;
        Ok(())
    }

    #[cfg(feature = "coverage")]
    pub fn get_coverage_report(&self) -> Result<crate::coverage::Report> {
        let mut report = crate::coverage::Report::default();

        for module in self.compiled_policy.modules.iter() {
            let span = module.package.refr.span();

            // Get coverage information for the module.
            let Some(covered) = self.coverage.get(&span.source) else {
                continue;
            };

            let mut file = crate::coverage::File {
                path: span.source.file().clone(),
                code: span.source.contents().clone(),
                covered: BTreeSet::new(),
                not_covered: BTreeSet::new(),
            };

            // Loop through each rule and figure out the lines that were not coverd.
            for rule in &module.policy {
                match rule.as_ref() {
                    Rule::Spec { head, bodies, .. } => {
                        match head {
                            RuleHead::Compr { assign, .. } | RuleHead::Func { assign, .. } => {
                                if let Some(a) = assign {
                                    self.gather_coverage_in_expr(&a.value, covered, &mut file)?;
                                }
                            }
                            RuleHead::Set { key, .. } => {
                                if let Some(k) = key {
                                    self.gather_coverage_in_expr(k, covered, &mut file)?;
                                }
                            }
                        }
                        for b in bodies {
                            self.gather_coverage_in_query(&b.query, covered, &mut file)?;
                        }
                    }
                    Rule::Default { value, .. } => {
                        self.gather_coverage_in_expr(value, covered, &mut file)?;
                    }
                }
            }

            report.files.push(file);
        }

        Ok(report)
    }

    #[cfg(feature = "coverage")]
    pub fn set_enable_coverage(&mut self, enable: bool) {
        if self.enable_coverage != enable {
            self.enable_coverage = enable;
            self.clear_coverage_data();
        }
    }

    #[cfg(feature = "coverage")]
    pub fn clear_coverage_data(&mut self) {
        self.coverage = Map::new();
    }

    pub fn set_gather_prints(&mut self, b: bool) {
        if b != self.gather_prints {
            // Clear existing prints.
            core::mem::take(&mut self.prints);
        }
        self.gather_prints = b;
    }

    pub fn take_prints(&mut self) -> Result<Vec<String>> {
        Ok(core::mem::take(&mut self.prints))
    }

    pub fn eval_rule_in_path(&mut self, path: String) -> Result<Value> {
        self.check_execution_time()?;
        if !self.compiled_policy.rule_paths.contains(&path) {
            bail!("not a valid rule path");
        }
        self.ensure_rule_evaluated(path.clone())?;
        let parts: Vec<&str> = path.split('.').collect();

        let (_, tail) = parts
            .split_first()
            .ok_or_else(|| anyhow!("internal error: expected rule path"))?;

        let value = Self::get_value_chained(self.data.clone(), tail);
        #[cfg(feature = "azure_policy")]
        {
            if let Some(target_info) = &self.compiled_policy.target_info {
                // Allow undefined values to pass through without schema validation
                if value != Value::Undefined {
                    target_info.effect_schema.validate(&value)?;
                }
            }
        }
        Ok(value)
    }

    pub fn compile(&mut self, rule: Option<Rc<str>>) -> Result<Rc<CompiledPolicyData>> {
        let data = Some(self.init_data.clone());
        let extensions = self.extensions.clone();
        let compiled_policy = self.compiled_policy_mut();

        compiled_policy.data = data;
        compiled_policy.extensions = extensions;
        if let Some(rule) = rule {
            if !compiled_policy.rule_paths.contains(rule.as_ref()) {
                bail!("not a valid rule path");
            }
            compiled_policy.rule_to_evaluate = rule;
        } else {
            compiled_policy.rule_to_evaluate = "".into();
        }

        // Populate loop hoisting lookup table
        use crate::compiler::hoist::LoopHoister;
        // Re-run hoisting with the analyzer's schedule so statement order is preserved.
        let hoister = compiled_policy
            .schedule
            .clone()
            .map_or_else(LoopHoister::new, LoopHoister::new_with_schedule);
        let loop_lookup = hoister.populate(compiled_policy.modules.as_ref())?;
        compiled_policy.loop_hoisting_table = loop_lookup;

        Ok(self.compiled_policy.clone())
    }
}
