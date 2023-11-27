// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::builtins::{self, BuiltinFcn};
use crate::lexer::*;
use crate::parser::Parser;
use crate::scheduler::*;
use crate::utils::*;
use crate::value::*;

use anyhow::{anyhow, bail, Result};
use log::info;
use serde::Serialize;
use std::collections::{hash_map::Entry, BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

type Scope = BTreeMap<SourceStr, Value>;

type DefaultRuleInfo = (Ref<Rule>, Option<String>);
type ContextExprs = (Option<Ref<Expr>>, Option<Ref<Expr>>);

#[derive(Clone)]
pub struct Interpreter {
    modules: Vec<Ref<Module>>,
    module: Option<Ref<Module>>,
    schedule: Option<Schedule>,
    current_module_path: String,
    input: Value,
    data: Value,
    init_data: Value,
    with_document: Value,
    with_functions: BTreeMap<String, String>,
    scopes: Vec<Scope>,
    // TODO: handle recursive calls where same expr could have different values.
    loop_var_values: BTreeMap<ExprRef, Value>,
    contexts: Vec<Context>,
    functions: FunctionTable,
    rules: HashMap<String, Vec<Ref<Rule>>>,
    default_rules: HashMap<String, Vec<DefaultRuleInfo>>,
    processed: BTreeSet<Ref<Rule>>,
    active_rules: Vec<Ref<Rule>>,
    builtins_cache: BTreeMap<(&'static str, Vec<Value>), Value>,
    no_rules_lookup: bool,
    traces: Option<Vec<std::rc::Rc<str>>>,
    allow_deprecated: bool,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct QueryResult {
    // Expressions is shown first to match OPA.
    pub expressions: Vec<Value>,
    #[serde(skip_serializing_if = "Value::is_empty_object")]
    pub bindings: Value,
}

impl Default for QueryResult {
    fn default() -> Self {
        Self {
            bindings: Value::new_object(),
            expressions: vec![],
        }
    }
}

#[derive(Debug, Clone, Default, Serialize)]
pub struct QueryResults {
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub result: Vec<QueryResult>,
}

#[derive(Debug, Clone)]
struct Context {
    key_expr: Option<ExprRef>,
    output_expr: Option<ExprRef>,
    value: Value,
    result: Option<QueryResult>,
    results: QueryResults,
    is_compr: bool,
}

#[derive(Debug)]
struct LoopExpr {
    span: Span,
    expr: ExprRef,
    value: ExprRef,
    index: SourceStr,
}

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter {
            modules: vec![],
            module: None,
            schedule: None,
            current_module_path: String::default(),
            input: Value::new_object(),
            data: Value::new_object(),
            init_data: Value::new_object(),
            with_document: Value::new_object(),
            with_functions: BTreeMap::new(),
            scopes: vec![Scope::new()],
            contexts: vec![],
            loop_var_values: BTreeMap::new(),
            functions: FunctionTable::new(),
            rules: HashMap::new(),
            default_rules: HashMap::new(),
            processed: BTreeSet::new(),
            active_rules: vec![],
            builtins_cache: BTreeMap::new(),
            no_rules_lookup: false,
            traces: None,
            allow_deprecated: true,
        }
    }

    pub fn set_schedule(&mut self, schedule: Option<Schedule>) {
        self.schedule = schedule;
    }

    pub fn set_functions(&mut self, functions: FunctionTable) {
        self.functions = functions;
    }

    pub fn set_modules(&mut self, modules: &[Ref<Module>]) {
        self.modules = modules.to_vec();
    }

    pub fn get_modules_mut(&mut self) -> &mut Vec<Ref<Module>> {
        &mut self.modules
    }

    pub fn set_init_data(&mut self, init_data: Value) {
        self.init_data = init_data;
    }

    pub fn set_data(&mut self, data: Value) {
        self.data = data;
    }

    pub fn get_data_mut(&mut self) -> &mut Value {
        &mut self.data
    }

    pub fn set_traces(&mut self, enable_tracing: bool) {
        self.traces = match enable_tracing {
            true => Some(vec![]),
            false => None,
        };
    }

    pub fn set_input(&mut self, input: Value) {
        self.input = input;
        info!("input: {:#?}", self.input);
    }

    pub fn init_with_document(&mut self) -> Result<()> {
        *Self::make_or_get_value_mut(&mut self.with_document, &["data"])? = Value::new_object();
        *Self::make_or_get_value_mut(&mut self.with_document, &["input"])? = Value::new_object();

        Ok(())
    }

    pub fn clear_builtins_cache(&mut self) {
        self.builtins_cache.clear();
    }

    pub fn clean_internal_evaluation_state(&mut self) {
        self.data = self.init_data.clone();
        self.processed.clear();
        self.loop_var_values.clear();
        self.scopes = vec![Scope::new()];
        self.contexts = vec![];
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

    // TODO: optimize this
    fn variables_assignment(&mut self, name: &SourceStr, value: &Value) -> Result<()> {
        if let Some(variable) = self.current_scope_mut()?.get_mut(name) {
            *variable = value.clone();
            Ok(())
        } else if name.text() == "_" {
            Ok(())
        } else {
            bail!("variable {} is undefined", name)
        }
    }

    fn eval_chained_ref_dot_or_brack(&mut self, mut expr: &ExprRef) -> Result<Value> {
        // Collect a chaing of '.field' or '["field"]'
        let mut path = vec![];
        loop {
            if let Some(v) = self.loop_var_values.get(expr) {
                path.reverse();
                return Ok(Self::get_value_chained(v.clone(), &path[..]));
            }
            match expr.as_ref() {
                // Stop path collection upon encountering the leading variable.
                Expr::Var(v) => {
                    path.reverse();
                    return self.lookup_var(v, &path[..]);
                }
                // Accumulate chained . field accesses.
                Expr::RefDot { refr, field, .. } => {
                    expr = refr;
                    path.push(*field.text());
                }
                Expr::RefBrack { refr, index, .. } => match index.as_ref() {
                    // refr["field"] is the same as refr.field
                    Expr::String(s) => {
                        expr = refr;
                        path.push(*s.text());
                    }
                    // Handle other forms of refr.
                    // Note, we have the choice to evaluate a non-string index
                    _ => {
                        path.reverse();
                        let obj = self.eval_expr(refr)?;
                        let index = self.eval_expr(index)?;
                        let mut v = obj[&index].clone();
                        // Qualified references starting with data (e.g data.p.q) can
                        // be indexed using numbers. The number will be converted to string
                        // if a matching key exists.
                        if v == Value::Undefined
                            && matches!(index, Value::Number(_))
                            && get_root_var(refr)?.text() == "data"
                        {
                            let index = index.to_string();
                            v = obj[&index].clone();
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

    fn is_loop_index_var(&self, ident: &SourceStr) -> bool {
        // TODO: check for vars that are declared using some-vars
        match ident.text() {
            "_" => true,
            _ => match self.lookup_local_var(ident) {
                // Vars declared using `some v` can be loop vars.
                // They are initialized to undefined.
                Some(Value::Undefined) => true,
                // If ident is a local var (in current or parent scopes),
                // then it is not a loop var.
                Some(_) => false,
                None => {
                    // Check if ident is a rule.
                    let path = self.current_module_path.clone() + "." + ident.text();
                    self.rules.get(&path).is_none()
                }
            },
        }
    }

    fn hoist_loops_impl(&self, expr: &ExprRef, loops: &mut Vec<LoopExpr>) {
        use Expr::*;
        match expr.as_ref() {
            RefBrack { refr, index, span } => {
                // First hoist any loops in refr
                self.hoist_loops_impl(refr, loops);

                // Then hoist the current bracket operation.
                match index.as_ref() {
                    Var(ident) if self.is_loop_index_var(&ident.source_str()) => {
                        loops.push(LoopExpr {
                            span: span.clone(),
                            expr: expr.clone(),
                            value: refr.clone(),
                            index: ident.source_str(),
                        })
                    }
                    _ => {
                        // hoist any loops in index expression.
                        self.hoist_loops_impl(index, loops);
                    }
                }
            }

            // Primitives
            String(_) | RawString(_) | Number(_) | True(_) | False(_) | Null(_) | Var(_) => (),

            // Recurse into expressions in other variants.
            Array { items, .. } | Set { items, .. } | Call { params: items, .. } => {
                for item in items {
                    self.hoist_loops_impl(item, loops);
                }
            }

            Object { fields, .. } => {
                for (_, key, value) in fields {
                    self.hoist_loops_impl(key, loops);
                    self.hoist_loops_impl(value, loops);
                }
            }

            RefDot { refr: expr, .. } | UnaryExpr { expr, .. } => {
                self.hoist_loops_impl(expr, loops)
            }

            BinExpr { lhs, rhs, .. }
            | BoolExpr { lhs, rhs, .. }
            | ArithExpr { lhs, rhs, .. }
            | AssignExpr { lhs, rhs, .. } => {
                self.hoist_loops_impl(lhs, loops);
                self.hoist_loops_impl(rhs, loops);
            }

            Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key.as_ref() {
                    self.hoist_loops_impl(key, loops);
                }
                self.hoist_loops_impl(value, loops);
                self.hoist_loops_impl(collection, loops);
            }

            // The output expressions of comprehensions must be subject to hoisting
            // only after evaluating the body of the comprehensions since the output
            // expressions may depend on variables defined within the body.
            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => (),
        }
    }

    fn hoist_loops(&self, literal: &Literal) -> Vec<LoopExpr> {
        let mut loops = vec![];
        use Literal::*;
        match literal {
            SomeVars { .. } => (),
            SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key {
                    self.hoist_loops_impl(key, &mut loops);
                }
                self.hoist_loops_impl(value, &mut loops);
                self.hoist_loops_impl(collection, &mut loops);
            }
            Every {
                domain: collection, ..
            } => self.hoist_loops_impl(collection, &mut loops),
            Expr { expr, .. } | NotExpr { expr, .. } => self.hoist_loops_impl(expr, &mut loops),
        }
        loops
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
            BinOp::Or => builtins::sets::union(lhs, rhs, lhs_value, rhs_value),
            BinOp::And => builtins::sets::intersection(lhs, rhs, lhs_value, rhs_value),
        }
    }

    fn eval_arith_expr(&mut self, op: &ArithOp, lhs: &ExprRef, rhs: &ExprRef) -> Result<Value> {
        let lhs_value = self.eval_expr(lhs)?;
        let rhs_value = self.eval_expr(rhs)?;

        if lhs_value == Value::Undefined || rhs_value == Value::Undefined {
            return Ok(Value::Undefined);
        }

        match (op, &lhs_value, &rhs_value) {
            (ArithOp::Sub, Value::Set(_), _) | (ArithOp::Sub, _, Value::Set(_)) => {
                builtins::sets::difference(lhs, rhs, lhs_value, rhs_value)
            }
            _ => builtins::numbers::arithmetic_operation(op, lhs, rhs, lhs_value, rhs_value),
        }
    }

    fn eval_assign_expr(&mut self, op: &AssignOp, lhs: &ExprRef, rhs: &ExprRef) -> Result<Value> {
        let (name, value) = match op {
            AssignOp::Eq => {
                match (lhs.as_ref(), rhs.as_ref()) {
                    (Expr::Var(lhs_span), Expr::Var(rhs_span)) => {
                        let (lhs_name, lhs_var) = (lhs_span.source_str(), self.eval_expr(lhs)?);
                        let (rhs_name, rhs_var) = (rhs_span.source_str(), self.eval_expr(rhs)?);

                        match (&lhs_var, &rhs_var) {
                            (Value::Undefined, Value::Undefined) => {
                                bail!(lhs.span().error("both operands are unsafe"))
                            }
                            (Value::Undefined, _) => (lhs_name, rhs_var),
                            (_, Value::Undefined) => (rhs_name, lhs_var),
                            // TODO: avoid reeval
                            _ => return self.eval_bool_expr(&BoolOp::Eq, lhs, rhs),
                        }
                    }
                    (Expr::Var(lhs_span), _) => {
                        let (name, var) = (lhs_span.source_str(), self.eval_expr(lhs)?);

                        // TODO: Check this
                        // Allow variable overwritten inside a loop
                        if !matches!(var, Value::Undefined)
                            && self.loop_var_values.get(rhs).is_none()
                        {
                            return self.eval_bool_expr(&BoolOp::Eq, lhs, rhs);
                        }

                        (name, self.eval_expr(rhs)?)
                    }
                    (_, Expr::Var(rhs_span)) => {
                        let (name, var) = (rhs_span.source_str(), self.eval_expr(rhs)?);

                        // TODO: Check this
                        // Allow variable overwritten inside a loop
                        if !matches!(var, Value::Undefined)
                            && self.loop_var_values.get(lhs).is_none()
                        {
                            return self.eval_bool_expr(&BoolOp::Eq, lhs, rhs);
                        }

                        (name, self.eval_expr(lhs)?)
                    }
                    // Treat the assignment as comparison if neither lhs nor rhs is a variable
                    _ => return self.eval_bool_expr(&BoolOp::Eq, lhs, rhs),
                }
            }
            AssignOp::ColEq => {
                let name = if let Expr::Var(span) = lhs.as_ref() {
                    span.source_str()
                } else {
                    bail!("internal error: unexpected");
                };

                // TODO: Check this
                // Allow variable overwritten inside a loop
                let lhs_val = self.lookup_local_var(&name);
                if !matches!(lhs_val, None | Some(Value::Undefined))
                    && self.loop_var_values.get(rhs).is_none()
                {
                    bail!(rhs
                        .span()
                        .error(&format!("redefinition for variable {}", name)));
                }

                (name, self.eval_expr(rhs)?)
            }
        };

        // Omit recording undefined values.
        if value == Value::Undefined {
            return Ok(value); //Ok(Value::Bool(false));
        }

        self.add_variable_or(&name)?;

        // TODO: optimize this
        self.variables_assignment(&name, &value)?;

        info!(
            "eval_assign_expr before, op: {:?}, lhs: {:?}, rhs: {:?}",
            op, lhs, rhs
        );

        Ok(Value::Bool(true))
    }

    fn eval_every(
        &mut self,
        _span: &Span,
        key: &Option<Span>,
        value: &Span,
        domain: &ExprRef,
        query: &Ref<Query>,
    ) -> Result<bool> {
        let domain = self.eval_expr(domain)?;

        self.scopes.push(Scope::new());
        self.contexts.push(Context {
            key_expr: None,
            output_expr: None,
            value: Value::new_set(),
            result: None,
            results: QueryResults::default(),
            is_compr: false,
        });
        let mut r = true;
        match domain {
            Value::Array(a) => {
                for (idx, v) in a.iter().enumerate() {
                    self.add_variable(&value.source_str(), v.clone())?;
                    if let Some(key) = key {
                        self.add_variable(&key.source_str(), Value::from_float(idx as Float))?;
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
            // Other types cause every to evaluate to true even though
            // it is supposed to happen only for empty domain.
            _ => (),
        };
        self.contexts.pop();
        self.scopes.pop();
        Ok(r)
    }

    fn lookup_or_eval_expr(
        &mut self,
        cache: &mut BTreeMap<ExprRef, Value>,
        expr: &ExprRef,
    ) -> Result<Value> {
        match cache.get(expr) {
            Some(v) => Ok(v.clone()),
            _ => {
                let v = self.eval_expr(expr)?;
                cache.insert(expr.clone(), v.clone());
                Ok(v)
            }
        }
    }

    fn make_bindings_impl(
        &mut self,
        is_last: bool,
        type_match: &mut BTreeSet<ExprRef>,
        cache: &mut BTreeMap<ExprRef, Value>,
        expr: &ExprRef,
        value: &Value,
    ) -> Result<bool> {
        // Propagate undefined.
        if value == &Value::Undefined {
            return Ok(false);
        }
        let span = expr.span();
        let raise_error = is_last && type_match.get(expr).is_none();

        match (expr.as_ref(), value) {
            (Expr::Var(ident), _) => {
                self.add_variable(&ident.source_str(), value.clone())?;
                Ok(true)
            }

            // Destructure arrays
            (Expr::Array { items, .. }, Value::Array(a)) => {
                if items.len() != a.len() {
                    if raise_error {
                        return Err(span.error(
                            format!(
                                "array length mismatch. Expected {} got {}.",
                                items.len(),
                                a.len()
                            )
                            .as_str(),
                        ));
                    }
                    return Ok(false);
                }
                type_match.insert(expr.clone());

                let mut r = false;
                for (idx, item) in items.iter().enumerate() {
                    r = self.make_bindings(is_last, type_match, cache, item, &a[idx])? || r;
                }

                Ok(true)
            }

            // Destructure objects
            (Expr::Object { fields, .. }, Value::Object(_)) => {
                let mut r = true;
                for (_, key_expr, value_expr) in fields.iter() {
                    // Rego does not support bindings in keys.
                    // Therefore, just eval key_expr.
                    let key = self.lookup_or_eval_expr(cache, key_expr)?;
                    let field_value = &value[&key];

                    if field_value == &Value::Undefined {
                        if raise_error {
                            return Err(span.error("Expected value, got undefined."));
                        }
                        return Ok(false);
                    }

                    // Match patterns in value_expr
                    r = r
                        && self.make_bindings(
                            is_last,
                            type_match,
                            cache,
                            value_expr,
                            field_value,
                        )?;
                }
                type_match.insert(expr.clone());

                Ok(r)
            }
            _ => {
                let expr_value = self.lookup_or_eval_expr(cache, expr)?;
                if expr_value == Value::Undefined {
                    return Ok(false);
                }

                if raise_error {
                    let expr_t = builtins::types::get_type(&expr_value);
                    let value_t = builtins::types::get_type(value);

                    if expr_t != value_t {
                        return Err(span.error(
			format!("Cannot bind pattern of type `{expr_t}` with value of type `{value_t}`. Value is {value}.").as_str()));
                    }
                }
                type_match.insert(expr.clone());

                Ok(&expr_value == value)
            }
        }
    }

    fn make_bindings(
        &mut self,
        is_last: bool,
        type_match: &mut BTreeSet<ExprRef>,
        cache: &mut BTreeMap<ExprRef, Value>,
        expr: &ExprRef,
        value: &Value,
    ) -> Result<bool> {
        let prev = self.no_rules_lookup;
        self.no_rules_lookup = true;
        let r = self.make_bindings_impl(is_last, type_match, cache, expr, value);
        self.no_rules_lookup = prev;
        r
    }

    fn make_key_value_bindings(
        &mut self,
        is_last: bool,
        type_match: &mut BTreeSet<ExprRef>,
        cache: &mut BTreeMap<ExprRef, Value>,
        exprs: (&Option<ExprRef>, &ExprRef),
        values: (&Value, &Value),
    ) -> Result<bool> {
        let (key_expr, value_expr) = exprs;
        let (key, value) = values;
        if let Some(key_expr) = key_expr {
            if !self.make_bindings(is_last, type_match, cache, key_expr, key)? {
                return Ok(false);
            }
        }
        self.make_bindings(is_last, type_match, cache, value_expr, value)
    }

    fn eval_some_in(
        &mut self,
        _span: &Span,
        key_expr: &Option<ExprRef>,
        value_expr: &ExprRef,
        collection: &ExprRef,
        stmts: &[&LiteralStmt],
    ) -> Result<bool> {
        let scope_saved = self.current_scope()?.clone();
        let mut type_match = BTreeSet::new();
        let mut cache = BTreeMap::new();
        let mut count = 0;
        match self.eval_expr(collection)? {
            Value::Array(a) => {
                for (idx, value) in a.iter().enumerate() {
                    if !self.make_key_value_bindings(
                        idx == a.len() - 1,
                        &mut type_match,
                        &mut cache,
                        (key_expr, value_expr),
                        (&Value::from_float(idx as Float), value),
                    )? {
                        continue;
                    }

                    if self.eval_stmts(stmts)? {
                        count += 1;
                    }
                    *self.current_scope_mut()? = scope_saved.clone();
                }
            }
            Value::Set(s) => {
                for (idx, value) in s.iter().enumerate() {
                    if !self.make_key_value_bindings(
                        idx == s.len() - 1,
                        &mut type_match,
                        &mut cache,
                        (key_expr, value_expr),
                        (value, value),
                    )? {
                        continue;
                    }

                    if self.eval_stmts(stmts)? {
                        count += 1;
                    }
                    *self.current_scope_mut()? = scope_saved.clone();
                }
            }

            Value::Object(o) => {
                for (idx, (key, value)) in o.iter().enumerate() {
                    if !self.make_key_value_bindings(
                        idx == o.len() - 1,
                        &mut type_match,
                        &mut cache,
                        (key_expr, value_expr),
                        (key, value),
                    )? {
                        continue;
                    }

                    if self.eval_stmts(stmts)? {
                        count += 1;
                    }
                    *self.current_scope_mut()? = scope_saved.clone();
                }
            }
            Value::Undefined => (),
            v => {
                let span = collection.span();
                bail!(span.error(
                    format!("`some .. in collection` expects array/set/object. Got `{v}`").as_str()
                ))
            }
        }

        Ok(count > 0)
    }

    fn make_expression_result(span: &Span, v: &Value) -> Value {
        let mut loc = BTreeMap::new();
        loc.insert(
            Value::String("row".into()),
            Value::from_float(span.line as f64),
        );
        loc.insert(
            Value::String("col".into()),
            Value::from_float(span.col as f64),
        );

        let mut expr = BTreeMap::new();
        expr.insert(Value::String("value".into()), v.clone());
        expr.insert(Value::String("location".into()), Value::from_map(loc));
        expr.insert(
            Value::String("text".into()),
            Value::String(span.text().to_string().into()),
        );
        Value::from_map(expr)
    }

    fn eval_stmt_impl(&mut self, stmt: &LiteralStmt, stmts: &[&LiteralStmt]) -> Result<bool> {
        Ok(match &stmt.literal {
            Literal::Expr { span, expr, .. } => {
                let value = match expr.as_ref() {
                    Expr::Call { span, fcn, params } => self.eval_call(
                        span,
                        fcn,
                        params,
                        get_extra_arg(
                            expr,
                            Some(self.current_module_path.as_str()),
                            &self.functions,
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
                                .push(Self::make_expression_result(span, &value))
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
                    Expr::Call { span, fcn, params } => self.eval_call(
                        span,
                        fcn,
                        params,
                        get_extra_arg(
                            expr,
                            Some(self.current_module_path.as_str()),
                            &self.functions,
                        ),
                        false,
                    )?,
                    _ => self.eval_expr(expr)?,
                };
                if let Some(ctx) = self.contexts.last_mut() {
                    if let Some(result) = &mut ctx.result {
                        result
                            .expressions
                            .push(Self::make_expression_result(span, &Value::Bool(true)))
                    }
                }
                // https://github.com/open-policy-agent/opa/issues/1622#issuecomment-520547385
                matches!(value, Value::Bool(false) | Value::Undefined)
            }
            Literal::SomeVars { span, vars, .. } => {
                for var in vars {
                    let name = var.source_str();
                    if let Ok(variable) = self.add_variable_or(&name) {
                        if variable != Value::Undefined {
                            return Err(anyhow!(
                                "duplicated definition of local variable {}",
                                name
                            ));
                        }
                    }
                }
                if let Some(ctx) = self.contexts.last_mut() {
                    if let Some(result) = &mut ctx.result {
                        result
                            .expressions
                            .push(Self::make_expression_result(span, &Value::Bool(true)))
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
                            .push(Self::make_expression_result(span, &Value::Bool(true)))
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
                            .push(Self::make_expression_result(span, &Value::Bool(true)))
                    }
                }
                self.eval_every(span, key, value, domain, query)?
            }
        })
    }

    fn eval_stmt(&mut self, stmt: &LiteralStmt, stmts: &[&LiteralStmt]) -> Result<bool> {
        let mut skip_exec = false;
        let saved_state = if !stmt.with_mods.is_empty() {
            // Save state;
            let with_document = self.with_document.clone();
            let input = self.input.clone();
            let data = self.data.clone();
            let processed = self.processed.clone();
            let with_functions = self.with_functions.clone();

            // Apply with modifiers.
            for wm in &stmt.with_mods {
                let path = Parser::get_path_ref_components(&wm.refr)?;
                let path: Vec<&str> = path.iter().map(|s| *s.text()).collect();
                let target = path.join(".");

                let value = match self.eval_expr(&wm.r#as) {
                    Ok(Value::Undefined) => {
                        if let Ok(fcn_path) = get_path_string(&wm.r#as, None) {
                            let span = wm.r#as.span();
                            if self.lookup_function_by_name(&fcn_path).is_some() {
                                let mut fcn_path = get_path_string(&wm.r#as, None)?;
                                if !fcn_path.starts_with("data.") {
                                    fcn_path = self.current_module_path.clone() + "." + &fcn_path;
                                }
                                self.with_functions.insert(target, fcn_path);
                                continue;
                            } else if self.lookup_builtin(span, &fcn_path).is_ok() {
                                self.with_functions.insert(target, fcn_path);
                                continue;
                            }
                        }
                        skip_exec = true;
                        continue;
                    }
                    Ok(v) => v,
                    Err(e) => return Err(e),
                };

                if path[0] == "input" || path[0] == "data" {
                    *Self::make_or_get_value_mut(&mut self.with_document, &path[..])? = value;
                } /* else if path.len() == 1 {
                      // TODO: handle var in current module.
                  } else {
                      // TODO: error about input, data
                  } */
            }

            self.data = self.with_document["data"].clone();
            self.input = self.with_document["input"].clone();
            self.processed.clear();

            (with_document, input, data, processed, with_functions)
        } else {
            (
                Value::Undefined,
                Value::Undefined,
                Value::Undefined,
                BTreeSet::new(),
                BTreeMap::new(),
            )
        };

        let r = if !skip_exec {
            self.eval_stmt_impl(stmt, stmts)
        } else {
            Ok(false)
        };

        // Restore state.
        if saved_state.0 != Value::Undefined {
            (
                self.with_document,
                self.input,
                self.data,
                self.processed,
                self.with_functions,
            ) = saved_state;
        }

        r
    }

    fn eval_stmts_in_loop(&mut self, stmts: &[&LiteralStmt], loops: &[LoopExpr]) -> Result<bool> {
        if loops.is_empty() {
            if !stmts.is_empty() {
                // Evaluate the current statement whose loop expressions have been hoisted.
                if self.eval_stmt(stmts[0], &stmts[1..])? {
                    if !matches!(&stmts[0].literal, Literal::SomeIn { .. }) {
                        self.eval_stmts(&stmts[1..])
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
            let loop_expr = &loops[0];
            let mut result = false;

            let loop_expr_value = self.eval_expr(&loop_expr.value)?;

            // If the loop's index variable has already been assigned a value
            // (this can happen if the same index is used for two different collections),
            // then evaluate statements only if the index applies to this collection.
            if let Some(idx) = self.lookup_local_var(&loop_expr.index) {
                if loop_expr_value[&idx] != Value::Undefined {
                    result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                    return Ok(result);
                }
            }

            // Save the current scope and restore it after evaluating the statements so
            // that the effects of the current loop iteration are cleared.
            let scope_saved = self.current_scope()?.clone();

            let query_result = self.get_current_context()?.result.clone();
            match loop_expr_value {
                Value::Array(items) => {
                    for (idx, v) in items.iter().enumerate() {
                        self.loop_var_values
                            .insert(loop_expr.expr.clone(), v.clone());
                        self.add_variable(&loop_expr.index, Value::from_float(idx as Float))?;

                        result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                        self.loop_var_values.remove(&loop_expr.expr);
                        *self.current_scope_mut()? = scope_saved.clone();
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result = query_result.clone();
                        }
                    }
                }
                Value::Set(items) => {
                    for v in items.iter() {
                        self.loop_var_values
                            .insert(loop_expr.expr.clone(), v.clone());
                        // For sets, index is also the value.
                        self.add_variable(&loop_expr.index, v.clone())?;
                        result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                        self.loop_var_values.remove(&loop_expr.expr);
                        *self.current_scope_mut()? = scope_saved.clone();
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result = query_result.clone();
                        }
                    }
                }
                Value::Object(obj) => {
                    for (k, v) in obj.iter() {
                        self.loop_var_values
                            .insert(loop_expr.expr.clone(), v.clone());
                        // For objects, index is key.
                        self.add_variable(&loop_expr.index, k.clone())?;
                        result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                        self.loop_var_values.remove(&loop_expr.expr);
                        *self.current_scope_mut()? = scope_saved.clone();
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result = query_result.clone();
                        }
                    }
                }
                Value::Undefined => {
                    result = false;
                }
                _ => {
                    return Err(loop_expr.span.source.error(
                        loop_expr.span.line,
                        loop_expr.span.col,
                        "item cannot be indexed",
                    ));
                }
            }

            // Return true if at least on iteration returned true
            Ok(result)
        }
    }

    fn eval_output_expr_in_loop(&mut self, loops: &[LoopExpr]) -> Result<bool> {
        if loops.is_empty() {
            let (key_expr, output_expr) = self.get_exprs_from_context()?;

            match (key_expr, output_expr) {
                (Some(ke), Some(oe)) => {
                    let key = self.eval_expr(&ke)?;
                    let value = self.eval_expr(&oe)?;

                    let ctx = self.contexts.last_mut().unwrap();
                    if key != Value::Undefined && value != Value::Undefined {
                        let map = ctx.value.as_object_mut()?;
                        match map.get(&key) {
                            Some(pv) if *pv != value => {
                                let span = ke.span();
                                return Err(span.source.error(
                                    span.line,
                                    span.col,
                                    format!(
					"value for key `{}` generated multiple times: `{}` and `{}`",
					serde_json::to_string_pretty(&key)?,
					serde_json::to_string_pretty(&pv)?,
					serde_json::to_string_pretty(&value)?,
                                    )
                                    .as_str(),
                                ));
                            }
                            _ => map.insert(key, value),
                        };
                    } else {
                        match &ctx.value {
                            Value::Object(_) => (),
                            _ => ctx.value = Value::Undefined,
                        }
                    };
                }
                (None, Some(oe)) => {
                    let output = self.eval_expr(&oe)?;
                    let ctx = self.contexts.last_mut().unwrap();
                    if output != Value::Undefined {
                        match &mut ctx.value {
                            Value::Array(a) => {
                                Rc::make_mut(a).push(output);
                            }
                            Value::Set(ref mut s) => {
                                Rc::make_mut(s).insert(output);
                            }
                            a => bail!("internal error: invalid context value {a}"),
                        }
                    } else if !ctx.is_compr {
                        match &ctx.value {
                            Value::Set(_) => (),
                            _ => ctx.value = Value::Undefined,
                        }
                    }
                }
                // No output expression.
                // TODO: should we just push a Bool(true)?
                _ => (),
            }

            // If a query snippet is being run, gather results.
            let ctx = self.contexts.last_mut().expect("no current context");
            if let Some(result) = &ctx.result {
                let mut result = result.clone();
                if let Some(scope) = self.scopes.last() {
                    for (name, value) in scope.iter() {
                        result
                            .bindings
                            .as_object_mut()?
                            .insert(Value::String(name.to_string().into()), value.clone());
                    }
                }
                if result.expressions.iter().all(|v| v != &Value::Undefined)
                    && !result.expressions.is_empty()
                {
                    ctx.results.result.push(result);
                }
            }

            return Ok(true);
        }

        // Try out values in current loop expr.
        let loop_expr = &loops[0];
        let mut result = false;
        match self.eval_expr(&loop_expr.value)? {
            Value::Array(items) => {
                for v in items.iter() {
                    self.loop_var_values
                        .insert(loop_expr.expr.clone(), v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            Value::Set(items) => {
                for v in items.iter() {
                    self.loop_var_values
                        .insert(loop_expr.expr.clone(), v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            Value::Object(obj) => {
                for (_, v) in obj.iter() {
                    self.loop_var_values
                        .insert(loop_expr.expr.clone(), v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            _ => {
                return Err(loop_expr.span.source.error(
                    loop_expr.span.line,
                    loop_expr.span.col,
                    "item cannot be indexed",
                ));
            }
        }
        self.loop_var_values.remove(&loop_expr.expr);
        Ok(result)
    }

    fn get_current_context(&self) -> Result<&Context> {
        match self.contexts.last() {
            Some(ctx) => Ok(ctx),
            _ => bail!("internal error: no active context found"),
        }
    }

    fn get_exprs_from_context(&self) -> Result<ContextExprs> {
        let ctx = self.get_current_context()?;
        Ok((ctx.key_expr.clone(), ctx.output_expr.clone()))
    }

    fn eval_output_expr(&mut self) -> Result<bool> {
        // Evaluate output expression after all the statements have been executed.

        let (key_expr, output_expr) = self.get_exprs_from_context()?;
        let mut loops = vec![];

        if let Some(ke) = &key_expr {
            self.hoist_loops_impl(ke, &mut loops);
        }
        if let Some(oe) = &output_expr {
            self.hoist_loops_impl(oe, &mut loops);
        }

        self.eval_output_expr_in_loop(&loops[..])?;

        let ctx = self.get_current_context()?;
        if let Some(_oe) = &ctx.output_expr {
            // Ensure that at least one output was generated.
            Ok(ctx.value != Value::Undefined)
        } else {
            Ok(true)
        }
    }

    fn eval_stmts(&mut self, stmts: &[&LiteralStmt]) -> Result<bool> {
        let mut result = true;

        for (idx, stmt) in stmts.iter().enumerate() {
            if !result {
                break;
            }

            let loop_exprs = self.hoist_loops(&stmt.literal);
            if !loop_exprs.is_empty() {
                // If there are hoisted loop expressions, execute subsequent statements
                // within loops.
                return self.eval_stmts_in_loop(&stmts[idx..], &loop_exprs[..]);
            }

            result = self.eval_stmt(stmt, &stmts[idx + 1..])?;
            if matches!(&stmt.literal, Literal::SomeIn { .. }) {
                return Ok(result);
            }
        }

        if result {
            result = self.eval_output_expr()?;
        } else {
            // If a query snippet is being run, gather results.
            let ctx = self.contexts.last_mut().expect("no current context");
            if let Some(result) = &ctx.result {
                let mut result = result.clone();
                if let Some(scope) = self.scopes.last() {
                    for (name, value) in scope.iter() {
                        result
                            .bindings
                            .as_object_mut()?
                            .insert(Value::String(name.to_string().into()), value.clone());
                    }
                }
                if result.expressions.iter().all(|v| v != &Value::Undefined)
                    && !result.expressions.is_empty()
                {
                    ctx.results.result.push(result);
                }
            }
        }

        Ok(result)
    }

    fn eval_query(&mut self, query: &Ref<Query>) -> Result<bool> {
        // Execute the query in a new scope
        self.scopes.push(Scope::new());
        let ordered_stmts: Vec<&LiteralStmt> = if let Some(schedule) = &self.schedule {
            match schedule.order.get(query) {
                Some(ord) => ord.iter().map(|i| &query.stmts[*i as usize]).collect(),
                // TODO
                _ => bail!(query
                    .span
                    .error("statements not scheduled in query {query:?}")),
            }
        } else {
            query.stmts.iter().collect()
        };

        let r = self.eval_stmts(&ordered_stmts);
        self.scopes.pop();
        r
    }

    fn eval_array(&mut self, items: &Vec<ExprRef>) -> Result<Value> {
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
        let mut object = BTreeMap::new();

        for (_, key, value) in fields {
            // TODO: check this
            // While the grammar defines a object-item as
            // ( scalar | ref | var ) ":" term, the OPA
            // implementation is more like expr ":" expr
            let key = self.eval_expr(key)?;
            let value = self.eval_expr(value)?;
            object.insert(key, value);
        }

        Ok(Value::from_map(object))
    }

    fn eval_set(&mut self, items: &Vec<ExprRef>) -> Result<Value> {
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
        let value = self.eval_expr(value)?;
        let collection = self.eval_expr(collection)?;

        let result = match &collection {
            Value::Array(array) => {
                if let Some(key) = key {
                    let key = self.eval_expr(key)?;
                    collection[&key] == value
                } else {
                    array.iter().any(|item| *item == value)
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
        // Push new context
        self.contexts.push(Context {
            key_expr: None,
            output_expr: Some(term.clone()),
            value: Value::new_array(),
            result: None,
            results: QueryResults::default(),
            is_compr: true,
        });

        // Evaluate body first.
        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn eval_set_compr(&mut self, term: &ExprRef, query: &Ref<Query>) -> Result<Value> {
        // Push new context
        self.contexts.push(Context {
            key_expr: None,
            output_expr: Some(term.clone()),
            value: Value::new_set(),
            result: None,
            results: QueryResults::default(),
            is_compr: true,
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
        // Push new context
        self.contexts.push(Context {
            key_expr: Some(key.clone()),
            output_expr: Some(value.clone()),
            value: Value::new_object(),
            result: None,
            results: QueryResults::default(),
            is_compr: true,
        });

        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn lookup_function_by_name(&self, path: &str) -> Option<&Vec<Ref<Rule>>> {
        let mut path = path.to_owned();
        if !path.starts_with("data.") {
            path = self.current_module_path.clone() + "." + &path;
        }

        match self.functions.get(&path) {
            Some((f, _)) => Some(f),
            _ => None,
        }
    }

    fn eval_builtin_call(
        &mut self,
        span: &Span,
        name: &str,
        builtin: builtins::BuiltinFcn,
        params: &[ExprRef],
    ) -> Result<Value> {
        let mut args = vec![];
        let allow_undefined = name == "print"; // TODO: with modifier
        for p in params {
            match self.eval_expr(p)? {
                // If any argument is undefined, then the call is undefined.
                Value::Undefined if !allow_undefined => return Ok(Value::Undefined),
                p => args.push(p),
            }
        }

        let cache = builtins::must_cache(name);
        if let Some(name) = &cache {
            if let Some(v) = self.builtins_cache.get(&(name, args.clone())) {
                return Ok(v.clone());
            }
        }

        let v = builtin.0(span, params, &args[..])?;

        // Handle trace function.
        // TODO: with modifier.
        if let (Some(traces), Value::String(msg)) = (&mut self.traces, &v) {
            traces.push(msg.clone());
            return Ok(Value::Bool(true));
        };

        if let Some(name) = cache {
            self.builtins_cache.insert((name, args), v.clone());
        }
        Ok(v)
    }

    fn lookup_builtin(&self, span: &Span, path: &str) -> Result<Option<&BuiltinFcn>> {
        Ok(if let Some(builtin) = builtins::BUILTINS.get(path) {
            Some(builtin)
        } else if let Some(builtin) = builtins::DEPRECATED.get(path) {
            if !self.allow_deprecated {
                bail!(span.error(format!("{path} is deprecated").as_str()))
            }
            Some(builtin)
        } else {
            None
        })
    }

    fn eval_call_impl(&mut self, span: &Span, fcn: &ExprRef, params: &[ExprRef]) -> Result<Value> {
        let fcn_path = match get_path_string(fcn, None) {
            Ok(p) => p,
            _ => bail!(span.error("invalid function expression")),
        };

        let orig_fcn_path = fcn_path;
        let fcn_path = match self.with_functions.remove(&orig_fcn_path) {
            Some(p) => p,
            _ => orig_fcn_path.clone(),
        };

        let fcns_rules = match self.lookup_function_by_name(&fcn_path) {
            Some(r) => r,
            _ => {
                // Look up builtin function.
                if let Ok(Some(builtin)) = self.lookup_builtin(span, &fcn_path) {
                    let r = self.eval_builtin_call(span, &fcn_path.clone(), *builtin, params);
                    if orig_fcn_path != fcn_path {
                        self.with_functions.insert(orig_fcn_path, fcn_path);
                    }
                    return r;
                }
                bail!(span.error(format!("could not find function {fcn_path}").as_str()));
            }
        };

        let fcns = fcns_rules.clone();

        let mut results: Vec<Value> = Vec::new();
        let mut errors: Vec<anyhow::Error> = Vec::new();
        let mut param_values = Vec::with_capacity(params.len());
        for p in params {
            let v = self.eval_expr(p)?;
            if v == Value::Undefined {
                return Ok(v);
            }
            param_values.push(v);
        }

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

            let mut args_scope = Scope::new();
            for (idx, a) in args.iter().enumerate() {
                let a = match a.as_ref() {
                    Expr::Var(s) => s.source_str(),
                    _ => {
                        match self.eval_expr(a) {
                            Ok(a) => {
                                if a != param_values[idx] {
                                    // Skip this rule definition.
                                    continue 'outer;
                                }

                                continue;
                            }
                            _ => {
                                // TODO: destructuring function arguments.
                                continue;
                            }
                        }
                    }
                };
                //TODO: check call in params
                args_scope.insert(a, param_values[idx].clone());
            }

            let ctx = Context {
                key_expr: None,
                output_expr: output_expr.clone(),
                value: Value::new_set(),
                result: None,
                results: QueryResults::default(),
                is_compr: false,
            };

            // Back up local variables of current function and empty
            // the local variables of callee function.
            let scopes = std::mem::take(&mut self.scopes);

            // Set the arguments scope.
            self.scopes.push(args_scope);
            let value = match self.eval_rule_bodies(ctx, span, bodies) {
                Ok(v) => v,
                Err(e) => {
                    // If the rule produces an error, save the error.
                    errors.push(e);
                    self.scopes = scopes;
                    continue;
                }
            };

            let result = match &value {
                Value::Set(s) if s.len() == 1 => s.iter().next().unwrap().clone(),
                Value::Set(s) if !s.is_empty() => {
                    return Err(span.source.error(
                        span.line,
                        span.col,
                        format!("function produced multiple outputs {value:?}").as_str(),
                    ))
                }
                // If the function successfully executed, but did not return any value, then return true.
                Value::Set(s) if s.is_empty() && output_expr.is_none() => Value::Bool(true),

                // If the function execution resulted in undefined, then propagate it.
                Value::Undefined => Value::Undefined,
                _ => bail!("internal error: function did not return set {value:?}"),
            };

            // Restore local variables for current context.
            self.scopes = scopes;

            if result != Value::Undefined {
                results.push(result);
            }
        }

        if results.is_empty() {
            if errors.is_empty() {
                return Ok(Value::Undefined);
            } else {
                return Err(anyhow!(errors[0].to_string()));
            }
        }

        // all defined values should be the equal to the same value that should be returned
        if !results.windows(2).all(|w| w[0] == w[1]) {
            return Err(span.source.error(
                span.line,
                span.col,
                "functions must not produce multiple outputs for same inputs",
            ));
        }

        if orig_fcn_path != fcn_path {
            self.with_functions.insert(orig_fcn_path, fcn_path);
        }

        Ok(results[0].clone())
    }

    fn eval_call(
        &mut self,
        span: &Span,
        fcn: &ExprRef,
        params: &Vec<ExprRef>,
        extra_arg: Option<ExprRef>,
        allow_return_arg: bool,
    ) -> Result<Value> {
        // TODO: global var check; interop with `some var`
        if let Some(ea) = extra_arg {
            match ea.as_ref() {
                Expr::Var(var)
                    if allow_return_arg && self.lookup_local_var(&var.source_str()).is_none() =>
                {
                    let value = self.eval_call_impl(span, fcn, &params[..params.len() - 1])?;
                    if *var.text() != "_" {
                        self.add_variable(&var.source_str(), value)?;
                    }
                    Ok(Value::Bool(true))
                }
                _ => {
                    let ret_value = self.eval_call_impl(span, fcn, &params[..params.len() - 1])?;
                    let value = self.eval_expr(&ea)?;
                    Ok(Value::Bool(ret_value == value))
                }
            }
        } else {
            self.eval_call_impl(span, fcn, params)
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

    fn ensure_rule_evaluated(&mut self, path: String) -> Result<()> {
        if let Some(rules) = self.rules.get(&path) {
            for r in rules.clone() {
                if !self.processed.contains(&r) {
                    let module = self.get_rule_module(&r)?;
                    self.eval_rule(&module, &r)?;
                }
            }
        }
        // Evaluate the associated default rules after non-default rules
        if let Some(rules) = self.default_rules.get(&path) {
            for (r, _) in rules.clone() {
                if !self.processed.contains(&r) {
                    let module = self.get_rule_module(&r)?;
                    let prev_module = self.set_current_module(Some(module))?;
                    self.eval_default_rule(&r)?;
                    self.set_current_module(prev_module)?;
                }
            }
        }

        Ok(())
    }

    fn lookup_var(&mut self, span: &Span, fields: &[&str]) -> Result<Value> {
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
            return Err(span.error("undefined var"));
        }

        // Ensure that rules are evaluated
        if name.text() == "data" {
            let v = Self::get_value_chained(self.data.clone(), fields);

            // If the rule has already been evaluated or specified via a with modifier,
            // use that value.
            if v != Value::Undefined {
                return Ok(v);
            }

            // Evaluate rule corresponding to longest matching path.
            for i in (1..fields.len() + 1).rev() {
                let path = "data.".to_owned() + &fields[0..i].join(".");
                if self.rules.get(&path).is_some() || self.default_rules.get(&path).is_some() {
                    self.ensure_rule_evaluated(path)?;
                    break;
                }
            }

            Ok(Self::get_value_chained(self.data.clone(), fields))
        } else if !self.modules.is_empty() {
            let path = Parser::get_path_ref_components(&self.module.clone().unwrap().package.refr)?;
            let mut path: Vec<&str> = path.iter().map(|s| *s.text()).collect();
            path.push(name.text());

            let v = Self::get_value_chained(self.data.clone(), &path);

            // If the rule has already been evaluated or specified via a with modifier,
            // use that value.
            if v != Value::Undefined {
                return Ok(v);
            }

            // Add module prefix and ensure that any matching rule is evaluated.
            let module_path =
                Self::get_path_string(&self.current_module()?.package.refr, Some("data"))?;
            let rule_path = module_path + "." + name.text();

            self.ensure_rule_evaluated(rule_path)?;

            let value = Self::get_value_chained(self.data.clone(), &path[..]);
            Ok(Self::get_value_chained(value, fields))
        } else {
            Ok(Value::Undefined)
        }
    }

    fn eval_expr(&mut self, expr: &ExprRef) -> Result<Value> {
        match expr.as_ref() {
            Expr::Null(_) => Ok(Value::Null),
            Expr::True(_) => Ok(Value::Bool(true)),
            Expr::False(_) => Ok(Value::Bool(false)),
            Expr::Number(span) => match serde_json::from_str::<Value>(*span.text()) {
                Ok(v) => Ok(v),
                Err(e) => Err(span.source.error(
                    span.line,
                    span.col,
                    format!("could not parse number. {e}").as_str(),
                )),
            },
            // TODO: Handle string vs rawstring
            Expr::String(span) => {
                match serde_json::from_str::<Value>(format!("\"{}\"", span.text()).as_str()) {
                    Ok(s) => Ok(s),
                    Err(e) => bail!(span.error(format!("invalid string literal. {e}").as_str())),
                }
            }
            Expr::RawString(span) => Ok(Value::String(span.text().to_string().into())),

            // TODO: Handle undefined variables
            Expr::Var(_) => self.eval_chained_ref_dot_or_brack(expr),
            Expr::RefDot { .. } => self.eval_chained_ref_dot_or_brack(expr),
            Expr::RefBrack { .. } => self.eval_chained_ref_dot_or_brack(expr),

            // Expressions with operators
            Expr::ArithExpr { op, lhs, rhs, .. } => self.eval_arith_expr(op, lhs, rhs),
            Expr::AssignExpr { op, lhs, rhs, .. } => self.eval_assign_expr(op, lhs, rhs),
            Expr::BinExpr { op, lhs, rhs, .. } => self.eval_bin_expr(op, lhs, rhs),
            Expr::BoolExpr { op, lhs, rhs, .. } => self.eval_bool_expr(op, lhs, rhs),
            Expr::Membership {
                key,
                value,
                collection,
                ..
            } => self.eval_membership(key, value, collection),

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
            Expr::UnaryExpr { .. } => unimplemented!("unar expr is umplemented"),
            Expr::Call { span, fcn, params } => self.eval_call(span, fcn, params, None, false),
        }
    }

    fn make_rule_context(&self, head: &RuleHead) -> Result<(Context, Vec<Span>)> {
        let mut path = Parser::get_path_ref_components(&self.module.clone().unwrap().package.refr)?;

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
                        result: None,
                        results: QueryResults::default(),
                        is_compr: false,
                    },
                    path,
                ))
            }
            RuleHead::Set { refr, key, .. } => {
                Parser::get_path_ref_components_into(refr, &mut path)?;
                Ok((
                    Context {
                        key_expr: None,
                        output_expr: key.clone(),
                        value: Value::new_set(),
                        result: None,
                        results: QueryResults::default(),
                        is_compr: false,
                    },
                    path,
                ))
            }
            _ => unimplemented!("unhandled rule ref type"),
        }
    }

    fn get_rule_module(&self, rule: &Ref<Rule>) -> Result<Ref<Module>> {
        for m in &self.modules {
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
        bodies: &Vec<RuleBody>,
    ) -> Result<Value> {
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
                        key_expr: None,
                        output_expr,
                        value: Value::new_array(),
                        result: None,
                        results: QueryResults::default(),
                        is_compr: false,
                    });
                }
                result = self.eval_query(&body.query);

                if matches!(&result, Ok(true) | Err(_)) {
                    break;
                }
            }
            result
        };

        let ctx = match self.contexts.pop() {
            Some(ctx) => ctx,
            _ => bail!("internal error: rule's context already popped"),
        };

        let result = match result {
            Ok(r) => r,
            Err(e) => return Err(e),
        };

        assert_eq!(self.scopes.len(), n_scopes);

        Ok(match result {
            true => match &ctx.value {
                Value::Object(_) => ctx.value,
                Value::Array(a) if a.len() == 1 => a[0].clone(),
                Value::Array(a) if a.is_empty() => Value::Bool(true),
                Value::Array(_) => {
                    return Err(span.source.error(
                        span.line,
                        span.col,
                        "complete rules should not produce multiple outputs",
                    ))
                }
                Value::Set(_) => ctx.value,
                _ => unimplemented!("todo fix this: ctx.value = {:?}", ctx.value),
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
        if paths.is_empty() {
            return Ok(obj);
        }

        let key = Value::String(paths[0].into());
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
                Some(v) if paths.len() == 1 => Ok(v),
                Some(v) => Self::make_or_get_value_mut(v, &paths[1..]),
                _ => bail!("internal error: unexpected"),
            },
            Value::Undefined if paths.len() > 1 => {
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
        let mut expr = Some(refr);
        while expr.is_some() {
            match expr {
                Some(Expr::RefDot { refr, field, .. }) => {
                    comps.push(*field.text());
                    expr = Some(refr);
                }
                Some(Expr::RefBrack { refr, index, .. })
                    if matches!(index.as_ref(), Expr::String(_)) =>
                {
                    if let Expr::String(s) = index.as_ref() {
                        comps.push(*s.text());
                        expr = Some(refr);
                    }
                }
                Some(Expr::Var(v)) => {
                    comps.push(*v.text());
                    expr = None;
                }
                _ => bail!("internal error: not a simple ref"),
            }
        }
        if let Some(d) = document {
            comps.push(d);
        };
        comps.reverse();
        Ok(comps.join("."))
    }

    pub fn set_current_module(
        &mut self,
        module: Option<Ref<Module>>,
    ) -> Result<Option<Ref<Module>>> {
        let m = self.module.clone();
        if let Some(m) = &module {
            self.current_module_path = Self::get_path_string(&m.package.refr, Some("data"))?;
        }
        self.module = module;
        Ok(m.clone())
    }

    fn get_rule_refr(rule: &Rule) -> &ExprRef {
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
            String(_) | RawString(_) | Number(_) | True(_) | False(_) | Null(_) => return Ok(()),

            // Uminus of number is treated as a single expression,
            UnaryExpr { expr, .. } if matches!(expr.as_ref(), Number(_)) => return Ok(()),

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
            Var(span) => ("var", span),
            Call { span, .. } => ("call", span),
            UnaryExpr { span, .. } => ("unaryexpr", span),
            RefDot { span, .. } => ("ref", span),
            RefBrack { span, .. } => ("ref", span),
            BinExpr { span, .. } => ("binexpr", span),
            BoolExpr { span, .. } => ("boolexpr", span),
            ArithExpr { span, .. } => ("arithexpr", span),
            AssignExpr { span, .. } => ("assignexpr", span),
            Membership { span, .. } => ("membership", span),
        };

        Err(span.error(format!("invalid `{kind}` in default value").as_str()))
    }

    pub fn check_default_rules(&self) -> Result<()> {
        for module in &self.modules {
            for rule in &module.policy {
                if let Rule::Default { value, .. } = rule.as_ref() {
                    Self::check_default_value(value)?;
                }
            }
        }
        Ok(())
    }

    pub fn eval_default_rule(&mut self, rule: &Ref<Rule>) -> Result<()> {
        // Skip reprocessing rule.
        if self.processed.contains(rule) {
            return Ok(());
        }

        if let Rule::Default {
            span, refr, value, ..
        } = rule.as_ref()
        {
            let scopes = std::mem::take(&mut self.scopes);

            let mut path =
                Parser::get_path_ref_components(&self.module.clone().unwrap().package.refr)?;

            let (refr, index) = match refr.as_ref() {
                Expr::RefBrack { refr, index, .. } => (refr, Some(index.clone())),
                Expr::Var(_) => (refr, None),
                _ => bail!(refr.span().error(&format!(
                    "invalid token {:?} with the default keyword",
                    refr
                ))),
            };

            Parser::get_path_ref_components_into(refr, &mut path)?;
            let paths: Vec<&str> = path.iter().map(|s| *s.text()).collect();

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
            Err(span.error("value for rule has already been specified in data document"))
        }
    }

    pub fn eval_rule(&mut self, module: &Ref<Module>, rule: &Ref<Rule>) -> Result<()> {
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
                msg += span
                    .source
                    .message(span.line, span.col, "depends on", "")
                    .as_str();
            }
            msg += "cyclic evaluation";
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
        let scopes = std::mem::take(&mut self.scopes);
        let prev_module = self.set_current_module(Some(module.clone()))?;

        match rule.as_ref() {
            Rule::Spec {
                span,
                head: rule_head,
                bodies: rule_body,
            } => {
                match rule_head {
                    RuleHead::Compr { refr, .. } | RuleHead::Set { refr, .. } => {
                        let (ctx, mut path) = self.make_rule_context(rule_head)?;
                        let special_set =
                            matches!((&ctx.output_expr, &ctx.value), (None, Value::Set(_)));
                        let value = match self.eval_rule_bodies(ctx, span, rule_body)? {
                            Value::Set(_) if special_set => {
                                let entry = path[path.len() - 1].text();
                                let mut s = BTreeSet::new();
                                s.insert(Value::String(entry.to_string().into()));
                                path = path[0..path.len() - 1].to_vec();
                                Value::from_set(s)
                            }
                            v => v,
                        };

                        let paths: Vec<&str> = path.iter().map(|s| *s.text()).collect();

                        if let RuleHead::Set { .. } = &rule_head {
                            // Ensure that sets are created as empty.
                            let vref = Self::make_or_get_value_mut(&mut self.data, &paths)?;
                            if *vref == Value::Undefined {
                                *vref = Value::new_set();
                            }
                        }

                        self.update_data(span, refr, &paths[..], value)?;

                        self.processed.insert(rule.clone());
                    }
                    RuleHead::Func { refr, .. } => {
                        let mut path =
                            Parser::get_path_ref_components(&self.current_module()?.package.refr)?;

                        Parser::get_path_ref_components_into(refr, &mut path)?;
                        let path: Vec<&str> = path.iter().map(|s| *s.text()).collect();

                        // Ensure that for functions with a nesting level (e.g: a.foo),
                        // `a` is created as an empty object.
                        if path.len() > 1 {
                            self.update_data(
                                span,
                                refr,
                                &path[0..path.len() - 1],
                                Value::new_object(),
                            )?;
                        }
                    }
                }
            }
            _ => bail!("internal error: unexpected"),
        }
        self.set_current_module(prev_module)?;
        self.scopes = scopes;
        match self.active_rules.pop() {
            Some(ref r) if r == rule => Ok(()),
            _ => bail!("internal error: current rule not active"),
        }
    }

    pub fn eval_user_query(
        &mut self,
        query: &Ref<Query>,
        schedule: &Schedule,
        enable_tracing: bool,
    ) -> Result<QueryResults> {
        self.traces = match enable_tracing {
            true => Some(vec![]),
            false => None,
        };

        // Add schedules for queries.
        if let Some(self_schedule) = &mut self.schedule {
            for (k, v) in schedule.order.iter() {
                self_schedule.order.insert(k.clone(), v.clone());
            }
        }

        // Push new context.
        self.contexts.push(Context {
            key_expr: None,
            output_expr: None,
            value: Value::new_set(),
            // Request that results be gathered.
            result: Some(QueryResult::default()),
            results: QueryResults::default(),
            is_compr: false,
        });

        let prev_module = self.set_current_module(self.modules.last().cloned())?;

        // Eval the query.
        let query_r = self.eval_query(query);

        let mut results = match self.contexts.pop() {
            Some(ctx) => ctx.results,
            _ => bail!("internal error: no context"),
        };

        // Restore schedules.
        if let Some(self_schedule) = &mut self.schedule {
            for (k, ord) in schedule.order.iter() {
                if k == query {
                    for idx in 0..results.result.len() {
                        let mut ordered_expressions = vec![Value::Undefined; ord.len()];
                        for (expr_idx, value) in results.result[idx].expressions.iter().enumerate()
                        {
                            let orig_idx = ord[expr_idx] as usize;
                            ordered_expressions[orig_idx] = value.clone();
                        }
                        if !ordered_expressions.iter().any(|v| v == &Value::Undefined) {
                            results.result[idx].expressions = ordered_expressions;
                        }
                    }
                }
                self_schedule.order.remove(k);
            }
        }

        self.set_current_module(prev_module)?;

        match query_r {
            Ok(_) => Ok(results),
            Err(e) => Err(e),
        }
    }

    pub fn gather_rules(&mut self) -> Result<()> {
        for module in self.modules.clone() {
            let prev_module = self.set_current_module(Some(module.clone()))?;
            for rule in &module.policy {
                let refr = Self::get_rule_refr(rule);
                if let Rule::Spec { .. } = rule.as_ref() {
                    // Adjust refr to ensure simple ref.
                    // TODO: refactor.
                    let refr = match refr.as_ref() {
                        Expr::RefBrack { index, .. }
                            if matches!(index.as_ref(), Expr::String(_)) =>
                        {
                            refr
                        }
                        Expr::RefBrack { refr, .. } => refr,
                        _ => refr,
                    };
                    let path = Self::get_path_string(refr, None)?;
                    let path = self.current_module_path.clone() + "." + &path;
                    match self.rules.entry(path) {
                        Entry::Occupied(o) => {
                            o.into_mut().push(rule.clone());
                        }
                        Entry::Vacant(v) => {
                            v.insert(vec![rule.clone()]);
                        }
                    }
                } else if let Rule::Default { .. } = rule.as_ref() {
                    let (refr, index) = match refr.as_ref() {
                        // TODO: Validate the index
                        Expr::RefBrack { refr, index, .. } => {
                            if !matches!(
                                index.as_ref(),
                                Expr::True(_) | Expr::False(_) | Expr::Number(_) | Expr::String(_)
                            ) {
                                // OPA's behavior is ignoring the non-scalar index
                                bail!(index.span().error("index is not a scalar value"));
                            }

                            let index = self.eval_expr(index)?;

                            (refr, Some(index.to_string()))
                        }
                        _ => (refr, None),
                    };

                    let path = Self::get_path_string(refr, None)?;
                    let path = self.current_module_path.clone() + "." + &path;
                    match self.default_rules.entry(path) {
                        Entry::Occupied(o) => {
                            for (_, i) in o.get() {
                                if index.is_some() && i.is_some() {
                                    let old = i.as_ref().unwrap();
                                    let new = index.as_ref().unwrap();
                                    if old == new {
                                        bail!(refr.span().error("multiple default rules for the variable with the same index"));
                                    }
                                } else if index.is_some() || i.is_some() {
                                    bail!(refr
                                        .span()
                                        .error("conflict type with the default rules"));
                                }
                            }
                            o.into_mut().push((rule.clone(), index));
                        }
                        Entry::Vacant(v) => {
                            v.insert(vec![(rule.clone(), index)]);
                        }
                    }
                }
            }
            self.set_current_module(prev_module)?;
        }
        Ok(())
    }
}
