// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::builtins::{self, BuiltinFcn};
use crate::lexer::*;
use crate::number::*;
use crate::parser::Parser;
use crate::scheduler::*;
use crate::utils::*;
use crate::value::*;
use crate::Rc;
use crate::{Expression, Extension, Location, QueryResult, QueryResults};

use anyhow::{anyhow, bail, Result};
use std::collections::btree_map::Entry as BTreeMapEntry;
use std::collections::{hash_map::Entry, BTreeMap, BTreeSet, HashMap, HashSet};
use std::ops::Bound::*;
use std::str::FromStr;

type Scope = BTreeMap<SourceStr, Value>;

type DefaultRuleInfo = (Ref<Rule>, Option<String>);
type ContextExprs = (Option<Ref<Expr>>, Option<Ref<Expr>>);
type State = (
    Value,
    Value,
    Value,
    BTreeSet<Ref<Rule>>,
    Value,
    BTreeMap<String, FunctionModifier>,
    BTreeMap<Vec<Value>, (Value, Ref<Expr>)>,
);

#[derive(Debug, Clone)]
enum FunctionModifier {
    Function(String),
    Value(Value),
}

#[derive(Debug, Clone)]
pub struct Interpreter {
    modules: Vec<Ref<Module>>,
    module: Option<Ref<Module>>,
    schedule: Option<Schedule>,
    current_module_path: String,
    input: Value,
    data: Value,
    init_data: Value,
    with_document: Value,
    with_functions: BTreeMap<String, FunctionModifier>,
    scopes: Vec<Scope>,
    // TODO: handle recursive calls where same expr could have different values.
    loop_var_values: BTreeMap<ExprRef, Value>,
    contexts: Vec<Context>,
    functions: FunctionTable,
    rules: HashMap<String, Vec<Ref<Rule>>>,
    default_rules: HashMap<String, Vec<DefaultRuleInfo>>,
    processed: BTreeSet<Ref<Rule>>,
    processed_paths: Value,
    rule_values: BTreeMap<Vec<Value>, (Value, Ref<Expr>)>,
    active_rules: Vec<Ref<Rule>>,
    builtins_cache: BTreeMap<(&'static str, Vec<Value>), Value>,
    no_rules_lookup: bool,
    traces: Option<Vec<Rc<str>>>,
    allow_deprecated: bool,
    strict_builtin_errors: bool,
    imports: BTreeMap<String, Ref<Expr>>,
    extensions: HashMap<String, (u8, Rc<Box<dyn Extension>>)>,

    #[cfg(feature = "coverage")]
    coverage: HashMap<Source, Vec<bool>>,
    #[cfg(feature = "coverage")]
    enable_coverage: bool,

    gather_prints: bool,
    prints: Vec<String>,
    rule_paths: HashSet<String>,
}

impl Default for Interpreter {
    fn default() -> Self {
        Self::new()
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
        }
    }
}

#[derive(Debug)]
enum LoopExpr {
    Loop {
        span: Span,
        expr: Ref<Expr>,
        value: Ref<Expr>,
        index: Ref<Expr>,
    },
    Walk {
        span: Span,
        expr: Ref<Expr>,
    },
}

impl LoopExpr {
    fn span(&self) -> Span {
        match self {
            Self::Loop { span, .. } => span.clone(),
            Self::Walk { span, .. } => span.clone(),
        }
    }

    fn value(&self) -> Ref<Expr> {
        match self {
            Self::Loop { value, .. } => value.clone(),
            Self::Walk { expr, .. } => expr.clone(),
        }
    }

    fn expr(&self) -> Ref<Expr> {
        match self {
            Self::Loop { expr, .. } => expr.clone(),
            Self::Walk { expr, .. } => expr.clone(),
        }
    }

    fn index(&self) -> Option<Ref<Expr>> {
        match self {
            Self::Loop { index, .. } => Some(index.clone()),
            Self::Walk { .. } => None,
        }
    }
}

impl Interpreter {
    pub fn new() -> Interpreter {
        Interpreter {
            modules: vec![],
            module: None,
            schedule: None,
            current_module_path: String::default(),
            input: Value::Undefined,
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
            processed_paths: Value::new_object(),
            rule_values: BTreeMap::new(),
            active_rules: vec![],
            builtins_cache: BTreeMap::new(),
            no_rules_lookup: false,
            traces: None,
            allow_deprecated: true,
            strict_builtin_errors: true,
            imports: BTreeMap::default(),
            extensions: HashMap::new(),

            #[cfg(feature = "coverage")]
            coverage: HashMap::new(),
            #[cfg(feature = "coverage")]
            enable_coverage: false,

            gather_prints: false,
            prints: Vec::default(),
            rule_paths: HashSet::new(),
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

    pub fn set_strict_builtin_errors(&mut self, b: bool) {
        self.strict_builtin_errors = b;
    }

    pub fn set_input(&mut self, input: Value) {
        self.input = input;
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
        self.loop_var_values.clear();
        self.scopes = vec![Scope::new()];
        self.contexts = vec![];
        self.rule_values.clear();
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
                    return self.lookup_var(v, &path[..], false);
                }
                // Accumulate chained . field accesses.
                Expr::RefDot { refr, field, .. } => {
                    expr = refr;
                    path.push(field.text());
                }
                Expr::RefBrack { refr, index, .. } => match index.as_ref() {
                    // refr["field"] is the same as refr.field
                    Expr::String(s) => {
                        expr = refr;
                        path.push(s.text());
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
                                    ref_path + "." + &index
                                } else {
                                    ref_path + "." + &index + "." + &path.join(".")
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

                // hoist any loops in index expression.
                self.hoist_loops_impl(index, loops);

                // Then hoist the current bracket operation.
                let mut indices = Vec::with_capacity(1);
                let _ = traverse(index, &mut |e| match e.as_ref() {
                    Var(ident) if self.is_loop_index_var(&ident.source_str()) => {
                        indices.push(ident.source_str());
                        Ok(false)
                    }
                    Array { .. } | Object { .. } => Ok(true),
                    _ => Ok(false),
                });
                if !indices.is_empty() {
                    loops.push(LoopExpr::Loop {
                        span: span.clone(),
                        expr: expr.clone(),
                        value: refr.clone(),
                        index: index.clone(),
                    })
                }
            }

            // Primitives
            String(_) | RawString(_) | Number(_) | True(_) | False(_) | Null(_) | Var(_) => (),

            // Recurse into expressions in other variants.
            Array { items, .. } | Set { items, .. } | Call { params: items, .. } => {
                for item in items {
                    self.hoist_loops_impl(item, loops);
                }

                // Handle walk builtin which acts as a generator.
                // TODO: Handle with modifier on the walk builtin.
                if let Expr::Call { fcn, .. } = expr.as_ref() {
                    if let Ok(fcn_path) = get_path_string(fcn, None) {
                        if fcn_path == "walk" {
                            // TODO: Use an enum for LoopExpr to handle walk
                            loops.push(LoopExpr::Walk {
                                span: expr.span().clone(),
                                expr: expr.clone(),
                            })
                        }
                    }
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
                self.strict_builtin_errors,
            ),
        }
    }

    fn eval_assign_expr(&mut self, op: &AssignOp, lhs: &ExprRef, rhs: &ExprRef) -> Result<Value> {
        let (name, value) = match op {
            AssignOp::Eq => {
                match (lhs.as_ref(), rhs.as_ref()) {
                    (_, Expr::Var(var))
                        if var.source_str().text() != "input"
                            && self.lookup_var(var, &[], true)? == Value::Undefined =>
                    {
                        (var.source_str(), self.eval_expr(lhs)?)
                    }
                    (Expr::Var(var), _)
                        if var.source_str().text() != "input"
                            && self.lookup_var(var, &[], true)? == Value::Undefined =>
                    {
                        (var.source_str(), self.eval_expr(rhs)?)
                    }
                    (
                        Expr::Array {
                            items: lhs_items, ..
                        },
                        Expr::Array {
                            items: rhs_items,
                            span: rhs_span,
                        },
                    ) => {
                        if lhs_items.len() != rhs_items.len() {
                            bail!(rhs_span
                                .error("mismatch in number of array elements in lhs and rhs"));
                        }
                        for (lhs, rhs) in std::iter::zip(lhs_items.iter(), rhs_items.iter()) {
                            if self.eval_assign_expr(&AssignOp::Eq, lhs, rhs)? != Value::Bool(true)
                            {
                                return Ok(Value::Bool(false));
                            }
                        }
                        return Ok(Value::Bool(true));
                    }
                    (
                        Expr::Object {
                            fields: lhs_fields, ..
                        },
                        Expr::Object {
                            fields: rhs_fields,
                            span: rhs_span,
                        },
                    ) => {
                        if lhs_fields.len() != rhs_fields.len() {
                            bail!(rhs_span.error("mismatch in number of object keysin lhs and rhs"));
                        }

                        for ((_, lhs_key, lhs_value), (_, rhs_key, rhs_value)) in
                            std::iter::zip(lhs_fields.iter(), rhs_fields.iter())
                        {
                            if self.eval_bool_expr(&BoolOp::Eq, lhs_key, rhs_key)?
                                != Value::Bool(true)
                            {
                                return Ok(Value::Bool(false));
                            }

                            if self.eval_assign_expr(&AssignOp::Eq, lhs_value, rhs_value)?
                                != Value::Bool(true)
                            {
                                return Ok(Value::Bool(false));
                            }
                        }
                        return Ok(Value::Bool(true));
                    }
                    (Expr::Array { .. }, _) => {
                        let value = self.eval_expr(rhs)?;
                        let mut cache = BTreeMap::new();
                        let mut type_match = BTreeSet::new();
                        return self
                            .make_bindings(false, &mut type_match, &mut cache, lhs, &value, false)
                            .map(Value::Bool);
                    }
                    (_, Expr::Array { .. }) => {
                        let value = self.eval_expr(lhs)?;
                        let mut cache = BTreeMap::new();
                        let mut type_match = BTreeSet::new();
                        return self
                            .make_bindings(false, &mut type_match, &mut cache, rhs, &value, false)
                            .map(Value::Bool);
                    }
                    (Expr::Object { .. }, _) => {
                        let value = self.eval_expr(rhs)?;
                        let mut cache = BTreeMap::new();
                        let mut type_match = BTreeSet::new();
                        return self
                            .make_bindings(false, &mut type_match, &mut cache, lhs, &value, false)
                            .map(Value::Bool);
                    }
                    (_, Expr::Object { .. }) => {
                        let value = self.eval_expr(lhs)?;
                        let mut cache = BTreeMap::new();
                        let mut type_match = BTreeSet::new();
                        return self
                            .make_bindings(false, &mut type_match, &mut cache, rhs, &value, false)
                            .map(Value::Bool);
                    }
                    // Treat the assignment as comparison if neither lhs nor rhs is a variable
                    _ => {
                        let r = self.eval_bool_expr(&BoolOp::Eq, lhs, rhs)?;
                        if r == Value::Bool(false) {
                            return Ok(Value::Undefined);
                        }
                        return Ok(r);
                    }
                }
            }
            AssignOp::ColEq => {
                let rhs_value = self.eval_expr(rhs)?;
                if rhs_value == Value::Undefined {
                    return Ok(rhs_value);
                }

                let name = if let Expr::Var(span) = lhs.as_ref() {
                    span.source_str()
                } else {
                    let mut cache = BTreeMap::new();
                    let mut type_match = BTreeSet::new();
                    return self
                        .make_bindings(false, &mut type_match, &mut cache, lhs, &rhs_value, false)
                        .map(Value::Bool);
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

                (name, rhs_value)
            }
        };

        // Omit recording undefined values.
        if value == Value::Undefined {
            return Ok(value); //Ok(Value::Bool(false));
        }

        self.add_variable_or(&name)?;

        // TODO: optimize this
        self.variables_assignment(&name, &value)?;

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
            Value::Undefined | Value::Null => r = false,
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
        check_existing_value: bool,
    ) -> Result<bool> {
        // Propagate undefined.
        if value == &Value::Undefined {
            return Ok(false);
        }
        let span = expr.span();
        let raise_error = is_last && type_match.get(expr).is_none();

        match (expr.as_ref(), value) {
            (Expr::Var(ident), _) if ident.text() == "_" => Ok(true),
            (Expr::Var(ident), _)
                if check_existing_value
                    && self.lookup_local_var(&ident.source_str()) == Some(value.clone()) =>
            {
                Ok(false)
            }

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

                let mut r = true;
                for (idx, item) in items.iter().enumerate() {
                    r = self.make_bindings(
                        is_last,
                        type_match,
                        cache,
                        item,
                        &a[idx],
                        check_existing_value,
                    )? && r;
                }

                Ok(r)
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
                            check_existing_value,
                        )?;
                }
                type_match.insert(expr.clone());

                Ok(r)
            }
            // TODO: This suppresses errors in case of type mismatches.
            // OPA raises the error sometimes in static scenarios, but doesn't
            // raise in scenarios due to data/input
            (Expr::Array { .. }, _) | (Expr::Object { .. }, _) => Ok(false),

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
        check_existing_value: bool,
    ) -> Result<bool> {
        let prev = self.no_rules_lookup;
        self.no_rules_lookup = true;
        let r = self.make_bindings_impl(
            is_last,
            type_match,
            cache,
            expr,
            value,
            check_existing_value,
        );
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
            if !self.make_bindings(is_last, type_match, cache, key_expr, key, false)? {
                return Ok(false);
            }
        }
        self.make_bindings(is_last, type_match, cache, value_expr, value, false)
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
                        (&Value::from(idx), value),
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
        Ok(match &stmt.literal {
            Literal::Expr { span, expr, .. } => {
                let value = match expr.as_ref() {
                    Expr::Call { span, fcn, params } => self.eval_call(
                        span,
                        expr,
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
                        expr,
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
                    if self.current_scope()?.get(&name).is_some() {
                        bail!("duplicated definition of local variable {}", name);
                    }
                    self.add_variable_or(&name)?;
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
            let processed_paths = std::mem::replace(&mut self.processed_paths, Value::new_object());
            self.rule_values.clear();

            let mut skip_exec = false;
            // Apply with modifiers.
            for wm in &stmt.with_mods {
                let path = Parser::get_path_ref_components(&wm.refr)?;
                let path: Vec<&str> = path.iter().map(|s| s.text()).collect();
                let mut target = path.join(".");

                let mut target_is_function = self.lookup_function_by_name(&target).is_some()
                    || matches!(self.lookup_builtin(wm.refr.span(), &target), Ok(Some(_)));

                if !target_is_function
                    && !target.starts_with("data.")
                    && !target.starts_with("input.")
                    && target != "input"
                {
                    // target must be a function.
                    if self.lookup_function_by_name(&target).is_none()
                        && !matches!(self.lookup_builtin(wm.refr.span(), &target), Ok(Some(_)))
                    {
                        // Prefix target with current module path.
                        target = self.current_module_path.clone() + "." + &target;
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
                                    && !matches!(
                                        self.lookup_builtin(wm.r#as.span(), &function_path),
                                        Ok(Some(_))
                                    )
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
                    if path[0] == "input" || path[0] == "data" {
                        // Override existing values in case of conflict.
                        let mut obj = &mut self.with_document;
                        for p in &path[0..path.len()] {
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
                        if let Some(rules) = self.rules.get(&target) {
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

            // Apply with modifiers before evaluating the loop expression.
            let (saved_state, _) = self.apply_with_modifiers(stmts[0])?;

            let loop_expr_value = loop_expr.value();
            let loop_expr_value = if let Expr::Call { span, fcn, params } = loop_expr_value.as_ref()
            {
                // Handle walk(obj, output_param)
                let extra_arg = get_extra_arg(
                    &loop_expr_value,
                    Some(self.current_module_path.as_str()),
                    &self.functions,
                );
                // If there is an extra arg, ignore it while computing the loop value.
                let params = if extra_arg.is_some() {
                    &params[..params.len() - 1]
                } else {
                    &params[..]
                };
                self.eval_call_impl(span, &loop_expr_value, fcn, params)?
            } else {
                self.eval_expr(&loop_expr_value)?
            };

            // Restore with modifiers.
            // TODO: Delay this restore so that the stmt doesn't have to apply with modifiers again.
            self.restore_state(saved_state)?;

            // If the loop's index variable h<as already been assigned a value
            // (this can happen if the same index is used for two different collections),
            // then evaluate statements only if the index applies to this collection.
            let loop_expr_index = loop_expr.index();
            if let Some(Expr::Var(index_var)) = loop_expr_index.as_ref().map(|r| r.as_ref()) {
                if let Some(idx) = self.lookup_local_var(&index_var.source_str()) {
                    if loop_expr_value[&idx] != Value::Undefined {
                        result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                        return Ok(result);
                    } else if idx != Value::Undefined {
                        // The index is not valid for this collection.
                        return Ok(false);
                    }
                }
            }

            // Create a new scope.
            self.scopes.push(Scope::default());

            let query_result = self.get_current_context()?.result.clone();
            match loop_expr_value {
                Value::Array(items) => {
                    for (idx, v) in items.iter().enumerate() {
                        self.loop_var_values.insert(loop_expr.expr(), v.clone());

                        let exec = if let Some(index) = loop_expr.index() {
                            let mut type_match = BTreeSet::new();
                            let mut cache = BTreeMap::new();
                            self.make_bindings(
                                false,
                                &mut type_match,
                                &mut cache,
                                &index,
                                &Value::from(idx),
                                true,
                            )?
                        } else {
                            true
                        };
                        if exec {
                            result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                        }

                        Self::clear_scope(self.current_scope_mut()?);
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result = query_result.clone();
                        }
                    }

                    self.loop_var_values.remove(&loop_expr.expr());
                }
                Value::Set(items) => {
                    for v in items.iter() {
                        self.loop_var_values.insert(loop_expr.expr(), v.clone());

                        // For sets, index is also the value.
                        let exec = if let Some(index) = loop_expr.index() {
                            let mut type_match = BTreeSet::new();
                            let mut cache = BTreeMap::new();
                            self.make_bindings(false, &mut type_match, &mut cache, &index, v, true)?
                        } else {
                            true
                        };
                        if exec {
                            result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                        }

                        Self::clear_scope(self.current_scope_mut()?);
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result = query_result.clone();
                        }
                    }
                    self.loop_var_values.remove(&loop_expr.expr());
                }
                Value::Object(obj) => {
                    for (k, v) in obj.iter() {
                        self.loop_var_values.insert(loop_expr.expr(), v.clone());
                        // For objects, index is key.
                        let exec = if let Some(index) = loop_expr.index() {
                            let mut type_match = BTreeSet::new();
                            let mut cache = BTreeMap::new();
                            self.make_bindings(false, &mut type_match, &mut cache, &index, k, true)?
                        } else {
                            true
                        };
                        if exec {
                            result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                        }

                        Self::clear_scope(self.current_scope_mut()?);
                        if let Some(ctx) = self.contexts.last_mut() {
                            ctx.result = query_result.clone();
                        }
                    }
                    self.loop_var_values.remove(&loop_expr.expr());
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

    fn eval_rule_ref(&mut self, refr: &ExprRef) -> Result<Vec<Value>> {
        let mut comps = vec![];
        let mut expr = refr;
        loop {
            match expr.as_ref() {
                Expr::Var(v) => {
                    comps.push(Value::String(v.text().into()));
                    break;
                }
                Expr::RefBrack { refr, index, .. } => {
                    comps.push(self.eval_expr(index)?);
                    expr = refr;
                }
                Expr::RefDot { refr, field, .. } => {
                    comps.push(Value::String(field.text().into()));
                    expr = refr;
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
            if idx == len - 1 {
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

    fn eval_output_expr_in_loop(&mut self, loops: &[LoopExpr]) -> Result<bool> {
        if loops.is_empty() {
            let (key_expr, output_expr) = self.get_exprs_from_context()?;

            let ctx = self.get_current_context()?;
            let (is_set, is_old_style_set) = (ctx.is_set, ctx.is_old_style_set);
            if let Some(rule_ref) = ctx.rule_ref.clone() {
                let mut comps = self.eval_rule_ref(&rule_ref)?;
                if let Some(ke) = &key_expr {
                    comps.push(self.eval_expr(ke)?);
                }
                let output = if let Some(oe) = &output_expr {
                    self.eval_expr(oe)?
                } else if is_old_style_set && !comps.is_empty() {
                    let output = comps[comps.len() - 1].clone();
                    comps.pop();
                    output
                } else {
                    Value::Bool(true)
                };

                let comps_defined = comps.iter().all(|v| v != &Value::Undefined);
                let ctx = self.contexts.last_mut().expect("no current context");

                if output == Value::Undefined || !comps_defined {
                    return Ok(false);
                }

                if is_set {
                    // Ensure that set rule is created even if the element is undefined.
                    let set = ctx
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
                match ctx
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
                if result.expressions.len() == 1 // Single expression query
                    || result // Multi expression query where no value is false
                       .expressions
                       .iter()
                       .all(|v| v.value != Value::Undefined && v.value != Value::Bool(false))
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
        match self.eval_expr(&loop_expr.value())? {
            Value::Array(items) => {
                for v in items.iter() {
                    self.loop_var_values.insert(loop_expr.expr(), v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            Value::Set(items) => {
                for v in items.iter() {
                    self.loop_var_values.insert(loop_expr.expr(), v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            Value::Object(obj) => {
                for (_, v) in obj.iter() {
                    self.loop_var_values.insert(loop_expr.expr(), v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            _ => {
                return Err(loop_expr.span().source.error(
                    loop_expr.span().line,
                    loop_expr.span().col,
                    "item cannot be indexed",
                ));
            }
        }
        self.loop_var_values.remove(&loop_expr.expr());
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

                if result.expressions.len() == 1 // Single expression query
                    || result // Multi expression query where no value is false
                    .expressions
                    .iter()
                    .all(|v| v.value != Value::Undefined && v.value != Value::Bool(false))
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
            path = self.current_module_path.clone() + "." + &path;
        }

        match self.functions.get(&path) {
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
    ) -> Result<Value> {
        let mut args = vec![];
        let is_print = name == "print"; // TODO: with modifier
        let allow_undefined = is_print;
        for p in params {
            match self.eval_expr(p)? {
                // If any argument is undefined, then the call is undefined.
                Value::Undefined if !allow_undefined => return Ok(Value::Undefined),
                p => args.push(p),
            }
        }

        if is_print && self.gather_prints {
            // Do not print to stderr. Instead, gather.
            let msg =
                builtins::print_to_string(span, params, &args[..], self.strict_builtin_errors)?;

            // Prefix location information.
            self.prints
                .push(format!("{}:{}: {msg}", span.source.file(), span.line));
            return Ok(Value::Bool(true));
        }

        let cache = builtins::must_cache(name);
        if let Some(name) = &cache {
            if let Some(v) = self.builtins_cache.get(&(name, args.clone())) {
                return Ok(v.clone());
            }
        }

        let v = match builtin.0(span, params, &args[..], self.strict_builtin_errors) {
            Ok(v) => v,
            // Ignore errors if we are not evaluating in strict mode.
            Err(_) if !self.strict_builtin_errors => return Ok(Value::Undefined),
            Err(e) => Err(e)?,
        };

        // Handle trace function.
        // TODO: with modifier.
        if name == "trace" {
            if let (Some(traces), Value::String(msg)) = (&mut self.traces, &v) {
                traces.push(msg.clone());
                return Ok(Value::Bool(true));
            }
        }

        if let Some(name) = cache {
            self.builtins_cache.insert((name, args), v.clone());
        }
        Ok(v)
    }

    fn lookup_builtin(&self, span: &Span, path: &str) -> Result<Option<&BuiltinFcn>> {
        if let Some(builtin) = builtins::BUILTINS.get(path) {
            return Ok(Some(builtin));
        }

        #[cfg(feature = "deprecated")]
        if let Some(builtin) = builtins::DEPRECATED.get(path) {
            let allow = self.allow_deprecated && !self.current_module()?.rego_v1;
            if !allow {
                bail!(span.error(format!("{path} is deprecated").as_str()))
            }
            return Ok(Some(builtin));
        }

        // Mark as used when deprecated feature is not enabled.
        std::convert::identity((span, self.allow_deprecated));

        Ok(None)
    }

    fn eval_call_impl(
        &mut self,
        span: &Span,
        expr: &ExprRef,
        fcn: &ExprRef,
        params: &[ExprRef],
    ) -> Result<Value> {
        // Return generated values of walk builtin.
        if let Some(v) = self.loop_var_values.get(expr) {
            return Ok(v.clone());
        }

        let fcn_path = match get_path_string(fcn, None) {
            Ok(p) => p,
            _ => bail!(span.error("invalid function expression")),
        };

        let mut param_values = Vec::with_capacity(params.len());
        let mut error = None;
        for p in params {
            match self.eval_expr(p) {
                Ok(v) => param_values.push(v),
                Err(e) => {
                    error = Some(Err(e));
                    break;
                }
            }
        }

        let orig_fcn_path = fcn_path;

        let mut with_functions_saved = None;
        let fcn_path = match self.with_functions.get(&orig_fcn_path) {
            Some(FunctionModifier::Function(p)) => {
                let p = p.clone();
                with_functions_saved = Some(self.with_functions.clone());
                self.with_functions.clear();
                p
            }
            Some(FunctionModifier::Value(v)) => {
                if param_values.iter().any(|v| v == &Value::Undefined) {
                    return Ok(Value::Undefined);
                }
                if let Some(err) = error {
                    err?;
                };
                return Ok(v.clone());
            }
            _ => orig_fcn_path.clone(),
        };

        let mut extension = None;
        let empty: Vec<Ref<Rule>> = vec![];
        let (fcns_rules, fcn_module) = match self.lookup_function_by_name(&fcn_path) {
            Some((fcns, m)) => (fcns, Some(m.clone())),
            _ => {
                if self.default_rules.get(&fcn_path).is_some()
                    || self
                        .default_rules
                        .get(&get_path_string(fcn, Some(&self.current_module_path))?)
                        .is_some()
                {
                    // process default functions later.
                    (&empty, self.module.clone())
                }
                // Look up extension.
                else if let Some(ext) = self.extensions.get_mut(&fcn_path) {
                    extension = Some(ext);
                    (&empty, None)
                }
                // Look up builtin function.
                else if let Some(builtin) = self.lookup_builtin(span, &fcn_path)? {
                    let r = self.eval_builtin_call(span, &fcn_path.clone(), *builtin, params);
                    if let Some(with_functions) = with_functions_saved {
                        self.with_functions = with_functions;
                    }
                    return r;
                } else {
                    bail!(span.error(format!("could not find function {fcn_path}").as_str()));
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
            if param_values.len() != *nargs as usize {
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
            let scopes = std::mem::take(&mut self.scopes);

            // Set the arguments scope.
            let args_scope = Scope::new();
            self.scopes.push(args_scope);

            let mut cache = BTreeMap::new();
            let mut type_match = BTreeSet::new();

            for (idx, a) in args.iter().enumerate() {
                let b = self.make_bindings(
                    false,
                    &mut type_match,
                    &mut cache,
                    a,
                    &param_values[idx],
                    false,
                );

                if b.ok() != Some(true) {
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

        if self.strict_builtin_errors && !errors.is_empty() {
            return Err(anyhow!(errors[0].to_string()));
        }

        if results.is_empty() {
            // Back up local variables of current function and empty
            // the local variables of callee function.
            let scopes = std::mem::take(&mut self.scopes);
            if errors.is_empty() {
                // Check if any default rules can be evaluated.
                // TODO: with mod
                let rules = match self.default_rules.get(&fcn_path).cloned() {
                    Some(rules) => Some(rules),
                    None => {
                        let fcn_path = get_path_string(fcn, Some(&self.current_module_path))?;
                        self.default_rules.get(&fcn_path).cloned()
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

        Ok(results[0].clone())
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
        // TODO: global var check; interop with `some var`
        if let Some(ea) = extra_arg {
            match ea.as_ref() {
                Expr::Var(var)
                    if allow_return_arg && self.lookup_local_var(&var.source_str()).is_none() =>
                {
                    let value =
                        self.eval_call_impl(span, expr, fcn, &params[..params.len() - 1])?;
                    if var.text() != "_" {
                        self.add_variable(&var.source_str(), value)?;
                    }
                    Ok(Value::Bool(true))
                }
                _ if allow_return_arg => {
                    let ret_value =
                        self.eval_call_impl(span, expr, fcn, &params[..params.len() - 1])?;
                    let mut cache = BTreeMap::new();
                    let mut type_match = BTreeSet::new();
                    self.make_bindings(false, &mut type_match, &mut cache, &ea, &ret_value, false)
                        .map(Value::Bool)
                }
                _ => {
                    let expected = self.eval_expr(&params[params.len() - 1])?;
                    let ret_value =
                        self.eval_call_impl(span, expr, fcn, &params[..params.len() - 1])?;
                    Ok(Value::Bool(ret_value == expected))
                }
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
        for module in self.modules.clone() {
            if Some(&module) == self.module.as_ref() {
                // Prevent cyclic evaluation.
                continue;
            }
            let module_path = get_path_string(&module.package.refr, Some("data"))?;
            if module_path.starts_with(&path)
                && (module_path.len() == path.len()
                    || &module_path[path.len()..path.len() + 1] == ".")
            {
                // Ensure that the module is created.
                let path = Parser::get_path_ref_components(&module.package.refr)?;
                let path: Vec<&str> = path.iter().map(|s| s.text()).collect();
                let vref = Self::make_or_get_value_mut(&mut self.data, &path[..])?;
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
                self.mark_processed(&path)?;
            }
        }

        Ok(())
    }

    fn ensure_rule_evaluated(&mut self, path: String) -> Result<()> {
        let mut matched = false;
        if let Some(rules) = self.rules.get(&path) {
            matched = true;
            for r in rules.clone() {
                if !self.processed.contains(&r) {
                    let module = self.get_rule_module(&r)?;
                    self.eval_rule(&module, &r)?;
                }
            }
        }

        // Evaluate the associated default rules after non-default rules
        if let Some(rules) = self.default_rules.get(&path) {
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
            self.mark_processed(&comps[1..])?;
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
                for module in self.modules.clone() {
                    for rule in &module.policy {
                        self.eval_rule(&module, rule)?;
                    }
                }
            }

            // With modifiers may be used to specify part of a module that that not yet been
            // evaluated. Therefore ensure that module is evaluated first.
            let path = "data.".to_owned() + &fields.join(".");
            self.ensure_module_evaluated(path.clone())?;

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
            let mut path: Vec<&str> = path.iter().map(|s| s.text()).collect();
            path.push(name.text());

            if self.is_processed(&path)? {
                let value = Self::get_value_chained(self.data.clone(), &path);
                return Ok(Self::get_value_chained(value, fields));
            }

            // Ensure that all the rules having common prefix (name) are evaluated.
            let rule_path = "data.".to_owned() + &path.join(".");

            if !no_error
                && self.rules.get(&rule_path).is_none()
                && self.default_rules.get(&rule_path).is_none()
                && self.imports.get(&rule_path).is_none()
            {
                bail!(span.error("var is unsafe"));
            }

            // Find the rule to which the var being looked up corresponds to. This is the prefix for
            // which rules exist.
            let mut found = false;
            for i in (0..fields.len() + 1).rev() {
                let comps = &fields[0..i];
                let path = if comps.is_empty() {
                    rule_path.clone()
                } else {
                    rule_path.clone() + "." + &fields[0..i].join(".")
                };

                if self.rules.get(&path).is_some() || self.default_rules.get(&path).is_some() {
                    self.ensure_rule_evaluated(path)?;
                    found = true;
                    break;
                }
            }

            if !found {
                if let Some(imported_var) = self.imports.get(&rule_path).cloned() {
                    return Ok(Self::get_value_chained(
                        self.eval_expr(&imported_var)?,
                        fields,
                    ));
                }
            }

            let value = Self::get_value_chained(self.data.clone(), &path[..]);
            Ok(Self::get_value_chained(value, fields))
        } else {
            Ok(Value::Undefined)
        }
    }

    fn eval_expr(&mut self, expr: &ExprRef) -> Result<Value> {
        #[cfg(feature = "coverage")]
        if self.enable_coverage {
            let span = expr.span();
            let source = &span.source;
            let line = span.line as usize;
            if line > 0 {
                // Check if coverage table already exists for source.
                match self.coverage.get_mut(source) {
                    Some(c) => {
                        // Ensure that current line is valid.
                        if c.len() < line + 1 {
                            c.resize(line + 1, false);
                        }
                        c[line] = true;
                    }
                    _ => {
                        // Create new table.
                        let mut c = vec![false; line + 1];
                        c[line] = true;
                        self.coverage.insert(source.clone(), c);
                    }
                }
            }
        }

        match expr.as_ref() {
            Expr::Null(_) => Ok(Value::Null),
            Expr::True(_) => Ok(Value::Bool(true)),
            Expr::False(_) => Ok(Value::Bool(false)),
            Expr::Number(span) => {
                let v = match Number::from_str(span.text()) {
                    Ok(v) => Ok(Value::Number(v)),
                    Err(_) => Err(span
                        .source
                        .error(span.line, span.col, "could not parse number")),
                };
                v
            }
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
            Expr::ArithExpr { op, lhs, rhs, .. } => self.eval_arith_expr(expr.span(), op, lhs, rhs),
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
            Expr::UnaryExpr { span, expr: uexpr } => match uexpr.as_ref() {
                Expr::Number(_) if !uexpr.span().text().starts_with('-') => {
                    builtins::numbers::arithmetic_operation(
                        span,
                        &ArithOp::Sub,
                        expr,
                        uexpr,
                        Value::from(0),
                        self.eval_expr(uexpr)?,
                        self.strict_builtin_errors,
                    )
                }
                _ => bail!(expr
                    .span()
                    .error("unary - can only be used with numeric literals")),
            },
            Expr::Call { span, fcn, params } => {
                self.eval_call(span, expr, fcn, params, None, false)
            }
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
        bodies: &[RuleBody],
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

        let ctx = match self.contexts.pop() {
            Some(ctx) => ctx,
            _ => bail!("internal error: rule's context already popped"),
        };

        let result = match result {
            Ok(r) => r,
            Err(e) => return Err(e),
        };

        assert_eq!(self.scopes.len(), n_scopes);

        if ctx.rule_ref.is_some() {
            if result {
                return Ok(ctx.rule_value);
            } else {
                return Ok(Value::Undefined);
            }
        }

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
        while let Some(e) = expr {
            match e {
                Expr::RefDot { refr, field, .. } => {
                    comps.push(field.text());
                    expr = Some(refr);
                }
                Expr::RefBrack { refr, index, .. } if matches!(index.as_ref(), Expr::String(_)) => {
                    if let Expr::String(s) = index.as_ref() {
                        comps.push(s.text());
                        expr = Some(refr);
                    }
                }
                Expr::Var(v) => {
                    comps.push(v.text());
                    expr = None;
                }
                _ => bail!(e.span().error("invalid ref expression")),
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

            let scopes = std::mem::take(&mut self.scopes);

            let mut path =
                Parser::get_path_ref_components(&self.module.clone().unwrap().package.refr)?;

            let (refr, index) = match refr.as_ref() {
                Expr::RefBrack { refr, index, .. } => (refr, Some(index.clone())),
                Expr::RefDot { .. } => (refr, None),
                Expr::Var(_) => (refr, None),
                _ => bail!(refr.span().error(&format!(
                    "invalid token {:?} with the default keyword",
                    refr
                ))),
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
                            for (path, value) in value.as_object()? {
                                let mut full_path = package_components.clone();
                                full_path.append(&mut path.as_array()?.clone());
                                self.check_rule_path(refr, &full_path, value, is_set)?;
                                self.update_rule_value(span, full_path, value.clone(), is_set)?;
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
                        if path.len() > 1 {
                            self.update_data(
                                span,
                                refr,
                                &path[0..path.len() - 1],
                                Value::new_object(),
                            )?;
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
        let scopes = std::mem::take(&mut self.scopes);
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
            value: Value::new_set(),
            // Request that results be gathered.
            result: Some(QueryResult::default()),
            ..Context::default()
        });

        let prev_module = self.set_current_module(Some(module.clone()))?;

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
                        let e = Expression {
                            value: Value::Undefined,
                            text: "".into(),
                            location: Location { row: 0, col: 0 },
                        };
                        let mut ordered_expressions =
                            vec![e; results.result[idx].expressions.len()];
                        for (expr_idx, value) in results.result[idx].expressions.iter().enumerate()
                        {
                            let orig_idx = ord[expr_idx] as usize;
                            ordered_expressions[orig_idx] = value.clone();
                        }
                        if !ordered_expressions
                            .iter()
                            .any(|v| v.value == Value::Undefined)
                        {
                            results.result[idx].expressions = ordered_expressions;
                        }
                    }
                }
                self_schedule.order.remove(k);
            }
        }

        self.set_current_module(prev_module)?;

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
                Expr::Var(v) => {
                    components.push(v.text().into());
                    break;
                }
                Expr::RefBrack { refr, index, .. } => {
                    if let Expr::String(s) = index.as_ref() {
                        components.push(s.text().into());
                    } else {
                        components.clear();
                    }
                    refr
                }
                Expr::RefDot { refr, field, .. } => {
                    components.push(field.text().into());
                    refr
                }
                _ => break,
            }
        }
        components.reverse();
        Ok(components)
    }

    pub fn create_rule_prefixes(&mut self) -> Result<()> {
        for module in self.modules.clone() {
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

                if components.len() > 1 {
                    components.pop();
                } else {
                    continue;
                }

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
        for c in 0..comps.len() {
            let path = self.current_module_path.clone() + "." + &comps[0..c + 1].join(".");
            if c + 1 == comps.len() {
                self.rule_paths.insert(path.clone());
            }

            match self.rules.entry(path) {
                Entry::Occupied(o) => {
                    o.into_mut().push(rule.clone());
                }
                Entry::Vacant(v) => {
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
        for (idx, c) in (0..comps.len()).enumerate() {
            let path = self.current_module_path.clone() + "." + &comps[0..c + 1].join(".");
            if c + 1 == comps.len() {
                self.rule_paths.insert(path.clone());
            }

            match self.default_rules.entry(path) {
                Entry::Occupied(o) => {
                    if idx + 1 == comps.len() {
                        for (_, i) in o.get() {
                            if index.is_some() && i.is_some() {
                                let old = i.as_ref().unwrap();
                                let new = index.as_ref().unwrap();
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
                Entry::Vacant(v) => {
                    v.insert(vec![(rule.clone(), index.clone())]);
                }
            }
        }

        Ok(())
    }

    pub fn process_imports(&mut self) -> Result<()> {
        for module in &self.modules {
            let module_path = get_path_string(&module.package.refr, Some("data"))?;
            for import in &module.imports {
                let target = match &import.r#as {
                    Some(s) => s.text(),
                    _ => match import.refr.as_ref() {
                        Expr::RefDot { field, .. } => field.text(),
                        Expr::RefBrack { index, .. } => match index.as_ref() {
                            Expr::String(s) => s.text(),
                            _ => "",
                        },
                        Expr::Var(v) if v.text() == "input" => {
                            // Warn redundant import of input. Ignore it.
                            eprintln!(
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
                self.imports
                    .insert(module_path.clone() + "." + target, import.refr.clone());
            }
        }
        Ok(())
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
                    self.record_rule(refr, rule.clone())?;
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
        if let std::collections::hash_map::Entry::Vacant(v) = self.extensions.entry(path) {
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
                Literal::Every { domain, query, .. } => {
                    self.gather_coverage_in_expr(domain, covered, file)?;
                    self.gather_coverage_in_query(query, covered, file)?;
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
                    let line = e.span().line as usize;
                    if line >= covered.len() || !covered[line] {
                        file.not_covered.insert(line as u32);
                    } else if line < covered.len() && covered[line] {
                        file.covered.insert(line as u32);
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

        for module in self.modules.iter() {
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
        self.coverage = HashMap::new();
    }

    pub fn set_gather_prints(&mut self, b: bool) {
        if b != self.gather_prints {
            // Clear existing prints.
            std::mem::take(&mut self.prints);
        }
        self.gather_prints = b;
    }

    pub fn take_prints(&mut self) -> Result<Vec<String>> {
        Ok(std::mem::take(&mut self.prints))
    }

    pub fn eval_rule_in_path(&mut self, path: String) -> Result<Value> {
        if !self.rule_paths.contains(&path) {
            bail!("not a valid rule path");
        }
        self.ensure_rule_evaluated(path.clone())?;
        let parts: Vec<&str> = path.split('.').collect();

        Ok(Self::get_value_chained(self.data.clone(), &parts[1..]))
    }
}
