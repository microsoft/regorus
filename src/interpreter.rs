// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::builtins;
use crate::lexer::Span;
use crate::parser::Parser;
use crate::value::*;

use anyhow::{anyhow, bail, Result};
use log::info;
use std::collections::{hash_map::Entry, BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

type Scope = BTreeMap<String, Variable>;

pub struct Interpreter<'source> {
    modules: Vec<&'source Module<'source>>,
    module: Option<&'source Module<'source>>,
    current_module_path: String,
    input: Value,
    data: Value,
    scopes: Vec<Scope>,
    // TODO: handle recursive calls where same expr could have different values.
    loop_var_values: BTreeMap<&'source Expr<'source>, Value>,
    contexts: Vec<Context<'source>>,
    functions: HashMap<String, &'source Rule<'source>>,
    rules: HashMap<String, Vec<&'source Rule<'source>>>,
    default_rules: HashMap<String, Vec<(&'source Rule<'source>, Option<String>)>>,
    processed: BTreeSet<&'source Rule<'source>>,
    active_rules: Vec<&'source Rule<'source>>,
}

#[derive(Debug)]
struct Variable {
    value: Value,
    partial: bool,
    _has_default: bool,
}

#[derive(Debug, Clone)]
struct Context<'source> {
    key_expr: Option<&'source Expr<'source>>,
    output_expr: Option<&'source Expr<'source>>,
    value: Value,
}

#[derive(Debug)]
struct LoopExpr<'source> {
    span: &'source Span<'source>,
    expr: &'source Expr<'source>,
    value: &'source Expr<'source>,
}

impl<'source> Interpreter<'source> {
    pub fn new(modules: Vec<&'source Module<'source>>) -> Result<Interpreter<'source>> {
        Ok(Interpreter {
            modules,
            module: None,
            current_module_path: String::default(),
            input: Value::new_object(),
            data: Value::new_object(),
            scopes: vec![Scope::new()],
            contexts: vec![],
            loop_var_values: BTreeMap::new(),
            functions: HashMap::new(),
            rules: HashMap::new(),
            default_rules: HashMap::new(),
            processed: BTreeSet::new(),
            active_rules: vec![],
        })
    }

    fn current_module(&self) -> Result<&'source Module<'source>> {
        match &self.module {
            Some(m) => Ok(m),
            _ => bail!("internal error: current module not set"),
        }
    }

    #[inline(always)]
    fn add_variable(
        &mut self,
        name: &str,
        partial: bool,
        default: Option<Value>,
    ) -> Result<(String, Value)> {
        let name = name.to_string();

        // Only add the variable if the key is not "_"
        let value = if name != "_" {
            let (value, _has_default) = if let Some(default) = default {
                (default, true)
            } else {
                (Value::Undefined, false)
            };

            let variable = Variable {
                value: value.clone(),
                partial,
                _has_default,
            };

            match self.scopes.last_mut() {
                Some(scope) => {
                    scope.insert(name.to_string(), variable);
                }
                _ => bail!("internal error: no active scope"),
            }
            value
        } else {
            Value::Undefined
        };
        Ok((name, value))
    }

    fn add_variable_or(
        &mut self,
        name: &str,
        partial: bool,
        default: Option<Value>,
    ) -> Result<(String, Value, bool)> {
        for scope in self.scopes.iter().rev() {
            if let Some(variable) = scope.get(&name.to_string()) {
                return Ok((name.to_string(), variable.value.clone(), variable.partial));
            }
        }

        let (name, value) = self.add_variable(name, partial, default)?;
        Ok((name, value, partial))
    }

    // TODO: optimize this
    fn variables_assignment(&mut self, name: &str, value: &Value) -> Result<()> {
        match self.scopes.last_mut() {
            Some(scope) => {
                if let Some(variable) = scope.get_mut(name) {
                    variable.value = value.clone();
                } else {
                    return Err(anyhow!("variable {} is undefined", name));
                }
            }
            _ => bail!("internal error: no active scope"),
        }

        Ok(())
    }

    fn eval_chained_ref_dot_or_brack(&mut self, mut expr: &'source Expr<'source>) -> Result<Value> {
        // Collect a chaing of '.field' or '["field"]'
        let mut path = vec![];
        loop {
            match expr {
                // Stop path collection upon encountering the leading variable.
                Expr::Var(v) => {
                    path.reverse();
                    return self.lookup_var(v.text(), &path[..]);
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
                        let obj = self.eval_expr(refr)?;
                        let index = self.eval_expr(index)?;
                        return Ok(Self::get_value_chained(obj[&index].clone(), &path[..]));
                    }
                },
                _ => {
                    path.reverse();
                    return Ok(Self::get_value_chained(self.eval_expr(expr)?, &path[..]));
                }
            }
        }
    }

    fn is_loop_var(&self, ident: &str) -> bool {
        // TODO: check for vars that are declared using some-vars
        // TODO: check for vars that are not declared and dont exist in any scope including global.
        ident == "_"
    }

    fn hoist_loops_impl(&self, expr: &'source Expr<'source>, loops: &mut Vec<LoopExpr<'source>>) {
        use Expr::*;
        match expr {
            RefBrack { refr, index, span } => {
                // First hoist any loops in refr
                self.hoist_loops_impl(refr, loops);

                // Then hoist the current bracket operation.
                match index.as_ref() {
                    Var(ident) if self.is_loop_var(ident.text()) => loops.push(LoopExpr {
                        span,
                        expr,
                        //var: ident.text(),
                        value: refr,
                    }),
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
                self.hoist_loops_impl(key, loops);
                if let Some(value) = value.as_ref() {
                    self.hoist_loops_impl(value, loops);
                }
                self.hoist_loops_impl(collection, loops);
            }

            // The output expressions of comprehensions must be subject to hoisting
            // only after evaluating the body of the comprehensions since the output
            // expressions may depend on variables defined within the body.
            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => (),
        }
    }

    fn hoist_loops(&self, literal: &'source Literal<'source>) -> Vec<LoopExpr<'source>> {
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
                self.hoist_loops_impl(key, &mut loops);
                if let Some(value) = value {
                    self.hoist_loops_impl(value, &mut loops);
                }
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
        lhs_expr: &'source Expr<'source>,
        rhs_expr: &'source Expr<'source>,
    ) -> Result<Value> {
        let lhs = self.eval_expr(lhs_expr)?;
        let rhs = self.eval_expr(rhs_expr)?;
        Ok(builtins::compare(op, &lhs, &rhs))
    }

    fn eval_bin_expr(
        &mut self,
        op: &BinOp,
        lhs: &'source Expr<'source>,
        rhs: &'source Expr<'source>,
    ) -> Result<Value> {
        let lhs = self.eval_expr(lhs)?;
        let rhs = self.eval_expr(rhs)?;

        let lhs = if let Value::Set(set) = lhs {
            set
        } else {
            return Err(anyhow!("expect {:?} to be a set", lhs));
        };

        let rhs = if let Value::Set(set) = rhs {
            set
        } else {
            return Err(anyhow!("expect {:?} to be a set", rhs));
        };

        info!(
            "eval_bin_expr, op: {:?}, lhs: {:?}, rhs: {:?}",
            op, lhs, rhs
        );

        Ok(Value::from_set(match op {
            BinOp::Or => lhs.union(&rhs).cloned().collect(),
            BinOp::And => lhs.intersection(&rhs).cloned().collect(),
        }))
    }

    fn eval_arith_expr(
        &mut self,
        op: &ArithOp,
        lhs: &'source Expr<'source>,
        rhs: &'source Expr<'source>,
    ) -> Result<Value> {
        let lhs = self.eval_expr(lhs)?;
        let rhs = self.eval_expr(rhs)?;

        // Handle special case for set difference.
        if let (Value::Set(lhs), ArithOp::Sub, Value::Set(rhs)) = (&lhs, op, &rhs) {
            return Ok(Value::from_set(lhs.difference(rhs).cloned().collect()));
        }

        let lhs = if let Value::Number(number) = lhs {
            number.0
        } else {
            return Err(anyhow!("expect {:?} to be a number", lhs));
        };

        let rhs = if let Value::Number(number) = rhs {
            number.0
        } else {
            return Err(anyhow!("expect {:?} to be a number", rhs));
        };

        let result = match op {
            ArithOp::Add => lhs + rhs,
            ArithOp::Sub => lhs - rhs,
            ArithOp::Mul => lhs * rhs,
            ArithOp::Div => lhs / rhs,
        };

        info!(
            "eval_arith_expr, op: {:?}, lhs: {:?}, rhs: {:?}",
            op, lhs, rhs
        );

        Ok(Value::Number(Number(result)))
    }

    fn eval_assign_expr(
        &mut self,
        op: &AssignOp,
        lhs: &'source Expr<'source>,
        rhs: &'source Expr<'source>,
    ) -> Result<Value> {
        let lhs = if let Expr::Var(span) = lhs {
            span.text()
        } else {
            return Err(anyhow!("expect a variable, got: {:?}", lhs));
        };

        let (_, variable, _) = self.add_variable_or(lhs, false, None)?;

        let rhs = self.eval_expr(rhs)?;

        // TODO: handle iterations
        if variable[0] != Value::Undefined {
            return Err(anyhow!("Redefinition for variable {:?}", lhs));
        }

        // TODO: optimize this
        self.variables_assignment(lhs, &rhs)?;

        info!(
            "eval_assign_expr before, op: {:?}, lhs: {:?}, rhs: {:?}",
            op, lhs, rhs
        );

        Ok(Value::Bool(true))
    }

    fn eval_stmt(&mut self, stmt: &'source LiteralStmt<'source>) -> Result<bool> {
        let mut to_restore = vec![];
        for wm in &stmt.with_mods {
            // Evaluate value and ref
            let value = self.eval_expr(&wm.r#as)?;
            let path = Parser::get_path_ref_components(&wm.refr)?;
            let mut path: Vec<&str> = path.iter().map(|s| s.text()).collect();

            // TODO: multiple modules and qualified path
            if path.len() > 2 && format!("{}.{}", path[0], path[1]) == self.current_module_path {
                path = path[1..].to_vec();
            }

            // Set new values in modifications table
            let mut saved = false;
            for (i, _) in path.iter().enumerate() {
                let vref = Self::make_or_get_value_mut(&mut self.data, &path[0..i])?;
                if vref == &Value::Undefined {
                    to_restore.push((path[0..i].to_vec(), vref.clone()));
                    saved = false;
                    break;
                }
            }

            // TODO: input
            let vref = Self::make_or_get_value_mut(&mut self.data, &path[..])?;
            if !saved {
                to_restore.push((path, vref.clone()));
            }

            *vref = value;
        }

        let r = Ok(match &stmt.literal {
            Literal::Expr { expr, .. } => {
                let value = self.eval_expr(expr)?;
                if let Value::Bool(bool) = value {
                    bool
                } else {
                    // panic!();
                    // TODO: confirm this
                    // For non-booleans, treat anything other than undefined as true
                    value != Value::Undefined
                }
            }
            Literal::SomeVars { vars, .. } => {
                for var in vars {
                    let name = var.text();
                    if let Ok((_, variable, _)) = self.add_variable_or(name, false, None) {
                        if variable != Value::Undefined {
                            return Err(anyhow!(
                                "duplicated definition of local variable {}",
                                name
                            ));
                        }
                    }
                }
                true
            }
            Literal::SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                let value = self.eval_membership(key, value, collection)?;
                if let Value::Bool(bool) = value {
                    bool
                } else {
                    panic!();
                }
            }
            _ => unimplemented!(),
        });

        for (path, value) in to_restore.into_iter().rev() {
            if value == Value::Undefined {
                unimplemented!("handle undefined restore");
            } else {
                let vref = Self::make_or_get_value_mut(&mut self.data, &path[..])?;
                *vref = value;
            }
        }
        r
    }

    fn eval_stmts_in_loop(
        &mut self,
        stmts: &'source [LiteralStmt<'source>],
        loops: &[LoopExpr<'source>],
    ) -> Result<bool> {
        if loops.is_empty() {
            if !stmts.is_empty() {
                // Evaluate the current statement whose loop expressions have been hoisted.
                if !self.eval_stmt(&stmts[0])? {
                    return Ok(false);
                }
                self.eval_stmts(&stmts[1..])
            } else {
                self.eval_stmts(stmts)
            }
        } else {
            let loop_expr = &loops[0];
            let mut result = false;
            match self.eval_expr(loop_expr.value)? {
                Value::Array(items) => {
                    for v in items.iter() {
                        self.loop_var_values.insert(loop_expr.expr, v.clone());
                        result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                    }
                }
                Value::Set(items) => {
                    for v in items.iter() {
                        self.loop_var_values.insert(loop_expr.expr, v.clone());
                        result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
                    }
                }
                Value::Object(obj) => {
                    for (_, v) in obj.iter() {
                        self.loop_var_values.insert(loop_expr.expr, v.clone());
                        result = self.eval_stmts_in_loop(stmts, &loops[1..])? || result;
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
            self.loop_var_values.remove(loop_expr.expr);
            // Return true if at least on iteration returned true
            Ok(result)
        }
    }

    fn eval_output_expr_in_loop(&mut self, loops: &[LoopExpr<'source>]) -> Result<bool> {
        if loops.is_empty() {
            let (key_expr, output_expr) = self.get_exprs_from_context()?;

            match (key_expr, output_expr) {
                (Some(ke), Some(oe)) => {
                    let key = self.eval_expr(ke)?;
                    let value = self.eval_expr(oe)?;

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
                        ctx.value = Value::Undefined;
                    };
                }
                (None, Some(oe)) => {
                    let output = self.eval_expr(oe)?;
                    let ctx = self.contexts.last_mut().unwrap();
                    if output != Value::Undefined {
                        match &mut ctx.value {
                            Value::Array(a) => {
                                Rc::make_mut(a).push(output);
                            }
                            Value::Set(ref mut s) => {
                                Rc::make_mut(s).insert(output);
                            }
                            _ => bail!("internal error: invalid context value"),
                        }
                    } else {
                        ctx.value = Value::Undefined;
                    }
                }
                // No output expression.
                // TODO: should we just push a Bool(true)?
                _ => (),
            }

            // Push the context back so that it is available to the caller.
            //            self.contexts.push(ctx);
            return Ok(true);
        }

        // Try out values in current loop expr.
        let loop_expr = &loops[0];
        let mut result = false;
        match self.eval_expr(loop_expr.value)? {
            Value::Array(items) => {
                for v in items.iter() {
                    self.loop_var_values.insert(loop_expr.expr, v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            Value::Set(items) => {
                for v in items.iter() {
                    self.loop_var_values.insert(loop_expr.expr, v.clone());
                    result = self.eval_output_expr_in_loop(&loops[1..])? || result;
                }
            }
            Value::Object(obj) => {
                for (_, v) in obj.iter() {
                    self.loop_var_values.insert(loop_expr.expr, v.clone());
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
        self.loop_var_values.remove(loop_expr.expr);
        Ok(result)
    }

    fn get_current_context(&self) -> Result<&Context<'source>> {
        match self.contexts.last() {
            Some(ctx) => Ok(ctx),
            _ => bail!("internal error: no active context found"),
        }
    }

    fn get_exprs_from_context(
        &self,
    ) -> Result<(
        Option<&'source Expr<'source>>,
        Option<&'source Expr<'source>>,
    )> {
        let ctx = self.get_current_context()?;
        Ok((ctx.key_expr, ctx.output_expr))
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
        if let Some(_oe) = ctx.output_expr {
            // Ensure that at least one output was generated.
            Ok(ctx.value != Value::Undefined)
        } else {
            Ok(true)
        }
    }

    fn eval_stmts(&mut self, stmts: &'source [LiteralStmt<'source>]) -> Result<bool> {
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
            result = self.eval_stmt(stmt)?;
        }

        if result {
            result = self.eval_output_expr()?;
        }
        Ok(result)
    }

    fn eval_query(&mut self, query: &'source Query<'source>) -> Result<bool> {
        // Execute the query in a new scope
        self.scopes.push(Scope::new());
        let r = self.eval_stmts(&query.stmts);
        self.scopes.pop();
        r
    }

    fn eval_array(&mut self, items: &'source Vec<Expr<'source>>) -> Result<Value> {
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

    fn eval_object(&mut self, fields: &'source Vec<(Span, Expr, Expr)>) -> Result<Value> {
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

    fn eval_set(&mut self, items: &'source Vec<Expr<'source>>) -> Result<Value> {
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
        key: &'source Expr<'source>,
        value: &'source Option<Expr<'source>>,
        collection: &'source Expr<'source>,
    ) -> Result<Value> {
        let key = self.eval_expr(key)?;

        let collection = self.eval_expr(collection)?;

        let result = match &collection {
            Value::Array(array) => {
                if let Some(value) = value {
                    let value = self.eval_expr(value)?;
                    collection[&key] == value
                } else {
                    array.iter().any(|item| *item == key)
                }
            }
            Value::Object(object) => {
                if let Some(value) = value {
                    let value = self.eval_expr(value)?;
                    collection[&key] == value
                } else {
                    object.values().into_iter().any(|item| *item == key)
                }
            }
            Value::Set(set) => {
                if value.is_some() {
                    false
                    //return Err(anyhow!("key-value pair is not supported for set"));
                } else {
                    set.contains(&key)
                }
            }
            _ => {
                return Err(anyhow!("\"{}\" must be array, object, or set", collection));
            }
        };

        Ok(Value::Bool(result))
    }

    fn eval_array_compr(
        &mut self,
        term: &'source Expr<'source>,
        query: &'source Query<'source>,
    ) -> Result<Value> {
        // Push new context
        self.contexts.push(Context {
            key_expr: None,
            output_expr: Some(term),
            value: Value::new_array(),
        });

        // Evaluate body first.
        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn eval_set_compr(
        &mut self,
        term: &'source Expr<'source>,
        query: &'source Query<'source>,
    ) -> Result<Value> {
        // Push new context
        self.contexts.push(Context {
            key_expr: None,
            output_expr: Some(term),
            value: Value::new_set(),
        });

        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn eval_object_compr(
        &mut self,
        key: &'source Expr<'source>,
        value: &'source Expr<'source>,
        query: &'source Query<'source>,
    ) -> Result<Value> {
        // Push new context
        self.contexts.push(Context {
            key_expr: Some(key),
            output_expr: Some(value),
            value: Value::new_object(),
        });

        self.eval_query(query)?;

        match self.contexts.pop() {
            Some(ctx) => Ok(ctx.value),
            None => bail!("internal error: context already popped"),
        }
    }

    fn lookup_function(&self, fcn: &'source Expr<'source>) -> Result<&'source Rule<'source>> {
        let mut path = Self::get_path_string(fcn, None)?;
        if !path.starts_with("data.") {
            path = self.current_module_path.clone() + "." + &path;
        }

        match self.functions.get(&path) {
            Some(r) => Ok(r),
            _ => {
                bail!("function not found")
            }
        }
    }

    fn eval_call(
        &mut self,
        span: &'source Span<'source>,
        fcn: &'source Expr<'source>,
        params: &'source Vec<Expr<'source>>,
    ) -> Result<Value> {
        let fcn_rule = match self.lookup_function(fcn) {
            Ok(r) => r,
            _ => {
                return Err(span
                    .source
                    .error(span.line, span.col, "could not find function"))
            }
        };

        let (args, output_expr, bodies) = match fcn_rule {
            Rule::Spec {
                head: RuleHead::Func { args, assign, .. },
                bodies,
                ..
            } => (args, assign.as_ref().map(|a| &a.value), bodies),
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
            let a = match a {
                Expr::Var(s) => s.text(),
                _ => unimplemented!("destructuring function arguments"),
            };
            //TODO: check call in params
            args_scope.insert(
                a.to_string(),
                Variable {
                    value: self.eval_expr(&params[idx])?,
                    partial: false,
                    _has_default: false,
                },
            );
        }

        let ctx = Context {
            key_expr: None,
            output_expr,
            value: Value::new_set(),
        };

        // Back up local variables of current function and empty
        // the local variables of callee function.
        let scopes = std::mem::take(&mut self.scopes);

        // Set the arguments scope.
        self.scopes.push(args_scope);
        let value = self.eval_rule_bodies(ctx, span, bodies)?;
        let result = match &value {
            Value::Set(s) if s.len() == 1 => Ok(s.iter().next().unwrap().clone()),
            Value::Set(s) if !s.is_empty() => Err(span.source.error(
                span.line,
                span.col,
                format!("function produced multiple outputs {value:?}").as_str(),
            )),
            // If the function successfully executed, but did not return any value, then return true.
            Value::Set(s) if s.is_empty() && output_expr.is_none() => Ok(Value::Bool(true)),

            // If the function execution resulted in undefined, then propagate it.
            Value::Undefined => Ok(Value::Undefined),
            _ => bail!("internal error: function did not return set {value:?}"),
        };

        // Restore local variables for current context.
        self.scopes = scopes;
        result
    }

    fn get_var_value(&self, name: &str) -> Option<Value> {
        // Lookup local variables and arguments.
        for scope in self.scopes.iter().rev() {
            if let Some(v) = scope.get(name) {
                return Some(v.value.clone());
            }
        }
        None
    }

    fn ensure_rule_evaluated(&mut self, path: String) -> Result<()> {
        if let Some(rules) = self.rules.get(&path) {
            for r in rules.clone() {
                if !self.processed.contains(r) {
                    let module = self.get_rule_module(r)?;
                    self.eval_rule(module, r)?;
                }
            }
        }
        // Evaluate the associated default rules after non-default rules
        if let Some(rules) = self.default_rules.get(&path) {
            for (r, _) in rules.clone() {
                if !self.processed.contains(r) {
                    let module = self.get_rule_module(r)?;
                    let prev_module = self.set_current_module(Some(module))?;
                    self.eval_default_rule(r)?;
                    self.set_current_module(prev_module)?;
                }
            }
        }
        Ok(())
    }

    fn lookup_var(&mut self, name: &str, fields: &[&str]) -> Result<Value> {
        // Return local variable/argument.
        if let Some(v) = self.get_var_value(name) {
            return Ok(Self::get_value_chained(v, fields));
        }

        // Handle input.
        if name == "input" {
            return Ok(Self::get_value_chained(self.input.clone(), fields));
        }

        // Ensure that rules are evaluated
        if name == "data" {
            // Evaluate rule corresponding to longest matching path.
            for i in (1..fields.len() + 1).rev() {
                let path = "data.".to_owned() + &fields[0..i].join(".");
                if self.rules.get(&path).is_some() || self.default_rules.get(&path).is_some() {
                    self.ensure_rule_evaluated(path)?;
                    break;
                }
            }
            Ok(Self::get_value_chained(self.data.clone(), fields))
        } else {
            // Add module prefix and ensure that any matching rule is evaluated.
            let module_path =
                Self::get_path_string(&self.current_module()?.package.refr, Some("data"))?;
            let path = module_path + "." + name;
            self.ensure_rule_evaluated(path)?;

            let mut path: Vec<&str> =
                Parser::get_path_ref_components(&self.module.unwrap().package.refr)?
                    .iter()
                    .map(|s| s.text())
                    .collect();
            path.push(name);

            let value = Self::get_value_chained(self.data.clone(), &path[..]);
            Ok(Self::get_value_chained(value, fields))
        }
    }

    fn eval_expr(&mut self, expr: &'source Expr<'source>) -> Result<Value> {
        match expr {
            Expr::Null(_) => Ok(Value::Null),
            Expr::True(_) => Ok(Value::Bool(true)),
            Expr::False(_) => Ok(Value::Bool(false)),
            Expr::Number(span) => match serde_json::from_str::<Value>(span.text()) {
                Ok(v) => Ok(v),
                Err(e) => Err(span.source.error(
                    span.line,
                    span.col,
                    format!("could not parse number. {e}").as_str(),
                )),
            },
            // TODO: Handle string vs rawstring
            Expr::String(span) => Ok(Value::String(span.text().to_string())),
            Expr::RawString(span) => Ok(Value::String(span.text().to_string())),

            // TODO: Handle undefined variables
            Expr::Var(_) => self.eval_chained_ref_dot_or_brack(expr),
            Expr::RefDot { .. } => self.eval_chained_ref_dot_or_brack(expr),
            Expr::RefBrack { .. } => match self.loop_var_values.get(expr) {
                Some(v) => Ok(v.clone()),
                _ => self.eval_chained_ref_dot_or_brack(expr),
            },

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
            Expr::Call { span, fcn, params } => self.eval_call(span, fcn, params),
        }
    }

    fn make_rule_context(
        &self,
        head: &'source RuleHead<'source>,
    ) -> Result<(Context<'source>, Vec<Span<'source>>)> {
        //TODO: include "data" ?
        let mut path = Parser::get_path_ref_components(&self.module.unwrap().package.refr)?;

        match head {
            RuleHead::Compr { refr, assign, .. } => {
                let output_expr = assign.as_ref().map(|assign| &assign.value);
                let (refr, key_expr, value) = match refr {
                    Expr::RefBrack { refr, index, .. } => {
                        (refr.as_ref(), Some(index.as_ref()), Value::new_object())
                    }
                    _ => (refr, None, Value::new_array()),
                };

                Parser::get_path_ref_components_into(refr, &mut path)?;

                Ok((
                    Context {
                        key_expr,
                        output_expr,
                        value,
                    },
                    path,
                ))
            }
            RuleHead::Set { refr, key, .. } => {
                Parser::get_path_ref_components_into(refr, &mut path)?;
                Ok((
                    Context {
                        key_expr: None,
                        output_expr: key.as_ref(),
                        value: Value::new_set(),
                    },
                    path,
                ))
            }
            _ => unimplemented!("unhandled rule ref type"),
        }
    }

    fn get_rule_module(&self, rule: &'source Rule<'source>) -> Result<&'source Module<'source>> {
        for m in &self.modules {
            if m.policy.contains(rule) {
                return Ok(m);
            }
        }
        bail!("internal error: could not find module for rule");
    }

    fn eval_rule_bodies(
        &mut self,
        ctx: Context<'source>,
        span: &'source Span<'source>,
        bodies: &'source Vec<RuleBody<'source>>,
    ) -> Result<Value> {
        let mut result = true;
        self.scopes.push(Scope::new());

        if bodies.is_empty() {
            self.contexts.push(ctx.clone());
            result = self.eval_output_expr()?;
        } else {
            for body in bodies {
                self.contexts.push(ctx.clone());
                result = self.eval_query(&body.query)?;

                // The body evaluated successfully.
                if result {
                    break;
                }

                if bodies.len() > 1 {
                    unimplemented!("else bodies");
                }
            }
        }

        let ctx = match self.contexts.pop() {
            Some(ctx) => ctx,
            _ => bail!("internal error: rule's context already popped"),
        };

        // Drop local variables and leave the local scope
        self.scopes.pop();

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
                _ => unimplemented!("todo fix this"),
            },
            false => Value::Undefined,
        })
    }

    fn get_value_chained(mut obj: Value, path: &[&str]) -> Value {
        for p in path {
            obj = obj[&Value::String(p.to_string())].clone();
        }
        obj
    }

    #[inline]
    fn make_or_get_value_mut<'a>(obj: &'a mut Value, paths: &[&str]) -> Result<&'a mut Value> {
        if paths.is_empty() {
            return Ok(obj);
        }

        let key = Value::String(paths[0].to_owned());
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
            _ => bail!("make: not an object {obj:?}"),
        }
    }

    pub fn merge_value(span: &Span<'source>, value: &mut Value, mut new: Value) -> Result<()> {
        match (value, &mut new) {
            (v @ Value::Undefined, _) => *v = new,
            (Value::Set(ref mut set), Value::Set(new)) => {
                Rc::make_mut(set).append(Rc::make_mut(new))
            }
            (Value::Object(map), Value::Object(new)) => {
                for (k, v) in new.iter() {
                    match map.get(k) {
                        Some(pv) if *pv != *v => {
                            return Err(span.source.error(
                                span.line,
                                span.col,
                                format!(
                                    "value for key `{}` generated multiple times: `{}` and `{}`",
                                    serde_json::to_string_pretty(&k)?,
                                    serde_json::to_string_pretty(&pv)?,
                                    serde_json::to_string_pretty(&v)?,
                                )
                                .as_str(),
                            ));
                        }
                        _ => Rc::make_mut(map).insert(k.clone(), v.clone()),
                    };
                }
            }
            _ => bail!("could not merge value"),
        };
        Ok(())
    }

    pub fn get_path_string(refr: &Expr, document: Option<&str>) -> Result<String> {
        let mut comps = vec![];
        let mut expr = Some(refr);
        while expr.is_some() {
            match expr {
                Some(Expr::RefDot { refr, field, .. }) => {
                    comps.push(field.text());
                    expr = Some(refr);
                }
                Some(Expr::RefBrack { refr, index, .. })
                    if matches!(index.as_ref(), Expr::String(_)) =>
                {
                    if let Expr::String(s) = index.as_ref() {
                        comps.push(s.text());
                        expr = Some(refr);
                    }
                }
                Some(Expr::Var(v)) => {
                    comps.push(v.text());
                    expr = None;
                }
                _ => bail!("not a simple ref"),
            }
        }
        if let Some(d) = document {
            comps.push(d);
        };
        comps.reverse();
        Ok(comps.join("."))
    }

    fn set_current_module(
        &mut self,
        module: Option<&'source Module<'source>>,
    ) -> Result<Option<&'source Module<'source>>> {
        let m = self.module;
        if let Some(m) = module {
            self.current_module_path = Self::get_path_string(&m.package.refr, Some("data"))?;
        }
        self.module = module;
        Ok(m)
    }

    pub fn update_function_table(&mut self) -> Result<()> {
        for module in self.modules.clone() {
            let prev_module = self.set_current_module(Some(module))?;
            let module_path =
                Self::get_path_string(&self.current_module()?.package.refr, Some("data"))?;
            for rule in &module.policy {
                if let Rule::Spec {
                    head: RuleHead::Func { refr, .. },
                    ..
                } = rule
                {
                    let mut path =
                        Parser::get_path_ref_components(&self.current_module()?.package.refr)?;

                    Parser::get_path_ref_components_into(refr, &mut path)?;
                    let path: Vec<&str> = path.iter().map(|s| s.text()).collect();

                    if path.len() > 1 {
                        let value =
                            Self::make_or_get_value_mut(&mut self.data, &path[0..path.len() - 1])?;
                        if value == &Value::Undefined {
                            *value = Value::new_object();
                        }
                    }

                    let full_path = Self::get_path_string(refr, Some(module_path.as_str()))?;
                    self.functions.insert(full_path, rule);
                }
            }
            self.set_current_module(prev_module)?;
        }
        Ok(())
    }

    fn get_rule_refr(rule: &'source Rule<'source>) -> &'source Expr<'source> {
        match rule {
            Rule::Spec { head, .. } => match &head {
                RuleHead::Compr { refr, .. }
                | RuleHead::Set { refr, .. }
                | RuleHead::Func { refr, .. } => refr,
            },
            Rule::Default { refr, .. } => refr,
        }
    }

    fn eval_default_rule(&mut self, rule: &'source Rule<'source>) -> Result<()> {
        // Skip reprocessing rule.
        if self.processed.contains(rule) {
            return Ok(());
        }

        match rule {
            Rule::Default {
                span, refr, value, ..
            } => {
                let mut path = Parser::get_path_ref_components(&self.module.unwrap().package.refr)?;

                let (refr, index) = match refr {
                    Expr::RefBrack { refr, index, .. } => (refr.as_ref(), Some(index.as_ref())),
                    Expr::Var(_) => (refr, None),
                    _ => bail!("invalid token {:?} with the default keyword", refr),
                };

                Parser::get_path_ref_components_into(refr, &mut path)?;
                let paths: Vec<&str> = path.iter().map(|s| s.text()).collect();

                if matches!(
                    value,
                    Expr::Var(_) | Expr::RefBrack { .. } | Expr::RefDot { .. }
                ) {
                    bail!("illegal default rule (value contains a variable or reference)");
                }
                let value = self.eval_expr(value)?;

                // Assume at this point that all the non-default rules have been evaluated.
                // Merge the default value only if
                // 1. The corresponding variable does not have value yet
                // 2. The corresponding index in the object does not have value yet
                if let Some(index) = index {
                    let index = self.eval_expr(index)?;
                    let mut object = Value::new_object();
                    object.as_object_mut()?.insert(index.clone(), value);

                    let vref = Self::make_or_get_value_mut(&mut self.data, &paths)?;

                    if let Value::Object(btree) = &vref {
                        if !btree.contains_key(&index) {
                            Self::merge_value(span, vref, object)?;
                        }
                    } else if let Value::Undefined = vref {
                        Self::merge_value(span, vref, object)?;
                    }
                } else {
                    let vref = Self::make_or_get_value_mut(&mut self.data, &paths)?;
                    if let Value::Undefined = &vref {
                        Self::merge_value(span, vref, value)?;
                    }
                };

                self.processed.insert(rule);
            }
            _ => println!("not a default rule"),
        }

        Ok(())
    }

    fn eval_rule(
        &mut self,
        module: &'source Module<'source>,
        rule: &'source Rule<'source>,
    ) -> Result<()> {
        // Skip reprocessing rule
        if self.processed.contains(rule) {
            return Ok(());
        }

        // Skip default rules
        if let Rule::Default { .. } = rule {
            return Ok(());
        }

        self.active_rules.push(rule);
        if self.active_rules.iter().filter(|&r| r == &rule).count() == 2 {
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

        let prev_module = self.set_current_module(Some(module))?;
        match rule {
            Rule::Spec {
                span,
                head: rule_head,
                bodies: rule_body,
            } => {
                if matches!(rule_head, RuleHead::Func { .. }) {
                    return Ok(());
                }

                let (ctx, mut path) = self.make_rule_context(rule_head)?;
                let special_set = matches!((ctx.output_expr, &ctx.value), (None, Value::Set(_)));
                let value = match self.eval_rule_bodies(ctx, span, rule_body)? {
                    Value::Set(_) if special_set => {
                        let entry = path[path.len() - 1].text();
                        let mut s = BTreeSet::new();
                        s.insert(Value::String(entry.to_owned()));
                        path = path[0..path.len() - 1].to_vec();
                        Value::from_set(s)
                    }
                    v => v,
                };

                if value != Value::Undefined {
                    let paths: Vec<&str> = path.iter().map(|s| s.text()).collect();
                    let vref = Self::make_or_get_value_mut(&mut self.data, &paths[..])?;
                    Self::merge_value(span, vref, value)?;
                }
            }
            _ => bail!("internal error: unexpected"),
        }
        self.set_current_module(prev_module)?;
        self.processed.insert(rule);
        match self.active_rules.pop() {
            Some(r) if r == rule => Ok(()),
            _ => bail!("internal error: current rule not active"),
        }
    }

    pub fn eval(&mut self, data: &Option<Value>, input: &Option<Value>) -> Result<Value> {
        if let Some(input) = input {
            self.input = input.clone();

            info!("input: {:#?}", self.input);
        }
        if let Some(data) = data {
            self.data = data.clone();
        }

        self.update_function_table()?;
        self.gather_rules()?;

        for module in self.modules.clone() {
            for rule in &module.policy {
                self.eval_rule(module, rule)?;
            }
        }

        // Defer the evaluation of the default rules to here
        for module in self.modules.clone() {
            let prev_module = self.set_current_module(Some(module))?;
            for rule in &module.policy {
                self.eval_default_rule(rule)?;
            }
            self.set_current_module(prev_module)?;
        }

        Ok(self.data.clone())
    }

    pub fn eval_query_snippet(&mut self, snippet: &'source Expr<'source>) -> Result<Value> {
        // Create a new scope for evaluating the expression.
        self.scopes.push(Scope::new());
        let prev_module = self.set_current_module(self.modules.last().copied())?;
        let value = self.eval_expr(snippet)?;
        // Pop the scope.
        let scope = self.scopes.pop();
        let r = match snippet {
            Expr::AssignExpr { .. } => {
                if let Some(scope) = scope {
                    let mut r = Value::new_object();
                    let map = r.as_object_mut()?;
                    // Capture each binding.
                    for (name, v) in scope {
                        map.insert(Value::String(name), v.value);
                    }
                    Ok(r)
                } else {
                    bail!("internal error: expression scope not found");
                }
            }
            _ => Ok(value),
        };
        self.set_current_module(prev_module)?;
        r
    }

    fn gather_rules(&mut self) -> Result<()> {
        for module in self.modules.clone() {
            let prev_module = self.set_current_module(Some(module))?;
            for rule in &module.policy {
                let refr = Self::get_rule_refr(rule);
                if let Rule::Spec { .. } = rule {
                    // Adjust refr to ensure simple ref.
                    // TODO: refactor.
                    let refr = match refr {
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
                            o.into_mut().push(rule);
                        }
                        Entry::Vacant(v) => {
                            v.insert(vec![rule]);
                        }
                    }
                } else if let Rule::Default { .. } = rule {
                    let (refr, index) = match refr {
                        // TODO: Validate the index
                        Expr::RefBrack { refr, index, .. } => {
                            if !matches!(
                                index.as_ref(),
                                Expr::True(_) | Expr::False(_) | Expr::Number(_) | Expr::String(_)
                            ) {
                                // OPA's behavior is ignoring the non-scalar index
                                bail!("index is not a scalar value");
                            }

                            let index = self.eval_expr(index)?;

                            (refr.as_ref(), Some(index.to_string()))
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
                                        bail!("multiple default rules for the variable with the same index");
                                    }
                                } else {
                                    bail!("conflict type with the default rules");
                                }
                            }
                            o.into_mut().push((rule, index));
                        }
                        Entry::Vacant(v) => {
                            v.insert(vec![(rule, index)]);
                        }
                    }
                }
            }
            self.set_current_module(prev_module)?;
        }
        Ok(())
    }
}
