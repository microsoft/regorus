// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr::*;
use crate::ast::*;
use crate::interpreter::Interpreter;
use crate::lexer::Span;

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::string::String;

use anyhow::{bail, Result};

#[derive(Debug)]
pub struct Definition<'a> {
    // The variable being defined.
    // This can be an empty string to indicate that
    // no variable is being defined.
    pub var: &'a str,

    // Other variables in the same scope used to compute
    // the value of this variable.
    pub used_vars: Vec<&'a str>,
}

#[derive(Debug)]
pub struct StmtInfo<'a> {
    // A statement can define multiple variables.
    // A variable can also be defined by multiple statement.
    pub definitions: Vec<Definition<'a>>,
}

#[derive(Debug)]
pub enum SortResult {
    // The order in which statements must be executed.
    Order(Vec<u16>),
    // List of statements comprising a cycle for a given var.
    Cycle(String, Vec<usize>),
}

pub fn schedule<'a>(infos: &mut [StmtInfo<'a>]) -> Result<SortResult> {
    let num_statements = infos.len();

    // Mapping from each var to the list of statements that define it.
    let mut defining_stmts: BTreeMap<&'a str, Vec<usize>> = BTreeMap::new();

    // For each statement, interate through its definitions and add the
    // statement (index) to the var's defining-statements list.
    for (idx, info) in infos.iter().enumerate() {
        for defn in &info.definitions {
            defining_stmts.entry(defn.var).or_default().push(idx);
        }
    }

    // Order of execution for statements.
    let mut order = vec![];
    order.reserve(infos.len());

    // Keep track of whether a var has been defined or not.
    let mut defined_vars = BTreeSet::new();

    // Keep track of whether a statement has been scheduled or not.
    let mut scheduled = vec![false; infos.len()];

    // List of vars to be processed.
    let mut vars_to_process: Vec<&'a str> = defining_stmts.keys().cloned().collect();
    let mut tmp = vec![];

    let mut queue = VecDeque::new();
    let mut schedule_stmt = |stmt_idx: usize| {
        // Check if the statement has already been scheduled.
        if scheduled[stmt_idx] {
            return None;
        }

        let definitions = &infos[stmt_idx].definitions;

        let can_be_scheduled = if definitions.len() == 1 {
            // Handle the more common case of single definition statements optimally.
            // Check if all the vars used by the definition are previously assigned.
            definitions[0]
                .used_vars
                .iter()
                .all(|uv| defined_vars.contains(uv))
        } else {
            // Set of vars that can be defined in this statement.
            let mut defined_in_stmt = BTreeSet::new();

            // Add each definition to processing queue.
            queue.clear();
            for defn in definitions {
                queue.push_back(defn);
            }

            while !queue.is_empty() {
                let n = queue.len();
                for _ in 0..n {
                    let defn = queue.pop_front().unwrap();
                    // Check if the vars used by this definition are
                    //  1) defined via prior assignments (or)
                    //  2) defined in current statement
                    if defn
                        .used_vars
                        .iter()
                        .all(|uv| defined_vars.contains(uv) || defined_in_stmt.contains(uv))
                    {
                        defined_in_stmt.insert(defn.var);
                    } else {
                        // The definiton must be processed again.
                        queue.push_back(defn);
                    }
                }
                // If no definition became defined, then there is a cycle between
                // the definitions in this statement. The cycle cannot be broken yet.
                if n == queue.len() {
                    break;
                }
            }

            // If the vars used by all the definitions are already defined or
            // can be defined by scheduling this statement, return true.
            queue.is_empty()
        };

        // Schedule the var if possible.
        if can_be_scheduled {
            order.push(stmt_idx as u16);
            scheduled[stmt_idx] = true;

            // For each definition in the statement, mark its var as defined.
            for defn in &infos[stmt_idx].definitions {
                defined_vars.insert(defn.var);
            }
            Some(true)
        } else {
            Some(false)
        }
    };

    let mut process_var = |var| {
        let mut stmt_scheduled = false;
        let mut reprocess_var = false;
        // Loop through each statement that defines the var.
        for stmt_idx in defining_stmts.entry(var).or_default().iter().cloned() {
            match schedule_stmt(stmt_idx) {
                Some(true) => {
                    stmt_scheduled = true;
                }
                Some(false) => {
                    reprocess_var = true;
                }
                None => {
                    // Statement has already been scheduled.
                }
            }
        }

        (stmt_scheduled, reprocess_var)
    };

    let mut done = false;
    while !done {
        done = true;

        // Swap with temporary vec.
        std::mem::swap(&mut vars_to_process, &mut tmp);

        // Loop through each unscheduled var.
        for var in tmp.iter().cloned() {
            let (stmt_scheduled, reprocess_var) = process_var(var);

            if stmt_scheduled {
                done = false;

                // If a statement has been scheduled, it means that the
                // var has been defined. Process "" (statements that don't define any var)
                // to see if any statements that depend on var can be scheduled.
                // Doing so allows statements like `x > 10` to be scheduled immediately after x has been defined.
                // TODO: Also schedule statements like `y = x > 10` immediately.
                process_var("");
            }

            if reprocess_var {
                vars_to_process.push(var);
            }
        }
    }

    if order.len() != num_statements {
        bail!("could not schedule all statements {order:?} {num_statements}");
    }

    // TODO: determine cycles.
    Ok(SortResult::Order(order))
}

#[derive(Clone, Default, Debug)]
pub struct Scope<'a> {
    pub locals: BTreeSet<&'a str>,
    pub inputs: BTreeSet<&'a str>,
}

fn traverse<'a>(expr: &'a Expr<'a>, f: &mut dyn FnMut(&'a Expr<'a>) -> Result<bool>) -> Result<()> {
    if !f(expr)? {
        return Ok(());
    }
    match expr {
        String(_) | RawString(_) | Number(_) | True(_) | False(_) | Null(_) | Var(_) => (),

        Array { items, .. } | Set { items, .. } => {
            for i in items {
                traverse(i, f)?;
            }
        }
        Object { fields, .. } => {
            for (_, k, v) in fields {
                traverse(k, f)?;
                traverse(v, f)?;
            }
        }

        ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => (),

        Call { params, .. } => {
            // TODO: is traversing function needed?
            // traverse(fcn, f)?;
            for p in params {
                traverse(p, f)?;
            }
        }

        UnaryExpr { expr, .. } => traverse(expr, f)?,

        RefDot { refr, .. } => traverse(refr, f)?,

        RefBrack { refr, index, .. } => {
            traverse(refr, f)?;
            traverse(index, f)?;
        }

        BinExpr { lhs, rhs, .. }
        | BoolExpr { lhs, rhs, .. }
        | ArithExpr { lhs, rhs, .. }
        | AssignExpr { lhs, rhs, .. } => {
            traverse(lhs, f)?;
            traverse(rhs, f)?;
        }

        Membership {
            key,
            value,
            collection,
            ..
        } => {
            if let Some(key) = key.as_ref() {
                traverse(key, f)?;
            }
            traverse(value, f)?;
            traverse(collection, f)?;
        }
    }
    Ok(())
}

fn var_exists<'a>(name: &'a str, parent_scopes: &[Scope<'a>]) -> bool {
    parent_scopes.iter().rev().any(|s| s.locals.contains(name))
}

fn gather_assigned_vars<'a>(
    expr: &'a Expr<'a>,
    can_shadow: bool,
    parent_scopes: &[Scope<'a>],
    scope: &mut Scope<'a>,
) -> Result<()> {
    traverse(expr, &mut |e| match e {
        // Ignore _, input, data.
        Var(v) if matches!(v.text(), "_" | "input" | "data") => Ok(false),

        // Record local var that can shadow input var.
        Var(v) if can_shadow => {
            scope.locals.insert(v.text());
            Ok(false)
        }

        // Record input vars.
        Var(v) if var_exists(v.text(), parent_scopes) => {
            scope.inputs.insert(v.text());
            Ok(false)
        }

        // Record local var.
        Var(v) => {
            scope.locals.insert(v.text());
            Ok(false)
        }

        // TODO: key vs value for object binding
        Array { .. } | Object { .. } => Ok(true),
        _ => Ok(false),
    })
}

fn gather_input_vars<'a>(
    expr: &'a Expr<'a>,
    parent_scopes: &[Scope<'a>],
    scope: &mut Scope<'a>,
) -> Result<()> {
    traverse(expr, &mut |e| match e {
        Var(v) if var_exists(v.text(), parent_scopes) => {
            let var = v.text();
            if !scope.locals.contains(var) {
                scope.inputs.insert(var);
            }
            Ok(false)
        }
        _ => Ok(true),
    })
}

fn gather_loop_vars<'a>(
    expr: &'a Expr<'a>,
    parent_scopes: &[Scope<'a>],
    scope: &mut Scope<'a>,
) -> Result<()> {
    traverse(expr, &mut |e| match e {
        Var(v) if var_exists(v.text(), parent_scopes) => Ok(false),
        RefBrack { index, .. } => {
            if let Var(v) = index.as_ref() {
                if !matches!(v.text(), "_" | "input" | "data")
                    && !var_exists(v.text(), parent_scopes)
                {
                    // Treat this as an index var.
                    scope.locals.insert(v.text());
                }
            }
            Ok(true)
        }

        _ => Ok(true),
    })
}

// TODO: start opa discussion
//    k = "k"
//   t = {"k": 5}
// {k:y} = t
// Try inlining value of t
fn gather_vars<'a>(
    expr: &'a Expr<'a>,
    can_shadow: bool,
    parent_scopes: &[Scope<'a>],
    scope: &mut Scope<'a>,
) -> Result<()> {
    // Process assignment expressions to gather vars that are defined/assigned
    // in current scope.
    if let AssignExpr { op, lhs, rhs, .. } = expr {
        gather_assigned_vars(lhs, *op == AssignOp::ColEq, parent_scopes, scope)?;
        gather_assigned_vars(rhs, false, parent_scopes, scope)?;
    } else {
        gather_assigned_vars(expr, can_shadow, parent_scopes, scope)?;
    }

    // Process all expressions to gather loop index vars and inputs.
    // TODO: := assignment and use in same statement.
    gather_input_vars(expr, parent_scopes, scope)?;
    gather_loop_vars(expr, parent_scopes, scope)
}

fn get_rule_prefix<'a>(expr: &Expr<'a>) -> Result<&'a str> {
    match expr {
        Expr::Var(v) => Ok(v.text()),
        Expr::RefDot { refr, .. } => get_rule_prefix(refr),
        Expr::RefBrack { refr, .. } => get_rule_prefix(refr),
        _ => bail!("internal error: analyzer: could not get rule prefix"),
    }
}

pub struct Analyzer<'a> {
    packages: BTreeMap<String, Scope<'a>>,
    locals: BTreeMap<&'a Query<'a>, Scope<'a>>,
    scopes: Vec<Scope<'a>>,
    order: BTreeMap<&'a Query<'a>, Vec<u16>>,
}

pub struct Schedule<'a> {
    pub scopes: BTreeMap<&'a Query<'a>, Scope<'a>>,
    pub order: BTreeMap<&'a Query<'a>, Vec<u16>>,
}

impl<'a> Default for Analyzer<'a> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> Analyzer<'a> {
    pub fn new() -> Analyzer<'a> {
        Analyzer {
            packages: BTreeMap::new(),
            locals: BTreeMap::new(),
            scopes: vec![],
            order: BTreeMap::new(),
        }
    }

    pub fn analyze(mut self, modules: &'a [Module<'a>]) -> Result<Schedule> {
        for m in modules {
            let path = Interpreter::get_path_string(&m.package.refr, Some("data"))?;
            let scope: &mut Scope = self.packages.entry(path).or_default();
            for r in &m.policy {
                let var = match r {
                    Rule::Default { refr, .. }
                    | Rule::Spec {
                        head:
                            RuleHead::Compr { refr, .. }
                            | RuleHead::Set { refr, .. }
                            | RuleHead::Func { refr, .. },
                        ..
                    } => get_rule_prefix(refr)?,
                };
                scope.locals.insert(var);
            }
        }

        for m in modules {
            self.analyze_module(m)?;
        }

        Ok(Schedule {
            scopes: self.locals,
            order: self.order,
        })
    }

    fn analyze_module(&mut self, m: &'a Module<'a>) -> Result<()> {
        let path = Interpreter::get_path_string(&m.package.refr, Some("data"))?;
        let scope = match self.packages.get(&path) {
            Some(s) => s,
            _ => bail!("internal error: package scope missing"),
        };

        self.scopes.push(scope.clone());
        for r in &m.policy {
            self.analyze_rule(r)?;
        }
        self.scopes.pop();

        Ok(())
    }

    fn analyze_rule(&mut self, r: &'a Rule<'a>) -> Result<()> {
        match r {
            Rule::Spec { head, bodies, .. } => {
                let (key, value, scope) = self.analyze_rule_head(head)?;
                // Push arg scope if any.
                // Args are maintained in a separate scope so that they aren't used for
                // scheduling.
                self.scopes.push(scope);
                for b in bodies {
                    self.analyze_query(key, value, &b.query, Scope::default())?;
                }

                if bodies.is_empty() {
                    if let Some(value) = value {
                        self.analyze_value_expr(value)?;
                    }
                }

                self.scopes.pop();
                Ok(())
            }
            Rule::Default { value, .. } => self.analyze_value_expr(value),
        }
    }

    fn analyze_value_expr(&mut self, expr: &'a Expr<'a>) -> Result<()> {
        let mut comprs = vec![];
        traverse(expr, &mut |e| match e {
            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => {
                comprs.push(e);
                Ok(false)
            }
            _ => Ok(true),
        })?;
        for compr in comprs {
            match compr {
                Expr::ArrayCompr { query, term, .. } | Expr::SetCompr { query, term, .. } => {
                    self.analyze_query(None, Some(term), query, Scope::default())?;
                }
                Expr::ObjectCompr {
                    query, key, value, ..
                } => self.analyze_query(
                    Some(key.as_ref()),
                    Some(value.as_ref()),
                    query,
                    Scope::default(),
                )?,
                _ => (),
            }
        }
        Ok(())
    }

    fn analyze_rule_head(
        &mut self,
        head: &'a RuleHead<'a>,
    ) -> Result<(Option<&'a Expr<'a>>, Option<&'a Expr<'a>>, Scope<'a>)> {
        let mut scope = Scope::default();
        Ok(match head {
            RuleHead::Compr { assign, .. } => (None, assign.as_ref().map(|a| &a.value), scope),
            RuleHead::Set { key, .. } => (key.as_ref(), None, scope),
            RuleHead::Func { args, assign, .. } => {
                for a in args.iter() {
                    match a {
                        Var(v) => {
                            scope.locals.insert(v.text());
                        }
                        _ => unimplemented!("non var arguments"),
                    }
                }
                (None, assign.as_ref().map(|a| &a.value), scope)
            }
        })
    }

    fn gather_local_vars(
        &mut self,
        key: Option<&'a Expr<'a>>,
        value: Option<&'a Expr<'a>>,
        query: &'a Query<'a>,
        scope: &mut Scope<'a>,
    ) -> Result<()> {
        // First process assign, some expressions and gather local vars.
        for stmt in &query.stmts {
            match &stmt.literal {
                Literal::SomeVars { vars, .. } => vars.iter().for_each(|v| {
                    scope.locals.insert(v.text());
                }),
                Literal::SomeIn {
                    key,
                    value,
                    collection,
                    ..
                } => {
                    if let Some(key) = key {
                        gather_vars(key, true, &self.scopes, scope)?;
                    }
                    gather_vars(value, true, &self.scopes, scope)?;
                    gather_input_vars(collection, &self.scopes, scope)?;
                    gather_loop_vars(collection, &self.scopes, scope)?;
                }
                Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => {
                    if let AssignExpr { .. } = expr {
                        gather_vars(expr, false, &self.scopes, scope)?;
                    } else {
                        gather_input_vars(expr, &self.scopes, scope)?;
                        gather_loop_vars(expr, &self.scopes, scope)?;
                    }
                }
                Literal::Every { domain, .. } => {
                    // key, value defined in every stmt is visible only in its body.
                    gather_input_vars(domain, &self.scopes, scope)?;
                    gather_loop_vars(domain, &self.scopes, scope)?;
                }
            }
        }

        if let Some(key) = key {
            gather_vars(key, false, &self.scopes, scope)?;
        }
        if let Some(value) = value {
            gather_vars(value, false, &self.scopes, scope)?;
        }

        // Remove input vars that are shadowed.
        for v in &scope.locals {
            scope.inputs.remove(v);
        }

        Ok(())
    }

    fn gather_used_vars_comprs_index_vars(
        expr: &'a Expr<'a>,
        scope: &mut Scope<'a>,
        first_use: &mut BTreeMap<&'a str, Span<'a>>,
        definitions: &mut Vec<Definition<'a>>,
    ) -> Result<(Vec<&'a str>, Vec<&'a Expr<'a>>)> {
        let mut used_vars = vec![];
        let mut comprs = vec![];
        traverse(expr, &mut |e| match e {
            Var(v) if !matches!(v.text(), "_" | "input" | "data") => {
                let name = v.text();
                if scope.locals.contains(name)
                /*|| scope.inputs.contains(name) */
                {
                    used_vars.push(name);
                    first_use.entry(name).or_insert(v.clone());
                } else if !scope.inputs.contains(name) {
                    bail!(v.error(format!("Use of undefined variable `{name}` is unsafe").as_str()));
                }
                Ok(false)
            }

            RefBrack { refr, index, .. } => {
                if let Var(v) = index.as_ref() {
                    let var = v.text();
                    if scope.locals.contains(var) {
                        let (rb_used_vars, rb_comprs) = Self::gather_used_vars_comprs_index_vars(
                            refr,
                            scope,
                            first_use,
                            definitions,
                        )?;
                        definitions.push(Definition {
                            var,
                            used_vars: rb_used_vars.clone(),
                        });
                        used_vars.extend(rb_used_vars);
                        used_vars.push(var);
                        comprs.extend(rb_comprs);
                        return Ok(false);
                    }
                }
                Ok(true)
            }

            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => {
                comprs.push(e);
                Ok(false)
            }

            _ => Ok(true),
        })?;
        Ok((used_vars, comprs))
    }

    fn process_comprs(
        &mut self,
        comprs: &[&'a Expr<'a>],
        scope: &mut Scope<'a>,
        first_use: &mut BTreeMap<&'a str, Span<'a>>,
        used_vars: &mut Vec<&'a str>,
    ) -> Result<()> {
        self.scopes.push(scope.clone());

        for compr in comprs {
            let compr_scope = match compr {
                Expr::ArrayCompr { query, term, .. } | Expr::SetCompr { query, term, .. } => {
                    self.analyze_query(None, Some(term), query, Scope::default())?;
                    self.locals.get(query)
                }
                Expr::ObjectCompr {
                    query, key, value, ..
                } => {
                    self.analyze_query(
                        Some(key.as_ref()),
                        Some(value.as_ref()),
                        query,
                        Scope::default(),
                    )?;
                    self.locals.get(query)
                }
                _ => return Ok(()),
            };

            // Record vars used by the comprehension scope.
            if let Some(compr_scope) = compr_scope {
                for iv in &compr_scope.inputs {
                    if scope.locals.contains(iv) {
                        // Record possible first use of current scope's local var.
                        first_use.entry(iv).or_insert(compr.span().clone());
                        used_vars.push(iv);
                    } else {
                        // If the var is not a local var, then add it to the set of input vars.
                        scope.inputs.insert(iv);
                    }
                }
            }
        }

        self.scopes.pop();
        Ok(())
    }

    fn gather_assigned_vars(
        &self,
        expr: &'a Expr<'a>,
        scope: &Scope<'a>,
        check_first_use: bool,
        first_use: &BTreeMap<&'a str, Span<'a>>,
    ) -> Result<Vec<&'a str>> {
        let mut vars = vec![];
        traverse(expr, &mut |e| match e {
            Var(v) => {
                let var = v.text();
                if scope.locals.contains(var) {
                    if check_first_use {
                        Self::check_first_use(v, first_use)?;
                    }
                    vars.push(var);
                }
                Ok(false)
            }
            // TODO: key vs value for object binding
            Array { .. } | Object { .. } => Ok(true),
            _ => Ok(false),
        })?;
        Ok(vars)
    }

    fn process_assign_expr(
        &mut self,
        op: &AssignOp,
        lhs: &'a Expr<'a>,
        rhs: &'a Expr<'a>,
        scope: &mut Scope<'a>,
        first_use: &mut BTreeMap<&'a str, Span<'a>>,
        definitions: &mut Vec<Definition<'a>>,
    ) -> Result<()> {
        match (lhs, rhs) {
            (
                Array {
                    items: lhs_items, ..
                },
                Array {
                    items: rhs_items, ..
                },
            ) => {
                if lhs_items.len() != rhs_items.len() {
                    let span = rhs.span();
                    bail!(span.error("mismatch in number of array elements"));
                }

                for (idx, lhs_elem) in lhs_items.iter().enumerate() {
                    self.process_assign_expr(
                        op,
                        lhs_elem,
                        &rhs_items[idx],
                        scope,
                        first_use,
                        definitions,
                    )?;
                }
                return Ok(());
            }
            // TODO: object
            _ => {
                {
                    let (mut used_vars, comprs) = Self::gather_used_vars_comprs_index_vars(
                        rhs,
                        scope,
                        first_use,
                        definitions,
                    )?;
                    self.process_comprs(&comprs[..], scope, first_use, &mut used_vars)?;
                    let check_first_use = *op == AssignOp::ColEq;
                    for var in self.gather_assigned_vars(lhs, scope, check_first_use, first_use)? {
                        definitions.push(Definition {
                            var,
                            used_vars: used_vars.clone(),
                        });
                    }
                }
                {
                    let (mut used_vars, comprs) = Self::gather_used_vars_comprs_index_vars(
                        lhs,
                        scope,
                        first_use,
                        definitions,
                    )?;
                    let check_first_use = false;
                    self.process_comprs(&comprs[..], scope, first_use, &mut used_vars)?;
                    for var in self.gather_assigned_vars(rhs, scope, check_first_use, first_use)? {
                        definitions.push(Definition {
                            var,
                            used_vars: used_vars.clone(),
                        });
                    }
                }
            }
        }

        Ok(())
    }

    fn process_expr(
        &mut self,
        expr: &'a Expr<'a>,
        scope: &mut Scope<'a>,
        first_use: &mut BTreeMap<&'a str, Span<'a>>,
        definitions: &mut Vec<Definition<'a>>,
    ) -> Result<()> {
        match expr {
            AssignExpr { op, lhs, rhs, .. } => {
                self.process_assign_expr(op, lhs, rhs, scope, first_use, definitions)
            }
            _ => {
                let (mut used_vars, comprs) =
                    Self::gather_used_vars_comprs_index_vars(expr, scope, first_use, definitions)?;
                self.process_comprs(&comprs[..], scope, first_use, &mut used_vars)?;
                definitions.push(Definition { var: "", used_vars });
                Ok(())
            }
        }
    }

    fn check_first_use(var: &Span<'a>, first_use: &BTreeMap<&'a str, Span<'a>>) -> Result<()> {
        let name = var.text();
        if let Some(r#use) = first_use.get(name) {
            if r#use.line < var.line || (r#use.line == var.line && r#use.col < var.col) {
                bail!(r#use.error(
                    format!(
                        "var `{name}` used before definition below.{}",
                        var.message("definition", "")
                    )
                    .as_str()
                ));
            }
        }
        Ok(())
    }

    fn gather_some_vars(
        expr: &'a Expr<'a>,
        scope: &Scope<'a>,
        _first_use: &BTreeMap<&'a str, Span<'a>>,
        vars: &mut Vec<&'a str>,
        non_vars: &mut Vec<&'a Expr<'a>>,
    ) -> Result<()> {
        traverse(expr, &mut |e| match e {
            Var(v) if scope.locals.contains(v.text()) => {
                vars.push(v.text());
                Ok(false)
            }
            // TODO: Object key/value
            Array { .. } | Object { .. } => Ok(true),
            _ => {
                non_vars.push(e);
                Ok(false)
            }
        })
    }

    fn analyze_query(
        &mut self,
        key: Option<&'a Expr<'a>>,
        value: Option<&'a Expr<'a>>,
        query: &'a Query<'a>,
        mut scope: Scope<'a>,
    ) -> Result<()> {
        self.gather_local_vars(key, value, query, &mut scope)?;

        let mut infos = vec![];
        let mut first_use = BTreeMap::new();
        for stmt in &query.stmts {
            let mut definitions = vec![];
            match &stmt.literal {
                Literal::SomeVars { vars, .. } => {
                    for v in vars {
                        Self::check_first_use(v, &first_use)?;
                    }
                }
                Literal::SomeIn {
                    key,
                    value,
                    collection,
                    ..
                } => {
                    let mut some_vars = vec![];
                    let mut non_vars = vec![];

                    if let Some(key) = key {
                        Self::gather_some_vars(
                            key,
                            &scope,
                            &first_use,
                            &mut some_vars,
                            &mut non_vars,
                        )?;
                    }
                    Self::gather_some_vars(
                        value,
                        &scope,
                        &first_use,
                        &mut some_vars,
                        &mut non_vars,
                    )?;

                    let mut col_definitions = vec![];
                    let (mut col_used_vars, col_comprs) = Self::gather_used_vars_comprs_index_vars(
                        collection,
                        &mut scope,
                        &mut first_use,
                        &mut col_definitions, // TODO: handle these definitions
                    )?;
                    self.process_comprs(
                        &col_comprs[..],
                        &mut scope,
                        &mut first_use,
                        &mut col_used_vars,
                    )?;

                    // Add dependency between some-vars and vars used in collection.
                    for var in &some_vars {
                        definitions.push(Definition {
                            var,
                            used_vars: col_used_vars.clone(),
                        })
                    }

                    let mut used_vars = vec![];
                    for e in non_vars {
                        let mut definitions = vec![];
                        let (uv, comprs) = Self::gather_used_vars_comprs_index_vars(
                            e,
                            &mut scope,
                            &mut first_use,
                            &mut definitions,
                        )?;
                        if !definitions.is_empty() {
                            bail!("internal error: non empty definitions");
                        }
                        used_vars.extend(uv);
                        self.process_comprs(
                            &comprs[..],
                            &mut scope,
                            &mut first_use,
                            &mut used_vars,
                        )?;
                    }
                    definitions.push(Definition { var: "", used_vars });
                    // TODO: vars in compr
                }
                Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => {
                    self.process_expr(expr, &mut scope, &mut first_use, &mut definitions)?;
                }
                Literal::Every {
                    key,
                    value,
                    domain,
                    query,
                    ..
                } => {
                    // Create dependencies for vars used in domain.
                    let (mut uv, comprs) = Self::gather_used_vars_comprs_index_vars(
                        domain,
                        &mut scope,
                        &mut first_use,
                        &mut definitions,
                    )?;
                    self.process_comprs(&comprs[..], &mut scope, &mut first_use, &mut uv)?;
                    definitions.push(Definition {
                        var: "",
                        used_vars: uv,
                    });

                    self.scopes.push(scope.clone());
                    let mut e_scope = Scope::default();
                    if let Some(key) = key {
                        e_scope.locals.insert(key.text());
                    }
                    e_scope.locals.insert(value.text());
                    self.scopes.push(e_scope);

                    // TODO: mark first use of key, value so that they cannot be := assigned
                    // within query.
                    self.analyze_query(None, None, query, Scope::default())?;

                    // TODO: propagate used vars from query
                    self.scopes.pop();
                    self.scopes.pop();
                }
            }

            // If no definitions exist (e.g when only inputs are used), create a definition
            // binding the "" var so that these statements get scheduled first.
            if definitions.is_empty() {
                definitions.push(Definition {
                    var: "",
                    used_vars: vec![],
                });
            }
            infos.push(StmtInfo { definitions });
        }

        if let SortResult::Order(ord) = schedule(&mut infos[..])? {
            self.order.insert(query, ord);
        }

        self.locals.insert(query, scope);

        Ok(())
    }
}
