// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr::{Set, *};
use crate::ast::*;
use crate::lexer::*;
use crate::utils::*;
use crate::*;

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::string::String;
use core::cmp;
use core::fmt;

use anyhow::{bail, Result};

#[derive(Debug)]
pub struct Definition<Str: Clone + cmp::Ord> {
    // The variable being defined.
    // This can be an empty string to indicate that
    // no variable is being defined.
    pub var: Str,

    // Other variables in the same scope used to compute
    // the value of this variable.
    pub used_vars: Vec<Str>,
}

#[derive(Debug)]
pub struct StmtInfo<Str: Clone + cmp::Ord> {
    // A statement can define multiple variables.
    // A variable can also be defined by multiple statement.
    pub definitions: Vec<Definition<Str>>,
}

#[derive(Debug)]
pub enum SortResult {
    // The order in which statements must be executed.
    Order(Vec<u16>),
    // List of statements comprising a cycle for a given var.
    #[allow(unused)]
    Cycle(String, Vec<usize>),
}

pub fn schedule<Str: Clone + cmp::Ord + fmt::Debug>(
    infos: &mut [StmtInfo<Str>],
    empty: &Str,
) -> Result<SortResult> {
    let num_statements = infos.len();

    // Mapping from each var to the list of statements that define it.
    let mut defining_stmts: BTreeMap<Str, Vec<usize>> = BTreeMap::new();

    // For each statement, interate through its definitions and add the
    // statement (index) to the var's defining-statements list.
    for (idx, info) in infos.iter().enumerate() {
        for defn in &info.definitions {
            let varc = defn.var.clone();
            defining_stmts.entry(varc).or_default().push(idx);
        }
    }

    // Order of execution for statements.
    let mut order = Vec::with_capacity(infos.len());

    // Keep track of whether a var has been defined or not.
    let mut defined_vars = BTreeSet::new();

    // Keep track of whether a statement has been scheduled or not.
    let mut scheduled = vec![false; infos.len()];

    // List of vars to be processed.
    let mut vars_to_process: Vec<Str> = defining_stmts.keys().cloned().collect();
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
                        defined_in_stmt.insert(defn.var.clone());
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
                defined_vars.insert(defn.var.clone());
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

    process_var(empty.clone());

    let mut done = false;
    while !done {
        done = true;

        // Swap with temporary vec.
        core::mem::swap(&mut vars_to_process, &mut tmp);

        // Loop through each unscheduled var.
        for var in tmp.iter().cloned() {
            let (stmt_scheduled, reprocess_var) = process_var(var.clone());

            if stmt_scheduled {
                done = false;

                // If a statement has been scheduled, it means that the
                // var has been defined. Process "" (statements that don't define any var)
                // to see if any statements that depend on var can be scheduled.
                // Doing so allows statements like `x > 10` to be scheduled immediately after x has been defined.
                // TODO: Also schedule statements like `y = x > 10` immediately.
                process_var(empty.clone());
            }

            if reprocess_var {
                vars_to_process.push(var);
            }
        }
    }

    if order.len() != num_statements {
        #[cfg(feature = "std")]
        std::eprintln!("could not schedule all statements {order:?}");
        return Ok(SortResult::Order(
            (0..num_statements).map(|i| i as u16).collect(),
        ));
    }

    // TODO: determine cycles.
    Ok(SortResult::Order(order))
}

#[derive(Clone, Default, Debug)]
pub struct Scope {
    pub locals: BTreeMap<SourceStr, Span>,
    pub unscoped: BTreeSet<SourceStr>,
    pub inputs: BTreeSet<SourceStr>,
}

pub fn traverse(expr: &Ref<Expr>, f: &mut dyn FnMut(&Ref<Expr>) -> Result<bool>) -> Result<()> {
    if !f(expr)? {
        return Ok(());
    }
    match expr.as_ref() {
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

fn var_exists(var: &Span, parent_scopes: &[Scope]) -> bool {
    let name = var.source_str();

    for pscope in parent_scopes.iter().rev() {
        if pscope.unscoped.contains(&name) {
            return true;
        }
        // Check parent scope vars defined using :=.
        if let Some(s) = pscope.locals.get(&name) {
            // Note: Since a rule cannot span multiple files, it is safe to check only
            // the line numbers.
            if s.line <= var.line {
                // The variable was defined in parent scope prior to current comprehension.
                return true;
            }
        }
    }
    false
}

fn gather_assigned_vars(
    expr: &Ref<Expr>,
    can_shadow: bool,
    parent_scopes: &[Scope],
    scope: &mut Scope,
) -> Result<()> {
    traverse(expr, &mut |e| match e.as_ref() {
        // Ignore _, input, data.
        Var(v) if matches!(v.0.text(), "_" | "input" | "data") => Ok(false),

        // Record local var that can shadow input var.
        Var(v) if can_shadow => {
            scope.locals.insert(v.0.source_str(), v.0.clone());
            Ok(false)
        }

        // Record input vars.
        Var(v) if var_exists(&v.0, parent_scopes) => {
            scope.inputs.insert(v.0.source_str());
            Ok(false)
        }

        // Record local var.
        Var(v) => {
            scope.unscoped.insert(v.0.source_str());
            Ok(false)
        }

        // TODO: key vs value for object binding
        Array { .. } | Object { .. } => Ok(true),
        _ => Ok(false),
    })
}

fn gather_input_vars(expr: &Ref<Expr>, parent_scopes: &[Scope], scope: &mut Scope) -> Result<()> {
    traverse(expr, &mut |e| match e.as_ref() {
        Var(v)
            if !scope.unscoped.contains(&v.0.source_str()) && var_exists(&v.0, parent_scopes) =>
        {
            scope.inputs.insert(v.0.source_str());
            Ok(false)
        }
        _ => Ok(true),
    })
}

fn gather_loop_vars(expr: &Ref<Expr>, parent_scopes: &[Scope], scope: &mut Scope) -> Result<()> {
    traverse(expr, &mut |e| match e.as_ref() {
        RefBrack { index, .. } => {
            gather_assigned_vars(index, false, parent_scopes, scope)?;
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
fn gather_vars(
    expr: &Ref<Expr>,
    can_shadow: bool,
    parent_scopes: &[Scope],
    scope: &mut Scope,
) -> Result<()> {
    // Process assignment expressions to gather vars that are defined/assigned
    // in current scope.
    if let AssignExpr { op, lhs, rhs, .. } = expr.as_ref() {
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

pub struct Analyzer {
    packages: BTreeMap<String, Scope>,
    scope_table: BTreeMap<Ref<Query>, Scope>,
    scopes: Vec<Scope>,
    order: BTreeMap<Ref<Query>, Vec<u16>>,
    functions: FunctionTable,
    current_module_path: String,
}

#[derive(Debug, Clone)]
pub struct Schedule {
    pub scopes: BTreeMap<Ref<Query>, Scope>,
    pub order: BTreeMap<Ref<Query>, Vec<u16>>,
}

impl Default for Analyzer {
    fn default() -> Self {
        Self::new()
    }
}

impl Analyzer {
    pub fn new() -> Analyzer {
        Analyzer {
            packages: BTreeMap::new(),
            scope_table: BTreeMap::new(),
            scopes: vec![],
            order: BTreeMap::new(),
            functions: FunctionTable::new(),
            current_module_path: String::default(),
        }
    }

    pub fn analyze(mut self, modules: &[Ref<Module>]) -> Result<Schedule> {
        self.add_rules(modules)?;
        self.functions = gather_functions(modules)?;

        for m in modules {
            self.analyze_module(m)?;
        }

        Ok(Schedule {
            scopes: self.scope_table,
            order: self.order,
        })
    }

    pub fn analyze_query_snippet(
        mut self,
        modules: &[Ref<Module>],
        query: &Ref<Query>,
    ) -> Result<Schedule> {
        self.add_rules(modules)?;
        self.analyze_query(None, None, query, Scope::default())?;

        Ok(Schedule {
            scopes: self.scope_table,
            order: self.order,
        })
    }

    fn add_rules(&mut self, modules: &[Ref<Module>]) -> Result<()> {
        for m in modules {
            let path = get_path_string(&m.package.refr, Some("data"))?;
            let scope: &mut Scope = self.packages.entry(path).or_default();
            for r in &m.policy {
                let var = match r.as_ref() {
                    Rule::Default { refr, .. }
                    | Rule::Spec {
                        head:
                            RuleHead::Compr { refr, .. }
                            | RuleHead::Set { refr, .. }
                            | RuleHead::Func { refr, .. },
                        ..
                    } => get_root_var(refr)?,
                };
                scope.unscoped.insert(var);
            }
        }

        Ok(())
    }

    fn analyze_module(&mut self, m: &Module) -> Result<()> {
        let path = get_path_string(&m.package.refr, Some("data"))?;
        let scope = match self.packages.get(&path) {
            Some(s) => s,
            _ => bail!("internal error: package scope missing"),
        };
        self.current_module_path = path;
        self.scopes.push(scope.clone());
        for r in &m.policy {
            self.analyze_rule(r)?;
        }
        self.scopes.pop();

        Ok(())
    }

    fn analyze_rule(&mut self, r: &Ref<Rule>) -> Result<()> {
        match r.as_ref() {
            Rule::Spec { head, bodies, .. } => {
                let (key, value, scope) = self.analyze_rule_head(head)?;
                // Push arg scope if any.
                // Args are maintained in a separate scope so that they aren't used for
                // scheduling.
                self.scopes.push(scope);
                for b in bodies {
                    self.analyze_query(key.clone(), value.clone(), &b.query, Scope::default())?;
                }

                if bodies.is_empty() {
                    if let Some(value) = value {
                        self.analyze_value_expr(&value)?;
                    }
                }

                self.scopes.pop();
                Ok(())
            }
            Rule::Default { value, .. } => self.analyze_value_expr(value),
        }
    }

    fn analyze_value_expr(&mut self, expr: &Ref<Expr>) -> Result<()> {
        let mut comprs = vec![];
        traverse(expr, &mut |e| match e.as_ref() {
            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => {
                comprs.push(e.clone());
                Ok(false)
            }
            _ => Ok(true),
        })?;
        for compr in comprs {
            match compr.as_ref() {
                Expr::ArrayCompr { query, term, .. } | Expr::SetCompr { query, term, .. } => {
                    self.analyze_query(None, Some(term.clone()), query, Scope::default())?;
                }
                Expr::ObjectCompr {
                    query, key, value, ..
                } => self.analyze_query(
                    Some(key.clone()),
                    Some(value.clone()),
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
        head: &RuleHead,
    ) -> Result<(Option<ExprRef>, Option<ExprRef>, Scope)> {
        let mut scope = Scope::default();
        Ok(match head {
            RuleHead::Compr { assign, .. } => {
                (None, assign.as_ref().map(|a| a.value.clone()), scope)
            }
            RuleHead::Set { key, .. } => (key.clone(), None, scope),
            RuleHead::Func { args, assign, .. } => {
                for a in args.iter() {
                    traverse(a, &mut |e| {
                        if let Var(v) = e.as_ref() {
                            scope.unscoped.insert(v.0.source_str());
                        }
                        Ok(true)
                    })?;
                }
                (None, assign.as_ref().map(|a| a.value.clone()), scope)
            }
        })
    }

    fn gather_local_vars(
        &mut self,
        key: Option<Ref<Expr>>,
        value: Option<Ref<Expr>>,
        query: &Query,
        scope: &mut Scope,
    ) -> Result<()> {
        // First process assign, some expressions and gather local vars.
        for stmt in &query.stmts {
            for wm in &stmt.with_mods {
                gather_input_vars(&wm.r#as, &self.scopes, scope)?;
                gather_loop_vars(&wm.r#as, &self.scopes, scope)?;
            }
            match &stmt.literal {
                Literal::SomeVars { vars, .. } => vars.iter().for_each(|v| {
                    scope.locals.insert(v.source_str(), v.clone());
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
                    if let AssignExpr { .. } = expr.as_ref() {
                        gather_vars(expr, false, &self.scopes, scope)?;
                    } else {
                        gather_input_vars(expr, &self.scopes, scope)?;
                        gather_loop_vars(expr, &self.scopes, scope)?;

                        let extra_arg = get_extra_arg(
                            expr,
                            Some(self.current_module_path.as_str()),
                            &self.functions,
                        );
                        if let Some(ea) = extra_arg {
                            gather_vars(&ea, false, &self.scopes, scope)?;
                        }
                    }
                }
                Literal::Every { domain, .. } => {
                    // key, value defined in every stmt is visible only in its body.
                    gather_input_vars(domain, &self.scopes, scope)?;
                    gather_loop_vars(domain, &self.scopes, scope)?;
                }
            }
        }

        if let Some(key) = &key {
            gather_vars(key, false, &self.scopes, scope)?;
        }
        if let Some(value) = &value {
            gather_vars(value, false, &self.scopes, scope)?;
        }

        // Remove input vars that are shadowed.
        for v in scope.locals.keys() {
            scope.inputs.remove(v);
            scope.unscoped.remove(v);
        }

        Ok(())
    }

    fn gather_used_vars_comprs_index_vars(
        expr: &Ref<Expr>,
        scope: &mut Scope,
        first_use: &mut BTreeMap<SourceStr, Span>,
        definitions: &mut Vec<Definition<SourceStr>>,
        assigned_vars: &Option<&BTreeSet<SourceStr>>,
    ) -> Result<(Vec<SourceStr>, Vec<Ref<Expr>>)> {
        let mut used_vars = vec![];
        let mut comprs = vec![];
        #[cfg(feature = "deprecated")]
        let full_expr = expr;
        traverse(expr, &mut |e| match e.as_ref() {
            Var(v) if !matches!(v.0.text(), "_" | "input" | "data") => {
                let name = v.0.source_str();
                let is_extra_arg = match assigned_vars {
                    Some(vars) => vars.contains(&v.0.source_str()),
                    _ => false,
                };

                if scope.locals.contains_key(&name) || scope.unscoped.contains(&name)
                /*|| scope.inputs.contains(name) */
                {
                    if !is_extra_arg {
                        used_vars.push(name.clone());
                        first_use.entry(name).or_insert(v.0.clone());
                    }
                } else if !scope.inputs.contains(&name) {
                    #[cfg(feature = "deprecated")]
                    {
                        if let Ok(path) = get_path_string(full_expr, None) {
                            if crate::builtins::BUILTINS.contains_key(path.as_str())
                                || crate::builtins::deprecated::DEPRECATED
                                    .contains_key(path.as_str())
                            {
                                return Ok(false);
                            }
                        }
                    }
                    bail!(v
                        .0
                        .error(format!("use of undefined variable `{name}` is unsafe").as_str()));
                }
                Ok(false)
            }

            RefBrack { refr, index, .. } => {
                traverse(index, &mut |e| match e.as_ref() {
                    Var(v) => {
                        let var = v.0.source_str();
                        if scope.locals.contains_key(&var) || scope.unscoped.contains(&var) {
                            let (rb_used_vars, rb_comprs) =
                                Self::gather_used_vars_comprs_index_vars(
                                    refr,
                                    scope,
                                    first_use,
                                    definitions,
                                    assigned_vars,
                                )?;
                            definitions.push(Definition {
                                var: var.clone(),
                                used_vars: rb_used_vars.clone(),
                            });
                            used_vars.extend(rb_used_vars);
                            used_vars.push(var);
                            comprs.extend(rb_comprs);
                        }
                        Ok(false)
                    }
                    Array { .. } | Object { .. } => Ok(true),
                    _ => Ok(false),
                })?;
                Ok(true)
            }

            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => {
                comprs.push(e.clone());
                Ok(false)
            }

            _ => Ok(true),
        })?;
        Ok((used_vars, comprs))
    }

    fn process_comprs(
        &mut self,
        comprs: &[Ref<Expr>],
        scope: &mut Scope,
        first_use: &mut BTreeMap<SourceStr, Span>,
        used_vars: &mut Vec<SourceStr>,
    ) -> Result<()> {
        self.scopes.push(scope.clone());

        for compr in comprs {
            let compr_scope = match compr.as_ref() {
                Expr::ArrayCompr { query, term, .. } | Expr::SetCompr { query, term, .. } => {
                    self.analyze_query(None, Some(term.clone()), query, Scope::default())?;
                    self.scope_table.get(query)
                }
                Expr::ObjectCompr {
                    query, key, value, ..
                } => {
                    self.analyze_query(
                        Some(key.clone()),
                        Some(value.clone()),
                        query,
                        Scope::default(),
                    )?;
                    self.scope_table.get(query)
                }
                _ => break,
            };

            // Record vars used by the comprehension scope.
            if let Some(compr_scope) = compr_scope {
                for iv in &compr_scope.inputs {
                    if scope.locals.contains_key(iv) || scope.unscoped.contains(iv) {
                        // Record possible first use of current scope's local var.
                        first_use.entry(iv.clone()).or_insert(compr.span().clone());
                        used_vars.push(iv.clone());
                    } else {
                        // If the var is not a local var, then add it to the set of input vars.
                        scope.inputs.insert(iv.clone());
                    }
                }
            }
        }

        self.scopes.pop();
        Ok(())
    }

    fn gather_assigned_vars(
        &self,
        expr: &Ref<Expr>,
        scope: &Scope,
        check_first_use: bool,
        first_use: &BTreeMap<SourceStr, Span>,
    ) -> Result<Vec<SourceStr>> {
        let mut vars = vec![];
        traverse(expr, &mut |e| match e.as_ref() {
            Var(v) => {
                let var = v.0.source_str();
                if scope.locals.contains_key(&var) {
                    if check_first_use {
                        Self::check_first_use(&v.0, first_use)?;
                    }
                    vars.push(var);
                } else if scope.unscoped.contains(&var) {
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

    #[allow(clippy::too_many_arguments)]
    fn process_assign_expr(
        &mut self,
        op: &AssignOp,
        lhs: &Ref<Expr>,
        rhs: &Ref<Expr>,
        scope: &mut Scope,
        first_use: &mut BTreeMap<SourceStr, Span>,
        definitions: &mut Vec<Definition<SourceStr>>,
        mut with_mods_used_vars: Vec<SourceStr>,
        mut with_mods_comprs: Vec<Ref<Expr>>,
    ) -> Result<()> {
        let empty_str = lhs.span().source_str().clone_empty();
        match (lhs.as_ref(), rhs.as_ref()) {
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
                        with_mods_used_vars.clone(),
                        with_mods_comprs.clone(),
                    )?;
                }
                return Ok(());
            }
            // TODO: object
            _ => {
                {
                    let (mut used_vars, mut comprs) = Self::gather_used_vars_comprs_index_vars(
                        rhs,
                        scope,
                        first_use,
                        definitions,
                        &None,
                    )?;
                    used_vars.append(&mut with_mods_used_vars.clone());
                    comprs.append(&mut with_mods_comprs.clone());
                    self.process_comprs(&comprs[..], scope, first_use, &mut used_vars)?;
                    let check_first_use = *op == AssignOp::ColEq;
                    let assigned_vars =
                        self.gather_assigned_vars(lhs, scope, check_first_use, first_use)?;

                    for var in &assigned_vars {
                        let used_vars = used_vars.iter().filter(|v| v != &var).cloned().collect();
                        definitions.push(Definition {
                            var: var.clone(),
                            used_vars,
                        });
                    }
                    if assigned_vars.is_empty() {
                        definitions.push(Definition {
                            var: empty_str.clone(),
                            used_vars: used_vars.clone(),
                        });
                    }
                }
                {
                    let (mut used_vars, mut comprs) = Self::gather_used_vars_comprs_index_vars(
                        lhs,
                        scope,
                        first_use,
                        definitions,
                        &None,
                    )?;
                    used_vars.append(&mut with_mods_used_vars);
                    comprs.append(&mut with_mods_comprs);
                    let check_first_use = false;
                    self.process_comprs(&comprs[..], scope, first_use, &mut used_vars)?;
                    let assigned_vars =
                        self.gather_assigned_vars(rhs, scope, check_first_use, first_use)?;
                    for var in &assigned_vars {
                        let used_vars = used_vars.iter().filter(|v| v != &var).cloned().collect();
                        definitions.push(Definition {
                            var: var.clone(),
                            used_vars,
                        });
                    }
                    if assigned_vars.is_empty() {
                        definitions.push(Definition {
                            var: empty_str.clone(),
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
        expr: &Ref<Expr>,
        scope: &mut Scope,
        first_use: &mut BTreeMap<SourceStr, Span>,
        definitions: &mut Vec<Definition<SourceStr>>,
        mut with_mods_used_vars: Vec<SourceStr>,
        mut with_mods_comprs: Vec<Ref<Expr>>,
    ) -> Result<()> {
        match expr.as_ref() {
            AssignExpr { op, lhs, rhs, .. } => self.process_assign_expr(
                op,
                lhs,
                rhs,
                scope,
                first_use,
                definitions,
                with_mods_used_vars,
                with_mods_comprs,
            ),
            _ => {
                let (mut used_vars, mut comprs) = Self::gather_used_vars_comprs_index_vars(
                    expr,
                    scope,
                    first_use,
                    definitions,
                    &None,
                )?;
                comprs.append(&mut with_mods_comprs);
                used_vars.append(&mut with_mods_used_vars);
                self.process_comprs(&comprs[..], scope, first_use, &mut used_vars)?;

                definitions.push(Definition {
                    var: expr.span().source_str().clone_empty(),
                    used_vars,
                });
                Ok(())
            }
        }
    }

    fn check_first_use(var: &Span, first_use: &BTreeMap<SourceStr, Span>) -> Result<()> {
        let name = var.source_str();
        if let Some(r#use) = first_use.get(&name) {
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
        expr: &Ref<Expr>,
        scope: &Scope,
        _first_use: &BTreeMap<SourceStr, Span>,
        vars: &mut Vec<SourceStr>,
        non_vars: &mut Vec<Ref<Expr>>,
    ) -> Result<()> {
        traverse(expr, &mut |e| match e.as_ref() {
            Var(v) if scope.locals.contains_key(&v.0.source_str()) => {
                vars.push(v.0.source_str());
                Ok(false)
            }
            // TODO: Object key/value
            Array { .. } | Object { .. } => Ok(true),
            _ => {
                non_vars.push(e.clone());
                Ok(false)
            }
        })
    }

    fn analyze_query(
        &mut self,
        key: Option<Ref<Expr>>,
        value: Option<Ref<Expr>>,
        query: &Ref<Query>,
        mut scope: Scope,
    ) -> Result<()> {
        let empty_str = query.span.source_str().clone_empty();
        self.gather_local_vars(key, value, query, &mut scope)?;

        let mut infos = vec![];
        let mut first_use = BTreeMap::new();
        for stmt in &query.stmts {
            let mut definitions = vec![];
            let mut with_mods_used_vars = vec![];
            let mut with_mods_comprs = vec![];
            for wm in &stmt.with_mods {
                let (mut used_vars, mut comprs) = Self::gather_used_vars_comprs_index_vars(
                    &wm.r#as,
                    &mut scope,
                    &mut first_use,
                    &mut definitions,
                    &None,
                )?;

                with_mods_used_vars.append(&mut used_vars);
                with_mods_comprs.append(&mut comprs);
            }
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
                    let (mut col_used_vars, mut col_comprs) =
                        Self::gather_used_vars_comprs_index_vars(
                            collection,
                            &mut scope,
                            &mut first_use,
                            &mut col_definitions,
                            &None,
                        )?;
                    col_used_vars.append(&mut with_mods_used_vars);
                    col_comprs.append(&mut with_mods_comprs.clone());
                    definitions.append(&mut col_definitions);

                    self.process_comprs(
                        &col_comprs[..],
                        &mut scope,
                        &mut first_use,
                        &mut col_used_vars,
                    )?;

                    // Add dependency between some-vars and vars used in collection.
                    for var in &some_vars {
                        definitions.push(Definition {
                            var: var.clone(),
                            used_vars: col_used_vars.clone(),
                        })
                    }

                    let mut used_vars = vec![];
                    for e in non_vars {
                        let mut definitions = vec![];
                        let (mut uv, mut comprs) = Self::gather_used_vars_comprs_index_vars(
                            &e,
                            &mut scope,
                            &mut first_use,
                            &mut definitions,
                            &None,
                        )?;

                        uv.append(&mut with_mods_used_vars.clone());
                        comprs.append(&mut with_mods_comprs.clone());
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
                    definitions.push(Definition {
                        var: empty_str.clone(),
                        used_vars,
                    });
                    // TODO: vars in compr
                }
                Literal::Expr { expr, .. } => {
                    let extra_arg = get_extra_arg(
                        expr,
                        Some(self.current_module_path.as_str()),
                        &self.functions,
                    );
                    if let Some(ref ea) = extra_arg {
                        // Gather vars that are being bound
                        let mut extras_scope = Scope::default();
                        gather_assigned_vars(ea, false, &self.scopes, &mut extras_scope)?;

                        for var in &extras_scope.unscoped {
                            scope.unscoped.insert(var.clone());
                        }

                        // Gather vars being used.
                        let (mut used_vars, mut comprs) = Self::gather_used_vars_comprs_index_vars(
                            expr,
                            &mut scope,
                            &mut first_use,
                            &mut definitions,
                            &Some(&extras_scope.unscoped),
                        )?;
                        used_vars.append(&mut with_mods_used_vars);
                        comprs.append(&mut with_mods_comprs);

                        self.process_comprs(
                            &comprs[..],
                            &mut scope,
                            &mut first_use,
                            &mut used_vars,
                        )?;

                        if !extras_scope.unscoped.is_empty() {
                            for var in extras_scope.unscoped {
                                definitions.push(Definition {
                                    var,
                                    used_vars: used_vars.clone(),
                                });
                            }
                        } else {
                            definitions.push(Definition {
                                var: empty_str.clone(),
                                used_vars,
                            });
                        }
                    } else {
                        self.process_expr(
                            expr,
                            &mut scope,
                            &mut first_use,
                            &mut definitions,
                            with_mods_used_vars,
                            with_mods_comprs,
                        )?;
                    }
                }
                Literal::NotExpr { expr, .. } => {
                    self.process_expr(
                        expr,
                        &mut scope,
                        &mut first_use,
                        &mut definitions,
                        with_mods_used_vars,
                        with_mods_comprs,
                    )?;
                }
                Literal::Every {
                    key,
                    value,
                    domain,
                    query,
                    ..
                } => {
                    // Create dependencies for vars used in domain.
                    let (mut uv, mut comprs) = Self::gather_used_vars_comprs_index_vars(
                        domain,
                        &mut scope,
                        &mut first_use,
                        &mut definitions,
                        &None,
                    )?;
                    uv.append(&mut with_mods_used_vars);
                    comprs.append(&mut with_mods_comprs);
                    self.process_comprs(&comprs[..], &mut scope, &mut first_use, &mut uv)?;
                    definitions.push(Definition {
                        var: empty_str.clone(),
                        used_vars: uv,
                    });

                    self.scopes.push(scope.clone());
                    let mut e_scope = Scope::default();
                    if let Some(key) = key {
                        e_scope.locals.insert(key.source_str(), key.clone());
                    }
                    e_scope.locals.insert(value.source_str(), value.clone());
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
                    var: empty_str.clone(),
                    used_vars: vec![],
                });
            }
            infos.push(StmtInfo { definitions });
        }

        let res = schedule(&mut infos[..], &query.span.source_str().clone_empty());
        match res {
            Ok(SortResult::Order(ord)) => {
                self.order.insert(query.clone(), ord);
            }
            Err(err) => {
                bail!(query.span.error(&err.to_string()))
            }
            _ => (),
        }
        self.scope_table.insert(query.clone(), scope);

        Ok(())
    }
}
