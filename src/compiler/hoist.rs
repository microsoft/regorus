// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

//! Loop hoisting functionality for compilation.
//!
//! This module contains code adapted from the RVM compiler to support
//! pre-computing loop hoisting information that can be stored in the
//! compiled policy and reused by the interpreter.

use super::destructuring_planner::{
    map_binding_error, BindingPlan, ScopingMode, VariableBindingContext,
};
use crate::ast::{Expr, ExprRef, Literal, LiteralStmt, Module, Query, Ref, Rule, RuleHead};
use crate::compiler::context::{ContextType, ScopeContext};
use crate::lookup::Lookup;
use crate::lookup::LookupResult;
use crate::scheduler::compute_module_globals;
use crate::*;
use anyhow::{anyhow, Result};

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

/// Implementation of VariableBindingContext for ScopeContext
impl VariableBindingContext for ScopeContext {
    fn is_var_unbound(&self, var_name: &str, scoping: ScopingMode) -> bool {
        if var_name == "_" {
            return false;
        }

        if self.unbound_vars.contains(var_name) {
            return true;
        }

        if self.has_scheduler_scope && self.local_vars.contains(var_name) {
            return true;
        }

        match scoping {
            ScopingMode::AllowShadowing => {
                // Allow shadowing - always consider variables as potentially unbound
                true
            }
            ScopingMode::RespectParent => {
                // Respect parent scope bindings
                if self
                    .module_globals
                    .as_ref()
                    .is_some_and(|globals| globals.contains(var_name))
                {
                    return false;
                }

                if self.bound_vars.contains(var_name) {
                    return false;
                }
                true
            }
        }
    }

    fn has_same_scope_binding(&self, var_name: &str) -> bool {
        if var_name == "_" {
            return false;
        }

        self.current_scope_bound_vars.contains(var_name)
    }
}

/// Type of loop that was hoisted
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoopType {
    /// `array[_]` or `object[idx]` patterns
    IndexIteration,
    Walk,
}

/// Information about a hoisted loop
#[derive(Debug, Clone)]
pub struct HoistedLoop {
    /// The loop expression itself (e.g., `array[_]`)
    pub loop_expr: Option<ExprRef>,

    /// Key/index variable (e.g., `_` or `idx`)
    pub key: Option<ExprRef>,

    /// Value expression (the result of indexing)
    pub value: ExprRef,

    /// Collection being iterated
    pub collection: ExprRef,

    /// Type of loop
    #[allow(dead_code)]
    pub loop_type: LoopType,
}

/// Lookup table mapping statements/expressions to their hoisted loops
#[derive(Debug, Clone, Default)]
pub struct HoistedLoopsLookup {
    /// Maps (module_index, statement_index) -> Vec<HoistedLoop>
    /// Stores pre-computed loops for each statement in rules/queries
    statement_loops: Lookup<Vec<HoistedLoop>>,

    /// Maps (module_index, expr_index) -> Vec<HoistedLoop>  
    /// For output expressions in comprehensions and rule values
    expr_loops: Lookup<Vec<HoistedLoop>>,

    /// Maps (module_index, expr_index) -> BindingPlan
    /// Stores pre-computed binding plans for assignment-style expressions
    expr_binding_plans: Lookup<BindingPlan>,

    /// Maps (module_index, query_index) -> ScopeContext
    /// Stores compilation contexts for queries (rules, comprehensions, every)
    query_contexts: Lookup<ScopeContext>,
}

impl HoistedLoopsLookup {
    /// Create a new empty lookup table
    pub fn new() -> Self {
        Self::default()
    }

    /// Ensure capacity for a given module and statement
    pub fn ensure_statement_capacity(&mut self, module_idx: u32, stmt_idx: u32) {
        self.statement_loops.ensure_capacity(module_idx, stmt_idx);
        self.expr_loops.ensure_capacity(module_idx, 0);
        self.expr_binding_plans.ensure_capacity(module_idx, 0);
        self.query_contexts.ensure_capacity(module_idx, 0);
    }

    /// Ensure capacity for a given module and expression
    pub fn ensure_expr_capacity(&mut self, module_idx: u32, expr_idx: u32) {
        self.expr_loops.ensure_capacity(module_idx, expr_idx);
        self.statement_loops.ensure_capacity(module_idx, 0);
        self.expr_binding_plans
            .ensure_capacity(module_idx, expr_idx);
        self.query_contexts.ensure_capacity(module_idx, 0);
    }

    /// Ensure capacity for a given module and query
    pub fn ensure_query_capacity(&mut self, module_idx: u32, query_idx: u32) {
        self.query_contexts.ensure_capacity(module_idx, query_idx);
        self.statement_loops.ensure_capacity(module_idx, 0);
        self.expr_loops.ensure_capacity(module_idx, 0);
        self.expr_binding_plans.ensure_capacity(module_idx, 0);
    }

    /// Store hoisted loops for a statement
    pub fn set_statement_loops(
        &mut self,
        module_idx: u32,
        stmt_idx: u32,
        loops: Vec<HoistedLoop>,
    ) -> Result<()> {
        self.statement_loops
            .set_checked(module_idx, stmt_idx, loops)
            .map_err(|err| anyhow!("statement_loops out of bounds: {err}"))
    }

    /// Get hoisted loops for a statement
    pub fn get_statement_loops(
        &self,
        module_idx: u32,
        stmt_idx: u32,
    ) -> LookupResult<Option<&Vec<HoistedLoop>>> {
        self.statement_loops.get_checked(module_idx, stmt_idx)
    }

    /// Store hoisted loops for an expression (output expressions)
    pub fn set_expr_loops(
        &mut self,
        module_idx: u32,
        expr_idx: u32,
        loops: Vec<HoistedLoop>,
    ) -> Result<()> {
        self.expr_loops
            .set_checked(module_idx, expr_idx, loops)
            .map_err(|err| anyhow!("expr_loops out of bounds: {err}"))
    }

    /// Get hoisted loops for an expression
    pub fn get_expr_loops(
        &self,
        module_idx: u32,
        expr_idx: u32,
    ) -> LookupResult<Option<&Vec<HoistedLoop>>> {
        self.expr_loops.get_checked(module_idx, expr_idx)
    }

    /// Store the compilation context for a query
    pub fn set_query_context(
        &mut self,
        module_idx: u32,
        query_idx: u32,
        context: ScopeContext,
    ) -> Result<()> {
        self.query_contexts
            .set_checked(module_idx, query_idx, context)
            .map_err(|err| anyhow!("query_contexts out of bounds: {err}"))
    }

    /// Store a binding plan for an expression
    pub fn set_expr_binding_plan(
        &mut self,
        module_idx: u32,
        expr_idx: u32,
        plan: BindingPlan,
    ) -> Result<()> {
        self.expr_binding_plans
            .set_checked(module_idx, expr_idx, plan)
            .map_err(|err| anyhow!("expr_binding_plans out of bounds: {err}"))
    }

    /// Get the compilation context for a query
    #[allow(dead_code)]
    pub fn get_query_context(
        &self,
        module_idx: u32,
        query_idx: u32,
    ) -> LookupResult<Option<&ScopeContext>> {
        self.query_contexts.get_checked(module_idx, query_idx)
    }

    /// Get the binding plan for an expression
    pub fn get_expr_binding_plan(
        &self,
        module_idx: u32,
        expr_idx: u32,
    ) -> LookupResult<Option<&BindingPlan>> {
        self.expr_binding_plans.get_checked(module_idx, expr_idx)
    }

    /// Merge another loop hoisting table into this one
    /// This is used to add query module loops to the existing table
    pub fn merge_query_loops(&mut self, mut other: HoistedLoopsLookup, module_idx: usize) {
        while self.statement_loops.module_len() < module_idx {
            self.statement_loops.push_module(Vec::new());
        }

        while self.expr_loops.module_len() < module_idx {
            self.expr_loops.push_module(Vec::new());
        }

        while self.expr_binding_plans.module_len() < module_idx {
            self.expr_binding_plans.push_module(Vec::new());
        }

        while self.query_contexts.module_len() < module_idx {
            self.query_contexts.push_module(Vec::new());
        }

        let query_module_idx = other.statement_loops.module_len().saturating_sub(1);

        if let Some(module) = other.statement_loops.remove_module(query_module_idx) {
            self.statement_loops.push_module(module);
        }

        if let Some(module) = other.expr_loops.remove_module(query_module_idx) {
            self.expr_loops.push_module(module);
        }

        if let Some(module) = other.expr_binding_plans.remove_module(query_module_idx) {
            self.expr_binding_plans.push_module(module);
        }

        if let Some(module) = other.query_contexts.remove_module(query_module_idx) {
            self.query_contexts.push_module(module);
        }
    }

    pub fn truncate_modules(&mut self, module_count: usize) {
        self.statement_loops.truncate_modules(module_count);
        self.expr_loops.truncate_modules(module_count);
        self.expr_binding_plans.truncate_modules(module_count);
        self.query_contexts.truncate_modules(module_count);
    }

    #[cfg(debug_assertions)]
    pub const fn module_len(&self) -> usize {
        self.statement_loops.module_len()
    }
}

// Note: ScopeContext is now defined in src/compiler/context.rs

/// Loop hoister that populates the HoistedLoopsLookup table
pub struct LoopHoister {
    lookup: HoistedLoopsLookup,
    schedule: Option<crate::Rc<crate::scheduler::Schedule>>,
    module_globals: Lookup<crate::Rc<BTreeSet<String>>>,
}

impl LoopHoister {
    /// Create a new loop hoister
    pub fn new() -> Self {
        Self {
            lookup: HoistedLoopsLookup::new(),
            schedule: None,
            module_globals: Lookup::new(),
        }
    }

    /// Create a new loop hoister with a schedule
    pub fn new_with_schedule(schedule: crate::Rc<crate::scheduler::Schedule>) -> Self {
        Self {
            lookup: HoistedLoopsLookup::new(),
            schedule: Some(schedule),
            module_globals: Lookup::new(),
        }
    }

    /// Populate loop hoisting information for all modules
    /// Returns the populated lookup table
    pub fn populate(mut self, modules: &[Ref<Module>]) -> Result<HoistedLoopsLookup> {
        self.module_globals = compute_module_globals(modules).map_err(|err| anyhow!(err))?;
        for (module_idx, module) in modules.iter().enumerate() {
            self.populate_module(module_idx as u32, module)?;
        }
        Ok(self.lookup)
    }

    fn create_scope_context(&self, module_idx: u32) -> Result<ScopeContext> {
        let mut context = ScopeContext::new();

        if let Some(globals) = self
            .module_globals
            .get_checked(module_idx, 0)
            .map_err(|err| anyhow!("module_globals out of bounds: {err}"))?
        {
            context.module_globals = Some(globals.clone());
        }

        Ok(context)
    }

    /// Populate loop hoisting information for all modules, with extra capacity
    /// for additional modules that will be added later (e.g., query modules)
    ///
    /// # Arguments
    /// * `modules` - The modules to populate
    /// * `extra_capacity` - Number of additional module slots to reserve
    pub fn populate_with_extra_capacity(
        mut self,
        modules: &[Ref<Module>],
        extra_capacity: u32,
    ) -> Result<HoistedLoopsLookup> {
        self.module_globals = compute_module_globals(modules).map_err(|err| anyhow!(err))?;
        for (module_idx, module) in modules.iter().enumerate() {
            self.populate_module(module_idx as u32, module)?;
        }
        // Ensure capacity for extra modules by ensuring capacity for a dummy statement
        // in each extra module (this will resize the module vector)
        let last_module_idx = modules.len() as u32;
        for i in 0..extra_capacity {
            self.lookup
                .ensure_statement_capacity(last_module_idx + i, 0);
            self.lookup.ensure_expr_capacity(last_module_idx + i, 0);
            self.module_globals.ensure_capacity(last_module_idx + i, 0);
            self.module_globals
                .set_checked(last_module_idx + i, 0, crate::Rc::new(BTreeSet::new()))
                .map_err(|err| anyhow!("module_globals out of bounds: {err}"))?;
        }
        Ok(self.lookup)
    }

    /// Populate loop information for a single module
    pub fn populate_module(&mut self, module_idx: u32, module: &Module) -> Result<()> {
        // Process all rules in the module
        for rule in &module.policy {
            self.populate_rule(module_idx, rule)?;
        }
        Ok(())
    }

    /// Finalize and return the populated lookup table
    pub fn finalize(self) -> HoistedLoopsLookup {
        self.lookup
    }

    /// Populate loop hoisting information for a query snippet
    /// Query snippets are treated like they're in a module appended at the end
    /// This matches how the analyzer handles query snippets
    ///
    /// # Arguments
    /// * `module_idx` - The module index to use (typically modules.len())
    /// * `query` - The query to populate
    /// * `num_statements` - Total number of statements in the query module
    /// * `num_expressions` - Total number of expressions in the query module
    pub fn populate_query_snippet(
        &mut self,
        module_idx: u32,
        query: &Query,
        num_statements: u32,
        num_expressions: u32,
    ) -> Result<()> {
        // Ensure capacity for all possible statement and expression indices
        // Indices are 0-based, so max index is count - 1
        if num_statements > 0 {
            self.lookup
                .ensure_statement_capacity(module_idx, num_statements - 1);
        }
        if num_expressions > 0 {
            self.lookup
                .ensure_expr_capacity(module_idx, num_expressions - 1);
        }

        self.module_globals.ensure_capacity(module_idx, 0);
        let mut reserved_globals = BTreeSet::new();
        reserved_globals.insert("data".to_string());
        reserved_globals.insert("input".to_string());
        self.module_globals
            .set_checked(module_idx, 0, crate::Rc::new(reserved_globals))
            .map_err(|err| anyhow!("module_globals out of bounds: {err}"))?;

        // Populate the query with default context
        let context = self.create_scope_context(module_idx)?;
        self.lookup.ensure_query_capacity(module_idx, query.qidx);
        self.populate_query(module_idx, query, &context)?;
        Ok(())
    }

    /// Populate loop information for a single rule
    fn populate_rule(&mut self, module_idx: u32, rule: &Rule) -> Result<()> {
        match rule {
            Rule::Spec { head, bodies, .. } => {
                // Create a context for this rule
                let mut context = self.create_scope_context(module_idx)?;

                // Bind function parameters if this is a function rule
                if let RuleHead::Func { args, .. } = head {
                    for param in args {
                        // Create binding plan for function parameter
                        match super::destructuring_planner::create_parameter_binding_plan(
                            param,
                            &context,
                            ScopingMode::AllowShadowing,
                        ) {
                            Ok(binding_plan) => {
                                let expr_idx = param.as_ref().eidx();
                                self.lookup.ensure_expr_capacity(module_idx, expr_idx);

                                // Immediately bind variables from the plan to context
                                Self::bind_vars_from_plan_to_context(&binding_plan, &mut context);

                                self.lookup.set_expr_binding_plan(
                                    module_idx,
                                    expr_idx,
                                    binding_plan,
                                )?;
                            }
                            Err(err) => return Err(map_binding_error(err)),
                        }

                        // Extract variable name from parameter expression
                        if let Expr::Var { span, .. } = param.as_ref() {
                            context.bind_variable(span.text());
                        }
                    }
                }

                // Extract key and value expressions from the rule head (matching RVM compiler pattern)
                let (key_expr, value_expr) = match head {
                    RuleHead::Compr { refr, assign, .. } => {
                        let output_expr = assign.as_ref().map(|a| a.value.clone());
                        let key_expr = match refr.as_ref() {
                            Expr::RefBrack { index, .. } => {
                                // For RefBrack (e.g., p[key]), the index is the key expression
                                Some(index.clone())
                            }
                            _ => {
                                // For non-RefBrack (e.g., p), no key expression
                                None
                            }
                        };
                        (key_expr, output_expr)
                    }
                    RuleHead::Set { key, .. } => {
                        // For set rules, no separate key_expr, output_expr is the key
                        (None, key.clone())
                    }
                    RuleHead::Func { assign, .. } => {
                        // Function rules return the assignment value (if any)
                        (None, assign.as_ref().map(|a| a.value.clone()))
                    }
                };

                // Process each rule body (definitions)
                for body in bodies {
                    // Create a context with the output expressions (using Rule context type)
                    let mut body_context = context.child_with_output_exprs(
                        ContextType::Rule,
                        key_expr.clone(),
                        value_expr.clone(),
                    );
                    body_context.current_scope_bound_vars =
                        context.current_scope_bound_vars.clone();

                    // Store the context for this query
                    let populated_body_context =
                        self.populate_query(module_idx, &body.query, &body_context)?;
                    self.lookup
                        .ensure_query_capacity(module_idx, body.query.qidx);
                    self.lookup.set_query_context(
                        module_idx,
                        body.query.qidx,
                        populated_body_context.clone(),
                    )?;

                    // Process the key expression if present
                    if let Some(ref key) = key_expr {
                        self.populate_output_expr(module_idx, key, &populated_body_context)?;
                    }

                    // Process the head value expression (if present)
                    if let Some(ref head_value) = value_expr {
                        self.populate_output_expr(module_idx, head_value, &populated_body_context)?;
                    }

                    // Process the value expression if present in the assign
                    if let Some(ref assign) = body.assign {
                        self.populate_output_expr(
                            module_idx,
                            &assign.value,
                            &populated_body_context,
                        )?;
                    }
                }

                // Handle rules with head assignments but no bodies (e.g., `y := "string"`)
                if bodies.is_empty() {
                    let mut body_context = context.child_with_output_exprs(
                        ContextType::Rule,
                        key_expr.clone(),
                        value_expr.clone(),
                    );
                    body_context.current_scope_bound_vars =
                        context.current_scope_bound_vars.clone();

                    if let Some(ref key) = key_expr {
                        self.populate_output_expr(module_idx, key, &body_context)?;
                    }

                    if let Some(ref value) = value_expr {
                        self.populate_output_expr(module_idx, value, &body_context)?;
                    }
                }
            }
            Rule::Default { value, .. } => {
                // For default rules, just process the value expression
                let context = self.create_scope_context(module_idx)?;
                self.populate_output_expr(module_idx, value, &context)?;
            }
        }

        Ok(())
    }

    /// Populate loop information for a query (sequence of statements)
    fn populate_query(
        &mut self,
        module_idx: u32,
        query: &Query,
        parent_context: &ScopeContext,
    ) -> Result<ScopeContext> {
        self.lookup.ensure_query_capacity(module_idx, query.qidx);
        let mut context = parent_context.clone();
        context.current_scope_bound_vars = parent_context.current_scope_bound_vars.clone();

        // Get the scheduled order if available
        let stmt_order: Vec<usize> = if let Some(ref schedule) = self.schedule {
            schedule
                .queries
                .get_checked(module_idx, query.qidx)
                .map_err(|err| anyhow!("schedule out of bounds: {err}"))?
                .map_or_else(
                    || (0..query.stmts.len()).collect(),
                    |query_schedule| {
                        query_schedule
                            .order
                            .iter()
                            .map(|&idx| idx as usize)
                            .collect()
                    },
                )
        } else {
            // No schedule available, use source order
            (0..query.stmts.len()).collect()
        };

        // Process statements in scheduled order
        for &stmt_idx in &stmt_order {
            let stmt = &query.stmts[stmt_idx];
            self.populate_statement(module_idx, stmt.sidx, stmt, &mut context)?;
        }

        Ok(context)
    }

    /// Populate loop information for a single statement
    fn populate_statement(
        &mut self,
        module_idx: u32,
        stmt_idx: u32,
        stmt: &LiteralStmt,
        context: &mut ScopeContext,
    ) -> Result<()> {
        // Handle SomeVars to mark variables as unbound
        if let Literal::SomeVars { vars, .. } = &stmt.literal {
            for var in vars {
                context.add_unbound_variable(var.text());
            }
        }

        let mut loops = Vec::new();
        self.analyze_literal(module_idx, &stmt.literal, context, &mut loops)?;

        for with_mod in &stmt.with_mods {
            self.analyze_expr(module_idx, &with_mod.refr, context, &mut loops)?;
            self.analyze_expr(module_idx, &with_mod.r#as, context, &mut loops)?;
        }

        self.lookup.ensure_statement_capacity(module_idx, stmt_idx);
        self.lookup
            .set_statement_loops(module_idx, stmt_idx, loops)?;

        Ok(())
    }

    fn analyze_literal(
        &mut self,
        module_idx: u32,
        literal: &Literal,
        context: &mut ScopeContext,
        loops: &mut Vec<HoistedLoop>,
    ) -> Result<()> {
        use Literal::*;

        match literal {
            SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                let binding_plan = super::destructuring_planner::create_some_in_binding_plan(
                    key, value, collection, context,
                )
                .map_err(map_binding_error)?;

                let expr_idx = collection.as_ref().eidx();
                self.lookup.ensure_expr_capacity(module_idx, expr_idx);
                Self::bind_vars_from_plan_to_context(&binding_plan, context);
                self.lookup
                    .set_expr_binding_plan(module_idx, expr_idx, binding_plan)?;

                if let Some(key_expr) = key {
                    self.analyze_expr(module_idx, key_expr, context, loops)?;
                }
                self.analyze_expr(module_idx, value, context, loops)?;
                self.analyze_expr(module_idx, collection, context, loops)?;
            }
            Expr { expr, .. } => {
                self.analyze_expr(module_idx, expr, context, loops)?;
            }
            Every { domain, query, .. } => {
                self.analyze_expr(module_idx, domain, context, loops)?;

                let every_context = context.child_with_output_exprs(ContextType::Every, None, None);
                let populated_context =
                    self.populate_query(module_idx, query.as_ref(), &every_context)?;
                self.lookup.ensure_query_capacity(module_idx, query.qidx);
                self.lookup
                    .set_query_context(module_idx, query.qidx, populated_context)?;
            }
            NotExpr { expr, .. } => {
                self.analyze_expr(module_idx, expr, context, loops)?;
            }
            _ => {}
        }

        Ok(())
    }

    fn analyze_expr(
        &mut self,
        module_idx: u32,
        expr: &ExprRef,
        context: &mut ScopeContext,
        loops: &mut Vec<HoistedLoop>,
    ) -> Result<()> {
        use crate::ast::Expr as E;

        match expr.as_ref() {
            E::String { .. }
            | E::RawString { .. }
            | E::Number { .. }
            | E::Bool { .. }
            | E::Null { .. }
            | E::Var { .. } => {}
            E::Array { items, .. } | E::Set { items, .. } => {
                for item in items {
                    self.analyze_expr(module_idx, item, context, loops)?;
                }
            }
            E::Object { fields, .. } => {
                for (_, key_expr, value_expr) in fields {
                    self.analyze_expr(module_idx, key_expr, context, loops)?;
                    self.analyze_expr(module_idx, value_expr, context, loops)?;
                }
            }
            E::ArrayCompr { term, query, .. } | E::SetCompr { term, query, .. } => {
                let compr_context = context.child_with_output_exprs(
                    ContextType::Comprehension,
                    None,
                    Some(term.clone()),
                );
                let populated_context =
                    self.populate_query(module_idx, query.as_ref(), &compr_context)?;
                self.lookup.ensure_query_capacity(module_idx, query.qidx);
                self.lookup
                    .set_query_context(module_idx, query.qidx, populated_context.clone())?;
                self.populate_output_expr_with_context(module_idx, term, &populated_context)?;
            }
            E::ObjectCompr {
                key, value, query, ..
            } => {
                let compr_context = context.child_with_output_exprs(
                    ContextType::Comprehension,
                    Some(key.clone()),
                    Some(value.clone()),
                );
                let populated_context =
                    self.populate_query(module_idx, query.as_ref(), &compr_context)?;
                self.lookup.ensure_query_capacity(module_idx, query.qidx);
                self.lookup
                    .set_query_context(module_idx, query.qidx, populated_context.clone())?;
                self.populate_output_expr_with_context(module_idx, key, &populated_context)?;
                self.populate_output_expr_with_context(module_idx, value, &populated_context)?;
            }
            E::Call { fcn, params, .. } => {
                self.analyze_expr(module_idx, fcn, context, loops)?;
                for param in params {
                    self.analyze_expr(module_idx, param, context, loops)?;
                }

                let is_walk = if let E::Var {
                    value: Value::String(name),
                    ..
                } = fcn.as_ref()
                {
                    name.as_ref() == "walk"
                } else {
                    false
                };

                if is_walk {
                    loops.push(HoistedLoop {
                        loop_expr: Some(expr.clone()),
                        key: None,
                        value: expr.clone(),
                        collection: expr.clone(),
                        loop_type: LoopType::Walk,
                    });
                }
                // If the last parameter expression contains unbound vars, create a binding plan
                if let Some(last_param) = params.last() {
                    match super::destructuring_planner::create_parameter_binding_plan(
                        last_param,
                        context,
                        ScopingMode::RespectParent,
                    ) {
                        Ok(binding_plan) => {
                            let expr_idx = last_param.as_ref().eidx();
                            self.lookup.ensure_expr_capacity(module_idx, expr_idx);

                            // Immediately bind variables from the plan to context
                            Self::bind_vars_from_plan_to_context(&binding_plan, context);

                            self.lookup.set_expr_binding_plan(
                                module_idx,
                                expr_idx,
                                binding_plan,
                            )?;
                        }
                        Err(err) => return Err(map_binding_error(err)),
                    }
                }
            }
            E::UnaryExpr { expr, .. } => {
                self.analyze_expr(module_idx, expr, context, loops)?;
            }
            E::RefDot { refr, .. } => {
                self.analyze_expr(module_idx, refr, context, loops)?;
            }
            E::RefBrack { refr, index, .. } => {
                self.analyze_expr(module_idx, refr, context, loops)?;
                self.analyze_expr(module_idx, index, context, loops)?;

                if Self::expr_contains_unbound_vars(index, context) {
                    match super::destructuring_planner::create_loop_index_binding_plan(
                        index, context,
                    ) {
                        Ok(binding_plan) => {
                            let expr_idx = index.as_ref().eidx();
                            self.lookup.ensure_expr_capacity(module_idx, expr_idx);
                            Self::bind_vars_from_plan_to_context(&binding_plan, context);
                            self.lookup.set_expr_binding_plan(
                                module_idx,
                                expr_idx,
                                binding_plan,
                            )?;
                        }
                        Err(err) => return Err(map_binding_error(err)),
                    }

                    loops.push(HoistedLoop {
                        loop_expr: Some(expr.clone()),
                        key: Some(index.clone()),
                        value: expr.clone(),
                        collection: refr.clone(),
                        loop_type: LoopType::IndexIteration,
                    });
                }
            }
            E::BinExpr { lhs, rhs, .. }
            | E::BoolExpr { lhs, rhs, .. }
            | E::ArithExpr { lhs, rhs, .. } => {
                self.analyze_expr(module_idx, lhs, context, loops)?;
                self.analyze_expr(module_idx, rhs, context, loops)?;
            }
            E::AssignExpr { op, lhs, rhs, .. } => {
                let binding_plan = super::destructuring_planner::create_assignment_binding_plan(
                    op.clone(),
                    lhs,
                    rhs,
                    context,
                )
                .map_err(map_binding_error)?;

                let expr_idx = expr.as_ref().eidx();
                self.lookup.ensure_expr_capacity(module_idx, expr_idx);
                Self::bind_vars_from_plan_to_context(&binding_plan, context);
                self.lookup
                    .set_expr_binding_plan(module_idx, expr_idx, binding_plan)?;

                self.analyze_expr(module_idx, lhs, context, loops)?;
                self.analyze_expr(module_idx, rhs, context, loops)?;
            }
            E::Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key_expr) = key {
                    self.analyze_expr(module_idx, key_expr, context, loops)?;
                }
                self.analyze_expr(module_idx, value, context, loops)?;
                self.analyze_expr(module_idx, collection, context, loops)?;
            }
            #[cfg(feature = "rego-extensions")]
            E::OrExpr { lhs, rhs, .. } => {
                self.analyze_expr(module_idx, lhs, context, loops)?;
                self.analyze_expr(module_idx, rhs, context, loops)?;
            }
        }

        Ok(())
    }

    /// Bind variables from a binding plan into the context
    fn bind_vars_from_plan_to_context(binding_plan: &BindingPlan, context: &mut ScopeContext) {
        let bound_vars = binding_plan.bound_vars();
        for var in bound_vars {
            context.bind_variable(&var);
        }
    }

    /// Check if an expression contains any unbound variables that should trigger loop hoisting
    fn expr_contains_unbound_vars(expr: &ExprRef, context: &ScopeContext) -> bool {
        use crate::ast::Expr as E;
        match expr.as_ref() {
            E::Var {
                value: Value::String(var_name),
                ..
            } => context.should_hoist_as_loop(var_name.as_ref()),
            E::Array { items, .. } | E::Set { items, .. } => items
                .iter()
                .any(|item| Self::expr_contains_unbound_vars(item, context)),
            E::Object { fields, .. } => fields.iter().any(|(_, _, value_expr)| {
                // For objects check only the value expression can be bound
                Self::expr_contains_unbound_vars(value_expr, context)
            }),
            // Other expressions don't contribute unbound vars from parent scope
            _ => false,
        }
    }

    /// Populate loop information for output expressions (rule values, comprehension terms)
    fn populate_output_expr(
        &mut self,
        module_idx: u32,
        expr: &ExprRef,
        context: &ScopeContext,
    ) -> Result<()> {
        self.populate_output_expr_with_context(module_idx, expr, context)
    }

    fn populate_output_expr_with_context(
        &mut self,
        module_idx: u32,
        expr: &ExprRef,
        context: &ScopeContext,
    ) -> Result<()> {
        let mut loops = Vec::new();
        let mut expr_context = context.clone();
        self.analyze_expr(module_idx, expr, &mut expr_context, &mut loops)?;

        let expr_idx = expr.as_ref().eidx();
        self.lookup.ensure_expr_capacity(module_idx, expr_idx);
        self.lookup.set_expr_loops(module_idx, expr_idx, loops)?;

        Ok(())
    }
}

impl Default for LoopHoister {
    fn default() -> Self {
        Self::new()
    }
}
