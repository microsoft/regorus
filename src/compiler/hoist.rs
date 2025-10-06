// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Loop hoisting functionality for compilation.
//!
//! This module contains code adapted from the RVM compiler to support
//! pre-computing loop hoisting information that can be stored in the
//! compiled policy and reused by the interpreter.

use crate::ast::{Expr, ExprRef, Literal, LiteralStmt, Module, Query, Ref, Rule, RuleHead};
use crate::compiler::context::{ContextType, ScopeContext};
use crate::lookup::Lookup;
use crate::*;
use anyhow::Result;

use alloc::vec::Vec;

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
        self.query_contexts.ensure_capacity(module_idx, 0);
    }

    /// Ensure capacity for a given module and expression
    pub fn ensure_expr_capacity(&mut self, module_idx: u32, expr_idx: u32) {
        self.expr_loops.ensure_capacity(module_idx, expr_idx);
        self.statement_loops.ensure_capacity(module_idx, 0);
        self.query_contexts.ensure_capacity(module_idx, 0);
    }

    /// Ensure capacity for a given module and query
    pub fn ensure_query_capacity(&mut self, module_idx: u32, query_idx: u32) {
        self.query_contexts.ensure_capacity(module_idx, query_idx);
        self.statement_loops.ensure_capacity(module_idx, 0);
        self.expr_loops.ensure_capacity(module_idx, 0);
    }

    /// Store hoisted loops for a statement
    pub fn set_statement_loops(&mut self, module_idx: u32, stmt_idx: u32, loops: Vec<HoistedLoop>) {
        self.statement_loops.set(module_idx, stmt_idx, loops);
    }

    /// Get hoisted loops for a statement
    pub fn get_statement_loops(&self, module_idx: u32, stmt_idx: u32) -> Option<&Vec<HoistedLoop>> {
        self.statement_loops.get_checked(module_idx, stmt_idx)
    }

    /// Store hoisted loops for an expression (output expressions)
    pub fn set_expr_loops(&mut self, module_idx: u32, expr_idx: u32, loops: Vec<HoistedLoop>) {
        self.expr_loops.set(module_idx, expr_idx, loops);
    }

    /// Get hoisted loops for an expression
    pub fn get_expr_loops(&self, module_idx: u32, expr_idx: u32) -> Option<&Vec<HoistedLoop>> {
        self.expr_loops.get_checked(module_idx, expr_idx)
    }

    /// Store the compilation context for a query
    pub fn set_query_context(&mut self, module_idx: u32, query_idx: u32, context: ScopeContext) {
        self.query_contexts.set(module_idx, query_idx, context);
    }

    /// Get the compilation context for a query
    pub fn get_query_context(&self, module_idx: u32, query_idx: u32) -> Option<&ScopeContext> {
        self.query_contexts.get_checked(module_idx, query_idx)
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

        if let Some(module) = other.query_contexts.remove_module(query_module_idx) {
            self.query_contexts.push_module(module);
        }
    }

    pub fn truncate_modules(&mut self, module_count: usize) {
        self.statement_loops.truncate_modules(module_count);
        self.expr_loops.truncate_modules(module_count);
        self.query_contexts.truncate_modules(module_count);
    }

    pub fn module_len(&self) -> usize {
        self.statement_loops.module_len()
    }
}

// Note: ScopeContext is now defined in src/compiler/context.rs

/// Loop hoister that populates the HoistedLoopsLookup table
pub struct LoopHoister {
    lookup: HoistedLoopsLookup,
    schedule: Option<crate::Rc<crate::scheduler::Schedule>>,
}

impl LoopHoister {
    /// Create a new loop hoister
    pub fn new() -> Self {
        Self {
            lookup: HoistedLoopsLookup::new(),
            schedule: None,
        }
    }

    /// Create a new loop hoister with a schedule
    pub fn new_with_schedule(schedule: crate::Rc<crate::scheduler::Schedule>) -> Self {
        Self {
            lookup: HoistedLoopsLookup::new(),
            schedule: Some(schedule),
        }
    }

    /// Populate loop hoisting information for all modules
    /// Returns the populated lookup table
    pub fn populate(mut self, modules: &[Ref<Module>]) -> Result<HoistedLoopsLookup> {
        for (module_idx, module) in modules.iter().enumerate() {
            self.populate_module(module_idx as u32, module)?;
        }
        Ok(self.lookup)
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

        // Populate the query with default context
        let context = ScopeContext::new();
        self.lookup.ensure_query_capacity(module_idx, query.qidx);
        self.populate_query(module_idx, query, &context).map(|_| ())
    }

    /// Populate loop information for a single rule
    fn populate_rule(&mut self, module_idx: u32, rule: &Rule) -> Result<()> {
        match rule {
            Rule::Spec { head, bodies, .. } => {
                // Create a context for this rule
                let mut context = ScopeContext::new();

                // Bind function parameters if this is a function rule
                if let RuleHead::Func { args, .. } = head {
                    for param in args {
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
                    let body_context = context.child_with_output_exprs(
                        ContextType::Rule,
                        key_expr.clone(),
                        value_expr.clone(),
                    );

                    // Store the context for this query
                    let populated_body_context =
                        self.populate_query(module_idx, &body.query, &body_context)?;
                    self.lookup
                        .ensure_query_capacity(module_idx, body.query.qidx);
                    self.lookup.set_query_context(
                        module_idx,
                        body.query.qidx,
                        populated_body_context.clone(),
                    );

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
                    let body_context = context.child_with_output_exprs(
                        ContextType::Rule,
                        key_expr.clone(),
                        value_expr.clone(),
                    );

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
                let context = ScopeContext::new();
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
        let mut context = parent_context.child();

        // Get the scheduled order if available
        let stmt_order: Vec<usize> = if let Some(ref schedule) = self.schedule {
            if let Some(query_schedule) = schedule.queries.get(module_idx, query.qidx) {
                query_schedule
                    .order
                    .iter()
                    .map(|&idx| idx as usize)
                    .collect()
            } else {
                // No schedule for this query, use source order
                (0..query.stmts.len()).collect()
            }
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

        // Traverse literal expressions to populate nested contexts (comprehensions, every, etc.)
        self.process_literal_for_contexts(module_idx, &stmt.literal, context)?;
        for with_mod in &stmt.with_mods {
            self.process_expr_for_contexts(module_idx, &with_mod.refr, context)?;
            self.process_expr_for_contexts(module_idx, &with_mod.r#as, context)?;
        }

        // Hoist loops from this statement using populated contexts
        let loops =
            self.hoist_loops_from_literal_with_context(module_idx, &stmt.literal, context)?;

        // Always store in lookup table, even if no loops (store empty vec)
        // This ensures the interpreter can always find an entry
        self.lookup.ensure_statement_capacity(module_idx, stmt_idx);
        self.lookup.set_statement_loops(module_idx, stmt_idx, loops);

        // Update context based on variable bindings in this statement
        self.update_context_from_literal(&stmt.literal, context);

        Ok(())
    }

    /// Hoist loops from a literal with variable binding context
    fn hoist_loops_from_literal_with_context(
        &self,
        module_idx: u32,
        literal: &Literal,
        context: &ScopeContext,
    ) -> Result<Vec<HoistedLoop>> {
        let mut loops = Vec::new();

        use Literal::*;
        match literal {
            SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                // Recursively hoist from sub-expressions first
                if let Some(key) = key {
                    self.hoist_loops_from_expr_with_context(module_idx, key, &mut loops, context)?;
                }
                self.hoist_loops_from_expr_with_context(module_idx, value, &mut loops, context)?;
                self.hoist_loops_from_expr_with_context(
                    module_idx, collection, &mut loops, context,
                )?;
            }
            Expr { expr, .. } => {
                // Hoist loops from expressions (like array[_] patterns)
                self.hoist_loops_from_expr_with_context(module_idx, expr, &mut loops, context)?;
            }
            Every { domain, query, .. } => {
                // Hoist from domain expression
                self.hoist_loops_from_expr_with_context(module_idx, domain, &mut loops, context)?;

                // Process the Every query in a child context
                let child_context = self
                    .lookup
                    .get_query_context(module_idx, query.qidx)
                    .cloned()
                    .unwrap_or_else(|| context.child());
                for stmt in &query.stmts {
                    self.hoist_loops_from_literal_with_context(
                        module_idx,
                        &stmt.literal,
                        &child_context,
                    )?;
                }
            }
            NotExpr { expr, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, expr, &mut loops, context)?;
            }
            _ => {
                // Other literal types don't have loops to hoist
            }
        }

        Ok(loops)
    }

    /// Traverse literals to populate nested contexts (comprehensions, every, etc.)
    fn process_literal_for_contexts(
        &mut self,
        module_idx: u32,
        literal: &Literal,
        context: &ScopeContext,
    ) -> Result<()> {
        use Literal::*;

        match literal {
            SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key_expr) = key {
                    self.process_expr_for_contexts(module_idx, key_expr, context)?;
                }
                self.process_expr_for_contexts(module_idx, value, context)?;
                self.process_expr_for_contexts(module_idx, collection, context)?;
            }
            Expr { expr, .. } | NotExpr { expr, .. } => {
                self.process_expr_for_contexts(module_idx, expr, context)?;
            }
            Every { domain, query, .. } => {
                // Process the domain expression for nested contexts
                self.process_expr_for_contexts(module_idx, domain, context)?;

                // Create a child context for the Every quantifier
                let every_context = context.child_with_output_exprs(ContextType::Every, None, None);
                let populated_every_context =
                    self.populate_query(module_idx, query.as_ref(), &every_context)?;
                self.lookup.ensure_query_capacity(module_idx, query.qidx);
                self.lookup.set_query_context(
                    module_idx,
                    query.qidx,
                    populated_every_context.clone(),
                );

                // Nested query already processed for hoisting via populated context
            }
            _ => {}
        }

        Ok(())
    }

    /// Traverse expressions to populate nested contexts (comprehensions, function params, etc.)
    fn process_expr_for_contexts(
        &mut self,
        module_idx: u32,
        expr: &ExprRef,
        context: &ScopeContext,
    ) -> Result<()> {
        use crate::ast::Expr as E;

        match expr.as_ref() {
            E::Array { items, .. } | E::Set { items, .. } => {
                for item in items {
                    self.process_expr_for_contexts(module_idx, item, context)?;
                }
            }
            E::Object { fields, .. } => {
                for (_, key_expr, value_expr) in fields {
                    self.process_expr_for_contexts(module_idx, key_expr, context)?;
                    self.process_expr_for_contexts(module_idx, value_expr, context)?;
                }
            }
            E::ArrayCompr { term, query, .. } | E::SetCompr { term, query, .. } => {
                let compr_context = context.child_with_output_exprs(
                    ContextType::Comprehension,
                    None,
                    Some(term.clone()),
                );

                let populated_compr_context =
                    self.populate_query(module_idx, query.as_ref(), &compr_context)?;
                self.lookup.ensure_query_capacity(module_idx, query.qidx);
                self.lookup.set_query_context(
                    module_idx,
                    query.qidx,
                    populated_compr_context.clone(),
                );

                self.populate_output_expr(module_idx, term, &populated_compr_context)?;
            }
            E::ObjectCompr {
                key, value, query, ..
            } => {
                let compr_context = context.child_with_output_exprs(
                    ContextType::Comprehension,
                    Some(key.clone()),
                    Some(value.clone()),
                );

                let populated_compr_context =
                    self.populate_query(module_idx, query.as_ref(), &compr_context)?;
                self.lookup.ensure_query_capacity(module_idx, query.qidx);
                self.lookup.set_query_context(
                    module_idx,
                    query.qidx,
                    populated_compr_context.clone(),
                );

                self.populate_output_expr(module_idx, key, &populated_compr_context)?;
                self.populate_output_expr(module_idx, value, &populated_compr_context)?;
            }
            E::Call { fcn, params, .. } => {
                self.process_expr_for_contexts(module_idx, fcn, context)?;
                for param in params {
                    self.process_expr_for_contexts(module_idx, param, context)?;
                }
            }
            E::UnaryExpr { expr, .. } => {
                self.process_expr_for_contexts(module_idx, expr, context)?;
            }
            E::RefDot { refr, .. } => {
                self.process_expr_for_contexts(module_idx, refr, context)?;
            }
            E::RefBrack { refr, index, .. } => {
                self.process_expr_for_contexts(module_idx, refr, context)?;
                self.process_expr_for_contexts(module_idx, index, context)?;
            }
            E::BinExpr { lhs, rhs, .. }
            | E::BoolExpr { lhs, rhs, .. }
            | E::ArithExpr { lhs, rhs, .. } => {
                self.process_expr_for_contexts(module_idx, lhs, context)?;
                self.process_expr_for_contexts(module_idx, rhs, context)?;
            }
            E::AssignExpr { lhs, rhs, .. } => {
                self.process_expr_for_contexts(module_idx, lhs, context)?;
                self.process_expr_for_contexts(module_idx, rhs, context)?;
            }
            E::Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key_expr) = key {
                    self.process_expr_for_contexts(module_idx, key_expr, context)?;
                }
                self.process_expr_for_contexts(module_idx, value, context)?;
                self.process_expr_for_contexts(module_idx, collection, context)?;
            }
            #[cfg(feature = "rego-extensions")]
            E::OrExpr { lhs, rhs, .. } => {
                self.process_expr_for_contexts(module_idx, lhs, context)?;
                self.process_expr_for_contexts(module_idx, rhs, context)?;
            }
            _ => {}
        }

        Ok(())
    }

    /// Hoist loops from expressions with variable binding context
    fn hoist_loops_from_expr_with_context(
        &self,
        module_idx: u32,
        expr: &ExprRef,
        loops: &mut Vec<HoistedLoop>,
        context: &ScopeContext,
    ) -> Result<()> {
        use Expr::*;
        match expr.as_ref() {
            // Primitive types - no loops to hoist
            String { .. }
            | RawString { .. }
            | Number { .. }
            | Bool { .. }
            | Null { .. }
            | Var { .. } => {
                // No sub-expressions to process
            }

            // Collection types - hoist from items
            Array { items, .. } => {
                for item in items {
                    self.hoist_loops_from_expr_with_context(module_idx, item, loops, context)?;
                }
            }
            Set { items, .. } => {
                for item in items {
                    self.hoist_loops_from_expr_with_context(module_idx, item, loops, context)?;
                }
            }
            Object { fields, .. } => {
                for (_, key_expr, value_expr) in fields {
                    self.hoist_loops_from_expr_with_context(module_idx, key_expr, loops, context)?;
                    self.hoist_loops_from_expr_with_context(
                        module_idx, value_expr, loops, context,
                    )?;
                }
            }

            // Comprehensions - process their queries
            // Note: Comprehension contexts and output expressions will be handled
            // by populate_comprehension called from the parent expression processing
            ArrayCompr { term, query, .. } | SetCompr { term, query, .. } => {
                let child_context = self
                    .lookup
                    .get_query_context(module_idx, query.qidx)
                    .cloned()
                    .unwrap_or_else(|| context.child());
                for stmt in &query.stmts {
                    self.hoist_loops_from_literal_with_context(
                        module_idx,
                        &stmt.literal,
                        &child_context,
                    )?;
                }
                self.hoist_loops_from_expr_with_context(module_idx, term, loops, &child_context)?;
            }
            ObjectCompr {
                key, value, query, ..
            } => {
                let child_context = self
                    .lookup
                    .get_query_context(module_idx, query.qidx)
                    .cloned()
                    .unwrap_or_else(|| context.child());
                for stmt in &query.stmts {
                    self.hoist_loops_from_literal_with_context(
                        module_idx,
                        &stmt.literal,
                        &child_context,
                    )?;
                }
                self.hoist_loops_from_expr_with_context(module_idx, key, loops, &child_context)?;
                self.hoist_loops_from_expr_with_context(module_idx, value, loops, &child_context)?;
            }

            // Function calls - check for walk() builtin which generates loops
            Call { fcn, params, .. } => {
                // First hoist loops in parameters.
                for param in params {
                    self.hoist_loops_from_expr_with_context(module_idx, param, loops, context)?;
                }

                // Check if this is a walk() call
                let is_walk = if let Var {
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
                        key: None, // walk doesn't have an index
                        value: expr.clone(),
                        collection: expr.clone(), // The walk call itself
                        loop_type: LoopType::Walk,
                    });
                    return Ok(());
                }

                // For other function calls, hoist loops in parameters
            }

            // Unary expressions - hoist from operand
            UnaryExpr { expr, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, expr, loops, context)?;
            }

            // Reference expressions - check for array[_] patterns
            RefDot { refr, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, refr, loops, context)?;
            }
            RefBrack { refr, index, .. } => {
                // Recursively hoist from sub-expressions
                self.hoist_loops_from_expr_with_context(module_idx, refr, loops, context)?;
                self.hoist_loops_from_expr_with_context(module_idx, index, loops, context)?;

                // Check if the index expression contains unbound variables
                // This handles both simple cases like array[x] and complex cases like array[[x, y]]
                if Self::expr_contains_unbound_vars(index, context) {
                    // This index contains unbound variables - create a loop to iterate
                    loops.push(HoistedLoop {
                        loop_expr: Some(expr.clone()),
                        key: Some(index.clone()),
                        value: expr.clone(),
                        collection: refr.clone(),
                        loop_type: LoopType::IndexIteration,
                    });
                    return Ok(());
                }
            }

            // Binary expressions - hoist from both operands
            BinExpr { lhs, rhs, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, lhs, loops, context)?;
                self.hoist_loops_from_expr_with_context(module_idx, rhs, loops, context)?;
            }
            BoolExpr { lhs, rhs, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, lhs, loops, context)?;
                self.hoist_loops_from_expr_with_context(module_idx, rhs, loops, context)?;
            }
            ArithExpr { lhs, rhs, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, lhs, loops, context)?;
                self.hoist_loops_from_expr_with_context(module_idx, rhs, loops, context)?;
            }
            AssignExpr { lhs, rhs, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, lhs, loops, context)?;
                self.hoist_loops_from_expr_with_context(module_idx, rhs, loops, context)?;
            }

            // Membership expressions - hoist from key, value, and collection
            Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key_expr) = key {
                    self.hoist_loops_from_expr_with_context(module_idx, key_expr, loops, context)?;
                }
                self.hoist_loops_from_expr_with_context(module_idx, value, loops, context)?;
                self.hoist_loops_from_expr_with_context(module_idx, collection, loops, context)?;
            }

            // Handle conditionally compiled expression types
            #[cfg(feature = "rego-extensions")]
            OrExpr { lhs, rhs, .. } => {
                self.hoist_loops_from_expr_with_context(module_idx, lhs, loops, context)?;
                self.hoist_loops_from_expr_with_context(module_idx, rhs, loops, context)?;
            }
        }
        Ok(())
    }

    /// Update context based on variable bindings in a literal
    fn update_context_from_literal(&self, literal: &Literal, context: &mut ScopeContext) {
        use crate::ast::Expr as E;
        use Literal::*;
        match literal {
            SomeIn { key, value, .. } => {
                // Bind the loop variables
                if let Some(key_expr) = key {
                    if let E::Var { span, .. } = key_expr.as_ref() {
                        context.bind_variable(span.text());
                    }
                }
                if let E::Var { span, .. } = value.as_ref() {
                    context.bind_variable(span.text());
                }
            }
            Expr { expr, .. } => {
                // Look for assignment expressions that bind variables
                if let E::AssignExpr { lhs, .. } = expr.as_ref() {
                    Self::bind_variables_from_expr(lhs, context);
                }
            }
            _ => {}
        }
    }

    /// Recursively bind variables from an expression (for assignments)
    fn bind_variables_from_expr(expr: &ExprRef, context: &mut ScopeContext) {
        use crate::ast::Expr as E;
        match expr.as_ref() {
            E::Var { span, .. } => {
                context.bind_variable(span.text());
            }
            E::Array { items, .. } => {
                for item in items {
                    Self::bind_variables_from_expr(item, context);
                }
            }
            E::Object { fields, .. } => {
                for (_, key_expr, value_expr) in fields {
                    Self::bind_variables_from_expr(key_expr, context);
                    Self::bind_variables_from_expr(value_expr, context);
                }
            }
            _ => {}
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
        let mut loops = Vec::new();
        self.hoist_loops_from_expr_with_context(module_idx, expr, &mut loops, context)?;

        // Always store expression loops, even if empty
        // This ensures the interpreter can always find an entry
        let expr_idx = expr.as_ref().eidx();
        self.lookup.ensure_expr_capacity(module_idx, expr_idx);
        self.lookup.set_expr_loops(module_idx, expr_idx, loops);

        // Traverse child expressions to populate any nested contexts (e.g., comprehensions)
        self.process_expr_for_contexts(module_idx, expr, context)?;

        Ok(())
    }
}

impl Default for LoopHoister {
    fn default() -> Self {
        Self::new()
    }
}
