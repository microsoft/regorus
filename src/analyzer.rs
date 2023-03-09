// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::value::*;

use anyhow::{bail, Result};
use std::collections::{BTreeMap, HashMap};
use std::vec;

pub struct Analyzer<'source> {
    input: Value,
    globals: Vec<String>,
    current_module_path: String,
    sorted_stmts: BTreeMap<&'source Query<'source>, Vec<&'source LiteralStmt<'source>>>,
}

#[derive(Debug, Default, Clone)]
pub struct Symbols {
    inputs: Vec<String>,
    outputs: Vec<String>,
    undecided: Vec<(String, String)>,
}

#[derive(Debug, Default)]
struct Node<'source> {
    symbols: Symbols,
    queries: Option<Vec<&'source Query<'source>>>,
}

impl<'source> Default for Analyzer<'source> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'source> Analyzer<'source> {
    pub fn new() -> Analyzer<'source> {
        Analyzer {
            input: Value::new_object(),
            globals: vec![],
            current_module_path: String::new(),
            sorted_stmts: BTreeMap::new(),
        }
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

    fn set_current_module(&mut self, module: Option<&'source Module<'source>>) -> Result<()> {
        if let Some(m) = module {
            self.current_module_path = Self::get_path_string(&m.package.refr, Some("data"))?;
        }
        Ok(())
    }

    fn get_path_string(refr: &Expr, document: Option<&str>) -> Result<String> {
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

    pub fn analyze_modules(&mut self, modules: &'source [&'source Module<'source>]) -> Result<()> {
        let mut queue: Vec<&'source Module<'source>> = vec![];

        for module in modules.iter().copied() {
            let mut symbols = Symbols::default();

            self.set_current_module(Some(module))?;
            for rule in &module.policy {
                let refr = Self::get_rule_refr(rule);
                let refr = match refr {
                    Expr::RefBrack { index, .. } if matches!(index.as_ref(), Expr::String(_)) => {
                        refr
                    }
                    Expr::RefBrack { refr, .. } => refr,
                    _ => refr,
                };
                let path = Self::get_path_string(refr, None)?;
                let path = self.current_module_path.clone() + "." + &path;
                self.globals.push(path.clone());
                symbols.outputs.push(path);
            }

            queue.push(module);
        }

        println!("[analyzer] globals: {:?}", self.globals);

        while let Some(module) = queue.pop() {
            self.set_current_module(Some(module))?;
            for rule in &module.policy {
                self.analyze_rule(rule)?;
            }
        }

        for (query, sorted_stmts) in &self.sorted_stmts {
            println!("query: {:?}\nsorted stmts: {:?}", *query, *sorted_stmts);
        }

        Ok(())
    }

    fn analyze_rule(&mut self, rule: &'source Rule<'source>) -> Result<()> {
        println!("Analyze rule {:?}", rule);

        if let Rule::Spec { head, bodies, .. } = rule {
            if matches!(head, RuleHead::Func { .. }) {
                return Ok(());
            }

            self.analyze_rule_head(head)?;
            self.analyze_rule_bodies(bodies)?;
        }

        Ok(())
    }

    fn analyze_rule_head(&mut self, head: &'source RuleHead<'source>) -> Result<()> {
        match head {
            RuleHead::Compr { assign, .. } => {
                if let Some(rule_assign) = assign {
                    let scope_in = Symbols::default();
                    let mut scope_out = Symbols::default();
                    let mut queue = vec![];

                    self.analyze_expr(&rule_assign.value, &scope_in, &mut scope_out, &mut queue)?;

                    let scope_in = scope_out;
                    let mut scope_out = Symbols::default();
                    while let Some(query) = queue.pop() {
                        self.analyze_query(query, &scope_in, &mut scope_out)?;
                    }
                }
            }
            RuleHead::Set { key, .. } => {
                if let Some(key_expr) = key {
                    let scope_in = Symbols::default();
                    let mut scope_out = Symbols::default();
                    let mut queue = vec![];

                    self.analyze_expr(key_expr, &scope_in, &mut scope_out, &mut queue)?;

                    let scope_in = scope_out;
                    let mut scope_out = Symbols::default();
                    while let Some(query) = queue.pop() {
                        self.analyze_query(query, &scope_in, &mut scope_out)?;
                    }
                }
            }
            _ => unimplemented!("unhandled rule head"),
        }

        Ok(())
    }

    fn analyze_rule_bodies(&mut self, bodies: &'source Vec<RuleBody<'source>>) -> Result<()> {
        if bodies.is_empty() {
            return Ok(());
        } else {
            for body in bodies {
                let scope_in = Symbols::default();
                let mut scope_out = Symbols::default();
                self.analyze_query(&body.query, &scope_in, &mut scope_out)?;

                if bodies.len() > 1 {
                    unimplemented!("else bodies");
                }
            }
        }

        Ok(())
    }

    fn analyze_query(
        &mut self,
        query: &'source Query<'source>,
        symbols_in: &Symbols,
        symbols_out: &mut Symbols,
    ) -> Result<()> {
        println!("query: {:?}\nquery scope: {:?}", query, symbols_out);
        let sorted_order = self.analyze_stmts(&query.stmts, symbols_in, symbols_out)?;
        println!("sorted_order: {:?}", sorted_order);

        let mut sorted_stmts = vec![];
        for index in sorted_order {
            sorted_stmts.push(&query.stmts[index]);
        }
        self.sorted_stmts.insert(query, sorted_stmts);

        Ok(())
    }

    fn analyze_stmts(
        &mut self,
        stmts: &'source [LiteralStmt<'source>],
        symbols_in: &Symbols,
        symbols_out: &mut Symbols,
    ) -> Result<Vec<usize>> {
        let mut stmts_symbols = Symbols::default();
        let mut nodes = vec![];

        for stmt in stmts.iter() {
            let mut stmt_symbols = Symbols::default();
            let mut queue = vec![];
            match &stmt.literal {
                Literal::Expr { expr, .. } => {
                    self.analyze_expr(expr, symbols_in, &mut stmt_symbols, &mut queue)?;
                }
                Literal::NotExpr { expr, .. } => {
                    self.analyze_expr(expr, symbols_in, &mut stmt_symbols, &mut queue)?;
                }
                Literal::Every {
                    key,
                    value,
                    domain,
                    query,
                    ..
                } => {
                    if let Some(key) = key {
                        stmts_symbols.outputs.push(key.text().to_string());
                    }
                    stmts_symbols.outputs.push(value.text().to_string());
                    self.analyze_expr(domain, symbols_in, &mut stmt_symbols, &mut queue)?;
                    queue.push(query);
                }
                Literal::SomeIn {
                    key,
                    value,
                    collection,
                    ..
                } => {
                    if let Some(key) = key {
                        self.analyze_expr(key, symbols_in, &mut stmt_symbols, &mut queue)?;
                    }
                    self.analyze_expr(value, symbols_in, &mut stmt_symbols, &mut queue)?;
                    self.analyze_expr(collection, symbols_in, &mut stmt_symbols, &mut queue)?;
                }
                Literal::SomeVars { .. } => {
                    // Ignore some for now so that we always sort it at the top
                }
            }
            println!("stmt: {:?}\nstmt symbols: {:?}", stmt, stmt_symbols);
            nodes.push(Node {
                symbols: stmt_symbols.clone(),
                queries: Some(queue),
            });
            symbols_out.inputs.extend(stmt_symbols.inputs);
            stmts_symbols.outputs.extend(stmt_symbols.outputs);
            stmts_symbols.undecided.extend(stmt_symbols.undecided);
        }

        // Extend the in scope
        let mut symbols_in = symbols_in.clone();
        symbols_in.outputs.extend(stmts_symbols.outputs);
        symbols_in.undecided.extend(stmts_symbols.undecided);

        for node in nodes.iter_mut() {
            if let Some(queue) = &node.queries {
                queue.iter().for_each(|query| {
                    let mut scope_out = Symbols::default();
                    self.analyze_query(query, &symbols_in, &mut scope_out)
                        .unwrap();
                    println!("query: {:?}\nout symbols: {:?}", query, scope_out);

                    // Merge the dependencies from the nested query and avoid duplications
                    scope_out.inputs.iter().for_each(|input| {
                        if !node.symbols.inputs.iter().any(|symbol| symbol == input) {
                            node.symbols.inputs.push(input.to_string());
                        }
                    });
                });
            }
        }

        self.sort(&mut nodes)
    }

    fn analyze_expr(
        &mut self,
        expr: &'source Expr,
        symbols_in: &Symbols,
        symbols_out: &mut Symbols,
        queue: &mut Vec<&'source Query<'source>>,
    ) -> Result<()> {
        match expr {
            Expr::Null(_) |
            Expr::True(_) |
            Expr::False(_) |
            Expr::Number(_) |
            // TODO: Handle string vs rawstring
            Expr::String(_) |
            Expr::RawString(_) => {},

            // TODO: Handle undefined variables
            Expr::Var(_) => self.analyze_chained_ref_dot_or_brack(expr, symbols_in, symbols_out, queue)?,
            Expr::RefDot { .. } => self.analyze_chained_ref_dot_or_brack(expr, symbols_in, symbols_out, queue)?,
            Expr::RefBrack { .. } => self.analyze_chained_ref_dot_or_brack(expr, symbols_in, symbols_out, queue)?,

            // Expressions with operators
            Expr::AssignExpr { op, lhs, rhs, .. } => self.analyze_assign_expr(op, lhs, rhs, symbols_in, symbols_out, queue)?,
            Expr::ArithExpr { lhs, rhs, .. } |
            Expr::BinExpr { lhs, rhs, .. } |
            Expr::BoolExpr { lhs, rhs, .. } => {
                self.analyze_expr(lhs, symbols_in, symbols_out, queue)?;
                self.analyze_expr(rhs, symbols_in, symbols_out, queue)?;
            }
            Expr::Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key.as_ref() {
                    self.analyze_expr(key, symbols_in, symbols_out, queue)?;
                }
                self.analyze_expr(value, symbols_in, symbols_out, queue)?;
                self.analyze_expr(collection, symbols_in, symbols_out, queue)?;
            }

            // Creation expression
            Expr::Array { items, .. } |
            Expr::Set { items, .. } => {
                items.iter().for_each(|item| {
                    self.analyze_expr(item, symbols_in, symbols_out, queue).unwrap();
                });
            }
            Expr::Object { fields, .. } => {
                fields.iter().for_each(|(_, key, value)| {
                    self.analyze_expr(key, symbols_in, symbols_out, queue).unwrap();
                    self.analyze_expr(value, symbols_in, symbols_out, queue).unwrap();
                });
            }

            // Comprehensions
            Expr::ArrayCompr { term, query, .. } |
            Expr::SetCompr { term, query, .. } => {
                if let Expr::Var(span) = term.as_ref() {
                    let name = span.text();
                    if self.lookup_var(name, &[], symbols_in)? {
                        symbols_out.inputs.push(name.to_string());
                    }
                } else {
                    // TODO: Handle nested variables
                    self.analyze_expr(term, symbols_in, symbols_out, queue)?;
                }
                queue.push(query);
            }
            Expr::ObjectCompr {
                key, value, query, ..
            } => {
                if let Expr::Var(span) = key.as_ref() {
                    let name = span.text();
                    if self.lookup_var(name, &[], symbols_in)? {
                        symbols_out.inputs.push(name.to_string());
                    }
                } else {
                    // TODO: Handle nested variables
                    self.analyze_expr(key, symbols_in, symbols_out, queue)?;
                }
                if let Expr::Var(span) = value.as_ref() {
                    let name = span.text();
                    if self.lookup_var(name, &[], symbols_in)? {
                        symbols_out.inputs.push(name.to_string());
                    }
                } else {
                    // TODO: Handle nested variables
                    self.analyze_expr(value, symbols_in, symbols_out, queue)?;
                }
                queue.push(query);
            }
            Expr::UnaryExpr { .. } => unimplemented!("unar expr is unimplemented"),
            Expr::Call { params, .. } => {
                params.iter().for_each(|param| {
                    self.analyze_expr(param, symbols_in, symbols_out, queue).unwrap();
                });
            }
        }

        Ok(())
    }

    fn analyze_assign_expr(
        &mut self,
        op: &AssignOp,
        lhs: &'source Expr<'source>,
        rhs: &'source Expr<'source>,
        symbols_in: &Symbols,
        symbols_out: &mut Symbols,
        queue: &mut Vec<&'source Query<'source>>,
    ) -> Result<()> {
        match op {
            AssignOp::Eq => {
                if matches!(lhs, Expr::Var(_)) && !matches!(rhs, Expr::Var(_)) {
                    if let Expr::Var(span) = lhs {
                        let name = span.text();
                        if self.lookup_var(name, &[], symbols_in)? {
                            // If the variable is found in the upper scopes, treat
                            // the assignment as comparison
                            // Do nothing as we don't need to track the dependency
                            // to the upper scope for a variable
                        } else {
                            // Otherwise, the variable should be an output
                            symbols_out.outputs.push(span.text().to_string());
                        }
                    }
                    self.analyze_expr(rhs, symbols_in, symbols_out, queue)?;
                } else if !matches!(lhs, Expr::Var(_)) && matches!(rhs, Expr::Var(_)) {
                    if let Expr::Var(span) = rhs {
                        let name = span.text();
                        if self.lookup_var(name, &[], symbols_in)? {
                            // If the variable is found in the upper scopes, treat
                            // the assignment as comparison
                            // Do nothing as we don't need to track the dependency
                            // to the upper scope for a variable
                        } else {
                            // Otherwise, the variable should be an output
                            symbols_out.outputs.push(span.text().to_string());
                        }
                    }
                    self.analyze_expr(lhs, symbols_in, symbols_out, queue)?;
                } else if matches!(lhs, Expr::Var(_)) && matches!(rhs, Expr::Var(_)) {
                    let lhs_name = if let Expr::Var(span) = lhs {
                        span.text()
                    } else {
                        unreachable!();
                    };

                    let rhs_name = if let Expr::Var(span) = rhs {
                        span.text()
                    } else {
                        unreachable!();
                    };

                    let lhs_found = self.lookup_var(lhs_name, &[], symbols_in)?;
                    let rhs_found = self.lookup_var(rhs_name, &[], symbols_in)?;

                    if lhs_found && !rhs_found {
                        // lhs is an input, rhs is an output
                        symbols_out.outputs.push(rhs_name.to_string());
                    } else if !lhs_found && rhs_found {
                        // lhs is an output, rhs is an input
                        symbols_out.outputs.push(lhs_name.to_string());
                    } else if lhs_found && rhs_found {
                        // Fall back to comparison
                        self.analyze_expr(lhs, symbols_in, symbols_out, queue)?;
                        self.analyze_expr(rhs, symbols_in, symbols_out, queue)?;
                    } else {
                        // Cannot decide if lhs and rhs are inputs or inputs. Add them to
                        // both queues so that we can determine later.
                        symbols_out
                            .undecided
                            .push((rhs_name.to_string(), lhs_name.to_string()));
                    }
                } else {
                    // Fall back to comparison
                    self.analyze_expr(lhs, symbols_in, symbols_out, queue)?;
                    self.analyze_expr(rhs, symbols_in, symbols_out, queue)?;
                }
            }
            AssignOp::ColEq => {
                if let Expr::Var(span) = lhs {
                    if symbols_out
                        .inputs
                        .iter()
                        .any(|symbol| symbol == span.text())
                    {
                        bail!(
                            "internal error: var {} already exists in the current scope",
                            span.text()
                        );
                    }
                    if symbols_out
                        .outputs
                        .iter()
                        .any(|symbol| symbol == span.text())
                    {
                        bail!(
                            "internal error: var {} already exists in the current scope",
                            span.text()
                        );
                    }
                    symbols_out.outputs.push(span.text().to_string());
                } else {
                    bail!("internal error: cannot assign to ref");
                }
                self.analyze_expr(rhs, symbols_in, symbols_out, queue)?;
            }
        }

        Ok(())
    }

    fn lookup_value_chained(mut obj: Value, path: &[&str]) -> bool {
        for p in path {
            obj = obj[&Value::String(p.to_string())].clone();
        }

        !matches!(obj, Value::Undefined)
    }

    fn lookup_var(&mut self, name: &str, fields: &[&str], scope: &Symbols) -> Result<bool> {
        let mut result = false;

        // Return local variable/argument.
        if scope.outputs.iter().any(|symbol| symbol == name) {
            result = true;
        }

        if scope
            .undecided
            .iter()
            .any(|(rhs, lhs)| rhs == name || lhs == name)
        {
            // Treat the variable as dependency even if it's still undecided
            result = true;
        }

        if name == "input" {
            // Handle input
            result = Self::lookup_value_chained(self.input.clone(), fields);
        }

        if name == "data" {
            let path = "data.".to_owned() + &fields.join(".");
            if self.globals.iter().any(|var| var == &path) {
                result = true;
            }
        } else {
            // Add module prefix and ensure that any matching rule is evaluated.
            let path = self.current_module_path.clone() + "." + name;

            if self.globals.iter().any(|var| var == &path) {
                result = true;
            }
        }

        println!(
            "[lookup_var, module: {}] {} {:?} scope: {:?} - {}",
            self.current_module_path, name, fields, scope, result
        );

        Ok(result)
    }

    fn analyze_chained_ref_dot_or_brack(
        &mut self,
        mut expr: &'source Expr<'source>,
        symbols_in: &Symbols,
        symbols_out: &mut Symbols,
        queue: &mut Vec<&'source Query<'source>>,
    ) -> Result<()> {
        // Collect a chain of '.field' or '["field"]'
        let mut path = vec![];

        println!("current scope: {:?}", symbols_out);

        loop {
            match expr {
                // Stop path collection upon encountering the leading variable.
                Expr::Var(v) if !matches!(v.text(), "_") => {
                    let name = v.text();
                    path.reverse();
                    if self.lookup_var(name, &path[..], symbols_in)? {
                        if !symbols_out.inputs.iter().any(|symbol| symbol == name) {
                            symbols_out.inputs.push(v.text().to_string());
                        }
                    } else if !symbols_out.outputs.iter().any(|symbol| symbol == name) {
                        symbols_out.outputs.push(v.text().to_string());
                    }
                    break;
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
                        self.analyze_expr(refr, symbols_in, symbols_out, queue)?;
                        self.analyze_expr(index, symbols_in, symbols_out, queue)?;
                        break;
                    }
                },
                _ => break,
            }
        }

        Ok(())
    }

    fn sort(&mut self, nodes: &mut Vec<Node<'source>>) -> Result<Vec<usize>> {
        if !nodes
            .iter_mut()
            .any(|node| node.symbols.undecided.is_empty())
        {
            // No need to sort
            let mut order = vec![];
            for (index, _) in nodes.iter_mut().enumerate() {
                order.push(index);
            }
            return Ok(order);
        }

        println!("build graph from {:?}", nodes);

        let mut map = HashMap::new();
        let mut queue = vec![];

        // Build index map for nodes with output
        for (index, node) in nodes.iter_mut().enumerate() {
            if node.symbols.undecided.is_empty() {
                let outputs = node.symbols.outputs.clone();
                outputs.iter().for_each(|output| {
                    map.insert(output.to_string(), index);
                });
            } else {
                queue.push((node, index));
            }
        }

        loop {
            if queue.is_empty() {
                break;
            }

            let mut unhandled = vec![];
            let queue_len = queue.len();

            for (node, index) in queue {
                let mut undecided = vec![];
                let mut inputs = vec![];
                let mut outputs = vec![];

                while let Some((lhs, rhs)) = &node.symbols.undecided.pop() {
                    if map.get(lhs).is_some() {
                        inputs.push(lhs.to_string());
                        outputs.push(rhs.to_string());
                        map.insert(rhs.to_string(), index);
                    } else if map.get(rhs).is_some() {
                        inputs.push(rhs.to_string());
                        outputs.push(lhs.to_string());
                        map.insert(lhs.to_string(), index);
                    } else {
                        undecided.push((lhs.to_string(), rhs.to_string()));
                    }
                }

                node.symbols = Symbols {
                    inputs,
                    outputs,
                    undecided,
                };

                if !node.symbols.undecided.is_empty() {
                    unhandled.push((node, index));
                }
            }

            if unhandled.len() == queue_len {
                bail!("internal error: unsolvable constraints");
            }

            queue = unhandled;
        }

        println!("constraints solver: {:?}", nodes);

        let mut in_graph = vec![Vec::new(); nodes.len()];
        let mut out_graph = vec![Vec::new(); nodes.len()];

        for (index, node) in nodes.iter_mut().enumerate() {
            for input in &node.symbols.inputs {
                if let Some(target) = map.get(input) {
                    in_graph[*target].push(index);
                    out_graph[index].push(*target);
                }
            }
        }

        println!(
            "build graph in {:?}, out {:?}\nmap: {:?}",
            in_graph, out_graph, map
        );

        let result = self.sort_graph(in_graph, out_graph)?;

        println!("sort result: {:?}", result);

        Ok(result)
    }

    fn sort_graph(
        &mut self,
        in_graph: Vec<Vec<usize>>,
        out_graph: Vec<Vec<usize>>,
    ) -> Result<Vec<usize>> {
        if in_graph.len() == 1 {
            return Ok(vec![0]);
        }

        // Perform Kahn's algorithm for topological sorting
        let mut in_degree: Vec<usize> = in_graph.iter().map(|node| node.len()).collect();

        let mut queue = vec![];

        for (index, degree) in in_degree.iter().enumerate() {
            if *degree == 0 {
                queue.push(index);
            }
        }

        println!("in_degree: {:?}\nqueue:{:?}", in_degree, queue);

        let mut _visited_count = 0;
        let mut result = vec![];

        while let Some(node) = queue.pop() {
            result.push(node);

            for adj in &out_graph[node] {
                // Skip self-pointing
                if *adj == node {
                    continue;
                }
                in_degree[*adj] -= 1;
                if in_degree[*adj] == 0 {
                    queue.push(*adj);
                }
            }

            _visited_count += 1;
        }

        // TODO: Check
        //if visited_count != in_graph.len() {
        //bail!("internal error: found circular dependency, visited_count: {}, expected: {}",
        //visited_count, in_graph.len());
        //}

        result.reverse();

        Ok(result)
    }
}
