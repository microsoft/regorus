// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::interpreter::*;
use crate::lexer::*;
use crate::parser::*;
use crate::scheduler::*;
use crate::value::*;

use anyhow::Result;

#[derive(Clone)]
pub struct Engine {
    modules: Vec<std::rc::Rc<Module>>,
    input: Value,
    data: Value,
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

impl Engine {
    pub fn new() -> Self {
        Self {
            modules: vec![],
            input: Value::new_object(),
            data: Value::new_object(),
        }
    }

    pub fn add_policy(&mut self, path: String, rego: String) -> Result<()> {
        let source = Source::new(path, rego);
        let mut parser = Parser::new(&source)?;
        self.modules.push(std::rc::Rc::new(parser.parse()?));
        Ok(())
    }

    pub fn add_policy_from_file(&mut self, path: String) -> Result<()> {
        let source = Source::from_file(path)?;
        let mut parser = Parser::new(&source)?;
        self.modules.push(std::rc::Rc::new(parser.parse()?));
        Ok(())
    }

    pub fn set_input(&mut self, input: Value) {
        self.input = input;
    }

    pub fn clear_data(&mut self) {
        self.data = Value::new_object();
    }

    pub fn add_data(&mut self, data: Value) -> Result<()> {
        self.data.merge(data)
    }

    pub fn eval_query(&self, query: String, enable_tracing: bool) -> Result<QueryResults> {
        let modules_ref: Vec<&Module> = self.modules.iter().map(|m| &**m).collect();

        // Analyze the modules and determine how statements must be scheduled.
        let analyzer = Analyzer::new();
        let schedule = analyzer.analyze(&modules_ref)?;

        // Create interpreter object.
        let mut interpreter = Interpreter::new(&modules_ref)?;

        // Evaluate all the modules.
        interpreter.eval(
            &Some(self.data.clone()),
            &Some(self.input.clone()),
            false,
            Some(schedule),
        )?;

        // Parse the query.
        let query_len = query.len();
        let query_source = Source::new("<query.rego>".to_string(), query);
        let query_span = Span {
            source: query_source.clone(),
            line: 1,
            col: 1,
            start: 0,
            end: query_len as u16,
        };
        let mut parser = Parser::new(&query_source)?;
        let query_node = parser.parse_query(query_span, "")?;
        let query_schedule = Analyzer::new().analyze_query_snippet(&modules_ref, &query_node)?;

        let results = interpreter.eval_user_query(&query_node, &query_schedule, enable_tracing)?;
        Ok(results)
    }
}
