// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::interpreter::*;
use crate::lexer::*;
use crate::parser::*;
use crate::scheduler::*;
use crate::utils::gather_functions;
use crate::value::*;

use anyhow::Result;

#[derive(Clone)]
pub struct Engine {
    modules: Vec<Ref<Module>>,
    interpreter: Interpreter,
    prepared: bool,
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
            interpreter: Interpreter::new(),
            prepared: false,
        }
    }

    pub fn add_policy(&mut self, path: String, rego: String) -> Result<()> {
        let source = Source::new(path, rego);
        let mut parser = Parser::new(&source)?;
        self.modules.push(Ref::new(parser.parse()?));
        // if policies change, interpreter needs to be prepared again
        self.prepared = false;
        Ok(())
    }

    pub fn add_policy_from_file(&mut self, path: String) -> Result<()> {
        let source = Source::from_file(path)?;
        let mut parser = Parser::new(&source)?;
        self.modules.push(Ref::new(parser.parse()?));
        self.prepared = false;
        Ok(())
    }

    pub fn set_input(&mut self, input: Value) {
        self.interpreter.set_input(input);
    }

    pub fn clear_data(&mut self) {
        self.interpreter.set_data(Value::new_object());
        self.prepared = false;
    }

    pub fn add_data(&mut self, data: Value) -> Result<()> {
        self.prepared = false;
        self.interpreter.get_data_mut().merge(data)
    }

    pub fn get_modules(&mut self) -> &Vec<Ref<Module>> {
        &self.modules
    }

    fn prepare_for_eval(&mut self, enable_tracing: bool) -> Result<()> {
        self.interpreter.set_traces(enable_tracing);

        // if the data/policies have changed or the interpreter has never been prepared
        if !self.prepared {
            // Analyze the modules and determine how statements must be scheduled.
            let analyzer = Analyzer::new();
            let schedule = analyzer.analyze(&self.modules)?;

            self.interpreter.init_with_document()?;
            self.interpreter.set_schedule(Some(schedule));
            self.interpreter.set_modules(&self.modules);

            self.interpreter.clear_builtins_cache();
            // when the interpreter is prepared the initial data is saved
            // the data will be reset to init_data each time clean_internal_evaluation_state is called
            let init_data = self.interpreter.get_data_mut().clone();
            self.interpreter.set_init_data(init_data);

            self.interpreter
                .set_functions(gather_functions(&self.modules)?);
            self.interpreter.gather_rules()?;
            self.prepared = true;
        }

        Ok(())
    }

    pub fn eval_rule(
        &mut self,
        module: &Ref<Module>,
        rule: &Ref<Rule>,
        enable_tracing: bool,
    ) -> Result<Value> {
        self.prepare_for_eval(enable_tracing)?;
        self.interpreter.clean_internal_evaluation_state();

        self.interpreter.eval_rule(module, rule)?;

        Ok(self.interpreter.get_data_mut().clone())
    }

    pub fn eval_modules(&mut self, enable_tracing: bool) -> Result<Value> {
        self.prepare_for_eval(enable_tracing)?;
        self.interpreter.clean_internal_evaluation_state();

        // Ensure that each module has an empty object
        for m in &self.modules {
            let path = Parser::get_path_ref_components(&m.package.refr)?;
            let path: Vec<&str> = path.iter().map(|s| *s.text()).collect();
            let vref =
                Interpreter::make_or_get_value_mut(self.interpreter.get_data_mut(), &path[..])?;
            if *vref == Value::Undefined {
                *vref = Value::new_object();
            }
        }

        self.interpreter.check_default_rules()?;
        for module in self.modules.clone() {
            for rule in &module.policy {
                self.interpreter.eval_rule(&module, rule)?;
            }
        }
        // Defer the evaluation of the default rules to here
        for module in self.modules.clone() {
            let prev_module = self.interpreter.set_current_module(Some(module.clone()))?;
            for rule in &module.policy {
                self.interpreter.eval_default_rule(rule)?;
            }
            self.interpreter.set_current_module(prev_module)?;
        }

        Ok(self.interpreter.get_data_mut().clone())
    }

    pub fn eval_query(&mut self, query: String, enable_tracing: bool) -> Result<QueryResults> {
        self.eval_modules(false)?;

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
        let query_node = Ref::new(parser.parse_query(query_span, "")?);
        let query_schedule = Analyzer::new().analyze_query_snippet(&self.modules, &query_node)?;

        let results =
            self.interpreter
                .eval_user_query(&query_node, &query_schedule, enable_tracing)?;
        Ok(results)
    }
}
