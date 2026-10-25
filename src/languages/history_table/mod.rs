// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! History tables: ordered `{mode, request, history}` rules compiled to one
//! `HistoryDecide` instruction.
//!
//! Table grammar: `{"rules": [{"mode": "forbid"|"require", "request": <pattern>,
//! "history": <regex>}, …]}` where `request`/`history` use the `history.match`
//! policy grammar. The emitted program reads `input = {"history": <handle>,
//! "request": <event>}` and returns `null` (grant) or the index of the first
//! violated rule.

use crate::builtins::history::{source, ObservationWorld};
use crate::rvm::instructions::HistoryDecideParams;
use crate::rvm::program::{HistoryRuleMode, HistoryTable, HistoryTableRule, Program};
use crate::rvm::Instruction;
use crate::utils::limits::ExecutionTimer;
use crate::value::Value;
use alloc::string::{String, ToString as _};
use alloc::sync::Arc;
use alloc::vec::Vec;

/// History table compilation failures.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum HistoryTableError {
    #[error("history table must be an object")]
    NotAnObject,
    #[error("history table must have a `rules` array")]
    MissingRules,
    #[error("history table rule {0} must be an object")]
    RuleNotAnObject(usize),
    #[error("history table rule {index} has invalid mode {found:?}")]
    BadMode { index: usize, found: String },
    #[error("history table rule {index} is missing `{member}`")]
    MissingMember { index: usize, member: &'static str },
    #[error("history table rule {index} is invalid: {message}")]
    InvalidPair { index: usize, message: String },
    #[error("history table has too many rules ({0})")]
    TooManyRules(usize),
}

/// Compile a history table `Value` into an RVM program with entry point `decide`.
pub fn compile(table: &Value) -> Result<Arc<Program>, HistoryTableError> {
    let Value::Object(ref members) = *table else {
        return Err(HistoryTableError::NotAnObject);
    };
    let Some(rules) = members
        .get(&Value::from("rules"))
        .and_then(|rules| rules.as_array().ok())
    else {
        return Err(HistoryTableError::MissingRules);
    };

    let mut program = Program::new();
    let mut table_rules = Vec::with_capacity(rules.len());
    for (index, rule) in rules.iter().enumerate() {
        let Value::Object(ref fields) = *rule else {
            return Err(HistoryTableError::RuleNotAnObject(index));
        };
        if let Some(key) = fields.keys().find(|k| {
            !matches!(
                k.as_string().map(|s| s.as_ref()),
                Ok("mode" | "request" | "history")
            )
        }) {
            return Err(HistoryTableError::InvalidPair {
                index,
                message: alloc::format!("unknown member {key}"),
            });
        }
        let member = |name: &'static str| {
            fields
                .get(&Value::from(name))
                .ok_or(HistoryTableError::MissingMember {
                    index,
                    member: name,
                })
        };
        let mode = match member("mode")?.as_string().map(|s| s.as_ref()) {
            Ok("forbid") => HistoryRuleMode::Forbid,
            Ok("require") => HistoryRuleMode::Require,
            _ => {
                return Err(HistoryTableError::BadMode {
                    index,
                    found: member("mode")?.to_string(),
                })
            }
        };
        let mut pair = Value::new_object();
        let pair_fields = pair
            .as_object_mut()
            .map_err(|e| HistoryTableError::InvalidPair {
                index,
                message: e.to_string(),
            })?;
        pair_fields.insert(Value::from("request"), member("request")?.clone());
        pair_fields.insert(Value::from("history"), member("history")?.clone());

        // Surface grammar errors now rather than at the first decision.
        let mut timer = ExecutionTimer::new(None);
        source::compile_pair(&pair, &mut timer, &mut ObservationWorld)
            .map_err(|e| HistoryTableError::InvalidPair {
                index,
                message: alloc::format!("{e}"),
            })?
            .release();

        let pair_literal = u16::try_from(program.add_literal(pair))
            .map_err(|_| HistoryTableError::TooManyRules(rules.len()))?;
        table_rules.push(HistoryTableRule { mode, pair_literal });
    }

    let history_key = literal(&mut program, "history", rules.len())?;
    let request_key = literal(&mut program, "request", rules.len())?;
    let table_index = program.add_history_table(HistoryTable { rules: table_rules });
    let params_index = program.add_history_decide_params(HistoryDecideParams {
        dest: 0,
        table: table_index,
        history: 2,
        request: 3,
    });
    program.instructions = alloc::vec![
        Instruction::LoadInput { dest: 1 },
        Instruction::IndexLiteral {
            dest: 2,
            container: 1,
            literal_idx: history_key,
        },
        Instruction::IndexLiteral {
            dest: 3,
            container: 1,
            literal_idx: request_key,
        },
        Instruction::HistoryDecide { params_index },
        Instruction::Return { value: 0 },
    ];
    program.instruction_spans = alloc::vec![None; program.instructions.len()];
    program.main_entry_point = 0;
    program.add_entry_point("decide".to_string(), 0);
    program.dispatch_window_size = 4;
    program.max_rule_window_size = 4;
    program.metadata.language = "history_table".to_string();
    program
        .initialize_resolved_builtins()
        .and_then(|()| program.validate_limits().map_err(anyhow::Error::msg))
        .map_err(|e| HistoryTableError::InvalidPair {
            index: 0,
            message: alloc::format!("{e}"),
        })?;
    Ok(Arc::new(program))
}

fn literal(program: &mut Program, key: &str, rules: usize) -> Result<u16, HistoryTableError> {
    u16::try_from(program.add_literal(Value::from(key)))
        .map_err(|_| HistoryTableError::TooManyRules(rules))
}
