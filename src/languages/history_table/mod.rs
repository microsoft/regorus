// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Ordered `{mode, request, history}` rules compiled to bounded `HistoryStep`
//! instructions. Cold JSON policies describe exact principal/action/resource
//! identities; execution accepts only a staged typed event and shared history.
//! Each decision returns `null` (grant) or the first violated rule's index.

pub(crate) mod store;

pub use crate::rvm::vm::history_tables::error::HistoryError;
pub use store::{Action, Event, HistoryHandle, HistoryStore, Principal, Resource};

use crate::rvm::instructions::HistoryStepParams;
use crate::rvm::program::{
    HistoryPairSource, HistoryRuleMode, HistoryTable, HistoryTableRule, Program,
};
use crate::rvm::vm::history_tables::ObservationWorld;
use crate::rvm::Instruction;
use crate::utils::limits::ExecutionTimer;
use crate::value::Value;
use alloc::string::{String, ToString as _};
use alloc::sync::Arc;
use alloc::vec::Vec;

/// History table compilation failures.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum HistoryTableError {
    #[error("history batch_size must be greater than zero")]
    InvalidBatchSize,
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

/// Compile a portable typed history table with entry point `decide`.
/// `batch_size` bounds the events consumed by each instruction dispatch.
pub fn compile(table: &Value, batch_size: u32) -> Result<Arc<Program>, HistoryTableError> {
    if batch_size == 0 {
        return Err(HistoryTableError::InvalidBatchSize);
    }
    let Value::Object(ref members) = *table else {
        return Err(HistoryTableError::NotAnObject);
    };
    let Some(rules) = members
        .get(&Value::from("rules"))
        .and_then(|rules| rules.as_array().ok())
    else {
        return Err(HistoryTableError::MissingRules);
    };
    if rules.len() > Program::MAX_INSTRUCTIONS.saturating_sub(2) {
        return Err(HistoryTableError::TooManyRules(rules.len()));
    }

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
        let request = member("request")?;
        let history = member("history")?;
        let mut timer = ExecutionTimer::new(None);
        // Borrow the members instead of copying both policy trees into a wrapper.
        let source = HistoryPairSource::parse(request, history, &mut timer, &mut ObservationWorld)
            .map_err(|e| HistoryTableError::InvalidPair {
                index,
                message: alloc::format!("{e}"),
            })?;
        table_rules.push(HistoryTableRule { mode, source });
    }

    let table_index = program.add_history_table(HistoryTable { rules: table_rules });
    for index in 0..rules.len() {
        let rule =
            u16::try_from(index).map_err(|_| HistoryTableError::TooManyRules(rules.len()))?;
        let params_index = program.add_history_step_params(HistoryStepParams {
            table: table_index,
            rule,
            batch_size,
        });
        program
            .instructions
            .push(Instruction::HistoryStep { params_index });
    }
    program.instructions.push(Instruction::LoadNull { dest: 0 });
    program.instructions.push(Instruction::Return { value: 0 });
    program.instruction_spans = alloc::vec![None; program.instructions.len()];
    program.main_entry_point = 0;
    program.add_entry_point("decide".to_string(), 0);
    program.dispatch_window_size = 1;
    program.max_rule_window_size = 1;
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
