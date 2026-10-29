// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Sample explanation results for unit tests of code that consumes or
//! produces them.

use super::*;
use crate::value::Value;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

/// `allow` with two definitions: `input.role == "admin"` fails, and the
/// second, a v0 rule `allow { false } { ... }` with two query blocks,
/// succeeds in its second block on
/// `input.user.token == data.tokens[input.user.name]` with both operands
/// redacted.
pub fn complete_rule_report() -> ExplanationReport {
    let role = ConditionExplanation {
        text: String::from(r#"input.role == "admin""#),
        outcome: Outcome::Failure,
        kind: ConditionKind::Comparison,
        location: Some(location(4, 5)),
        operator: Some(Operator::Eq),
        left: Some(known(Value::from("guest"), Some("input.role"))),
        right: Some(known(Value::from("admin"), None)),
        witness: None,
        binding: None,
    };
    let token = ConditionExplanation {
        text: String::from("input.user.token == data.tokens[input.user.name]"),
        outcome: Outcome::Success,
        kind: ConditionKind::Comparison,
        location: Some(location(8, 5)),
        operator: Some(Operator::Eq),
        left: Some(redacted("input.user.token")),
        right: Some(redacted("data.tokens[input.user.name]")),
        witness: None,
        binding: None,
    };
    ExplanationReport {
        query_result: Value::from(true),
        rules: vec![RuleExplanation {
            name: String::from("data.test.allow"),
            kind: RuleKind::Complete,
            result: ReportedValue::Known(Value::from(true)),
            emissions: Vec::new(),
            definitions: vec![
                definition(0, 0, Outcome::Failure, 3, vec![role]),
                definition(1, 1, Outcome::Success, 7, vec![token]),
            ],
        }],
    }
}

/// `deny contains name if { some name in input.users; ... }` that emitted
/// `"bob"` after a loop over two users.
pub fn partial_set_report() -> ExplanationReport {
    let names: BTreeSet<Value> = [Value::from("bob")].into_iter().collect();
    let in_users = ConditionExplanation {
        text: String::from("some name in input.users"),
        outcome: Outcome::Success,
        kind: ConditionKind::Iteration,
        location: None,
        operator: None,
        left: None,
        right: None,
        witness: Some(LoopWitness {
            iterations: 2,
            successes: 1,
            sample_key: Some(known(Value::from(1_u64), None)),
            sample_value: Some(known(Value::from("bob"), Some("input.users"))),
        }),
        binding: Some(String::from("name")),
    };
    ExplanationReport {
        query_result: Value::from(names.clone()),
        rules: vec![RuleExplanation {
            name: String::from("data.test.deny"),
            kind: RuleKind::PartialSet,
            result: ReportedValue::Known(Value::from(names)),
            emissions: vec![emission(None, Value::from("bob"), vec![in_users.clone()])],
            definitions: vec![definition(0, 0, Outcome::Success, 3, vec![in_users])],
        }],
    }
}

/// `labels[k] := v if { some k, v in input.tags }` that emitted
/// `"env": "prod"`.
pub fn partial_object_report() -> ExplanationReport {
    let labels: BTreeMap<Value, Value> = [(Value::from("env"), Value::from("prod"))]
        .into_iter()
        .collect();
    let labels = Value::from(labels);
    let in_tags = ConditionExplanation {
        text: String::from("some k, v in input.tags"),
        outcome: Outcome::Success,
        kind: ConditionKind::Iteration,
        location: Some(location(4, 5)),
        operator: None,
        left: None,
        right: None,
        witness: Some(LoopWitness {
            iterations: 1,
            successes: 1,
            sample_key: Some(known(Value::from("env"), None)),
            sample_value: Some(known(Value::from("prod"), Some("input.tags"))),
        }),
        binding: None,
    };
    ExplanationReport {
        query_result: labels.clone(),
        rules: vec![RuleExplanation {
            name: String::from("data.test.labels"),
            kind: RuleKind::PartialObject,
            result: ReportedValue::Known(labels),
            emissions: vec![emission(
                Some(Value::from("env")),
                Value::from("prod"),
                vec![in_tags.clone()],
            )],
            definitions: vec![definition(0, 0, Outcome::Success, 3, vec![in_tags])],
        }],
    }
}

/// `allow if input.role == "admin"` and `allow if not input.locked`, with
/// all of `input` unknown. The two definitions are not ordered, but they
/// have the same value, so they can't conflict and the result is exact.
pub fn partial_eval_result() -> PartialEvalResult {
    let role = ResidualCondition {
        text: String::from(r#"input.role == "admin""#),
        kind: ResidualKind::ConditionHolds,
        operator: Some(Operator::Eq),
        input_path: Some(String::from("input.role")),
        value: Some(Value::from("admin")),
        negated: Vec::new(),
        rule: Some(String::from("data.test.allow")),
        location: Some(location(3, 5)),
    };
    let locked = ResidualCondition {
        text: String::from("input.locked"),
        kind: ResidualKind::Truthy,
        operator: None,
        input_path: Some(String::from("input.locked")),
        value: None,
        negated: Vec::new(),
        rule: None,
        location: None,
    };
    let not_locked = ResidualCondition {
        text: String::from("not input.locked"),
        kind: ResidualKind::NegationHolds,
        operator: None,
        input_path: None,
        value: None,
        negated: vec![locked],
        rule: Some(String::from("data.test.allow")),
        location: None,
    };
    PartialEvalResult {
        kind: RuleKind::Complete,
        status: ResidualStatus::Exact,
        result: Value::Undefined,
        residual_queries: vec![
            ResidualQuery {
                key: None,
                value: Value::from(true),
                conditions: vec![role],
            },
            ResidualQuery {
                key: None,
                value: Value::from(true),
                conditions: vec![not_locked],
            },
        ],
        warnings: Vec::new(),
    }
}

/// `reasons contains "admin" if input.role == "admin"` and
/// `reasons contains "locked" if input.locked`, with all of `input` unknown.
pub fn partial_eval_set_result() -> PartialEvalResult {
    let role = ResidualCondition {
        text: String::from(r#"input.role == "admin""#),
        kind: ResidualKind::ConditionHolds,
        operator: Some(Operator::Eq),
        input_path: Some(String::from("input.role")),
        value: Some(Value::from("admin")),
        negated: Vec::new(),
        rule: None,
        location: None,
    };
    let locked = ResidualCondition {
        text: String::from("input.locked"),
        kind: ResidualKind::Truthy,
        operator: None,
        input_path: Some(String::from("input.locked")),
        value: None,
        negated: Vec::new(),
        rule: None,
        location: None,
    };
    PartialEvalResult {
        kind: RuleKind::PartialSet,
        status: ResidualStatus::Exact,
        result: Value::Undefined,
        residual_queries: vec![
            ResidualQuery {
                key: None,
                value: Value::from("admin"),
                conditions: vec![role],
            },
            ResidualQuery {
                key: None,
                value: Value::from("locked"),
                conditions: vec![locked],
            },
        ],
        warnings: Vec::new(),
    }
}

/// `labels["env"] := "prod" if input.env == "prod"`, with all of `input`
/// unknown.
pub fn partial_eval_object_result() -> PartialEvalResult {
    PartialEvalResult {
        kind: RuleKind::PartialObject,
        status: ResidualStatus::Exact,
        result: Value::Undefined,
        residual_queries: vec![ResidualQuery {
            key: Some(Value::from("env")),
            value: Value::from("prod"),
            conditions: vec![ResidualCondition {
                text: String::from(r#"input.env == "prod""#),
                kind: ResidualKind::ConditionHolds,
                operator: Some(Operator::Eq),
                input_path: Some(String::from("input.env")),
                value: Some(Value::from("prod")),
                negated: Vec::new(),
                rule: None,
                location: None,
            }],
        }],
        warnings: Vec::new(),
    }
}

/// `allow := true if input.x` and `allow := false if input.y`: independent
/// definitions with different values, which conflict when both hold. A
/// single body that iterates, `allow := v if { some v in data.vals; input.x }`,
/// gives the same result.
pub fn partial_eval_conflict_result() -> PartialEvalResult {
    PartialEvalResult {
        kind: RuleKind::Complete,
        status: ResidualStatus::PossibleConflict,
        result: Value::Undefined,
        residual_queries: Vec::new(),
        warnings: vec![String::from(
            "data.test.allow: definitions with different values may both hold",
        )],
    }
}

/// `msg := input.name`, whose value is computed from unknown input.
pub fn partial_eval_unsupported_result() -> PartialEvalResult {
    PartialEvalResult {
        kind: RuleKind::Complete,
        status: ResidualStatus::Unsupported,
        result: Value::Undefined,
        residual_queries: Vec::new(),
        warnings: vec![String::from(
            "data.test.msg: the value depends on unknown input",
        )],
    }
}

pub fn known(value: Value, path: Option<&str>) -> Operand {
    Operand {
        value: ReportedValue::Known(value),
        path: path.map(String::from),
    }
}

pub fn redacted(path: &str) -> Operand {
    Operand {
        value: ReportedValue::Redacted,
        path: Some(String::from(path)),
    }
}

fn location(line: usize, column: usize) -> SourceLocation {
    SourceLocation {
        file: String::from("test.rego"),
        line,
        column,
    }
}

fn emission(
    key: Option<Value>,
    value: Value,
    conditions: Vec<ConditionExplanation>,
) -> EmissionExplanation {
    EmissionExplanation {
        index: 0,
        definition: 0,
        key: key.map(ReportedValue::Known),
        value: ReportedValue::Known(value),
        conditions,
    }
}

fn definition(
    index: usize,
    body: usize,
    outcome: Outcome,
    line: usize,
    conditions: Vec<ConditionExplanation>,
) -> DefinitionExplanation {
    DefinitionExplanation {
        index,
        body,
        outcome,
        location: Some(location(line, 1)),
        conditions,
    }
}
