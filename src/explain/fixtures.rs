// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Sample explanation results for unit tests of code that consumes or
//! produces them.

use super::*;
use crate::value::Value;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
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
        site_id: 0,
        owner: owner("data.test.allow", 0),
        outcome: Outcome::Failure,
        left: Some(known(Value::from("guest"), Some("input.role"))),
        right: Some(known(Value::from("admin"), None)),
        witness: None,
        binding: None,
    };
    let token = ConditionExplanation {
        site_id: 1,
        owner: owner("data.test.allow", 0),
        outcome: Outcome::Success,
        left: Some(redacted("input.user.token")),
        right: Some(redacted("data.tokens[input.user.name]")),
        witness: None,
        binding: None,
    };
    ExplanationReport {
        query: query("data.test.allow"),
        query_result: Value::from(true),
        rules: vec![RuleExplanation {
            name: String::from("data.test.allow"),
            call_instance: 0,
            kind: RuleKind::Complete,
            outcome: RuleOutcome::Matched,
            result: ReportedValue::Known(Value::from(true)),
            emissions: Vec::new(),
            definitions: vec![
                definition(0, 0, Outcome::Failure, 3, vec![role]),
                definition(1, 1, Outcome::Success, 7, vec![token]),
            ],
            results: None,
        }],
        checks: vec![
            ConditionSite {
                site_id: 0,
                text: String::from(r#"input.role == "admin""#),
                kind: ConditionKind::Comparison,
                location: Some(location(4, 5)),
                operator: Some(Operator::Eq),
            },
            ConditionSite {
                site_id: 1,
                text: String::from("input.user.token == data.tokens[input.user.name]"),
                kind: ConditionKind::Comparison,
                location: Some(location(8, 5)),
                operator: Some(Operator::Eq),
            },
        ],
    }
}

/// `deny contains name if { some name in input.users; ... }` that emitted
/// `"bob"` after a loop over two users.
pub fn partial_set_report() -> ExplanationReport {
    let names: BTreeSet<Value> = [Value::from("bob")].into_iter().collect();
    let in_users = ConditionExplanation {
        site_id: 0,
        owner: owner("data.test.deny", 0),
        outcome: Outcome::Success,
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
        query: query("data.test.deny"),
        query_result: Value::from(names.clone()),
        rules: vec![RuleExplanation {
            name: String::from("data.test.deny"),
            call_instance: 0,
            kind: RuleKind::PartialSet,
            outcome: RuleOutcome::Matched,
            result: ReportedValue::Known(Value::from(names)),
            emissions: vec![emission(None, Value::from("bob"), vec![in_users.clone()])],
            definitions: vec![definition(0, 0, Outcome::Success, 3, vec![in_users])],
            results: None,
        }],
        checks: vec![ConditionSite {
            site_id: 0,
            text: String::from("some name in input.users"),
            kind: ConditionKind::Iteration,
            location: None,
            operator: None,
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
        site_id: 0,
        owner: owner("data.test.labels", 0),
        outcome: Outcome::Success,
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
        query: query("data.test.labels"),
        query_result: labels.clone(),
        rules: vec![RuleExplanation {
            name: String::from("data.test.labels"),
            call_instance: 0,
            kind: RuleKind::PartialObject,
            outcome: RuleOutcome::Matched,
            result: ReportedValue::Known(labels),
            emissions: vec![emission(
                Some(Value::from("env")),
                Value::from("prod"),
                vec![in_tags.clone()],
            )],
            definitions: vec![definition(0, 0, Outcome::Success, 3, vec![in_tags])],
            results: None,
        }],
        checks: vec![ConditionSite {
            site_id: 0,
            text: String::from("some k, v in input.tags"),
            kind: ConditionKind::Iteration,
            location: Some(location(4, 5)),
            operator: None,
        }],
    }
}

/// Per-result attribution of
///
/// ```rego
/// deny contains "public" if {
///     some r in input.resources
///     some t in r.tags
///     t == "public"
/// }
/// ```
///
/// over two resources whose tags are each `["public"]`. Both derivations
/// produce `"public"`; a proof budget of one keeps the first. The inner loop
/// iterates two different collections, so its elements at index 0 are
/// counted separately per collection rather than merged. The outer
/// iteration value of the retained proof was elided; definitions and
/// emissions are omitted for brevity.
pub fn attributed_report() -> ExplanationReport {
    let public: BTreeSet<Value> = [Value::from("public")].into_iter().collect();
    let distinct = |site_id, loop_name: &str, collection, count| DistinctElements {
        site_id,
        loop_name: String::from(loop_name),
        collection,
        count: Some(Count::Exact(count)),
    };
    let proof = Derivation {
        definition: 0,
        body: 0,
        conditions: vec![ConditionExplanation {
            site_id: 2,
            owner: owner("data.test.deny", 0),
            outcome: Outcome::Success,
            left: Some(known(Value::from("public"), Some("t"))),
            right: Some(known(Value::from("public"), None)),
            witness: None,
            binding: None,
        }],
        bindings: vec![
            IterationBinding {
                site_id: 0,
                collection: 0,
                key: ReportedValue::Known(Value::from(0_u64)),
                value: ReportedValue::Elided,
            },
            IterationBinding {
                site_id: 1,
                collection: 1,
                key: ReportedValue::Known(Value::from(0_u64)),
                value: ReportedValue::Known(Value::from("public")),
            },
        ],
    };
    let result = ResultExplanation {
        key: None,
        value: ReportedValue::Known(Value::from("public")),
        derivations_total: Count::Exact(2),
        distinct_elements: vec![
            distinct(0, "input.resources[_]", 0, 2),
            distinct(1, "r.tags[_]", 1, 1),
            distinct(1, "r.tags[_]", 2, 1),
        ],
        proofs: vec![proof],
    };
    let iteration = |site_id, text: &str| ConditionSite {
        site_id,
        text: String::from(text),
        kind: ConditionKind::Iteration,
        location: None,
        operator: None,
    };
    ExplanationReport {
        query: query("data.test.deny"),
        query_result: Value::from(public.clone()),
        rules: vec![RuleExplanation {
            name: String::from("data.test.deny"),
            call_instance: 0,
            kind: RuleKind::PartialSet,
            outcome: RuleOutcome::Matched,
            result: ReportedValue::Known(Value::from(public)),
            emissions: Vec::new(),
            definitions: Vec::new(),
            results: Some(vec![result]),
        }],
        checks: vec![
            iteration(0, "some r in input.resources"),
            iteration(1, "some t in r.tags"),
            ConditionSite {
                site_id: 2,
                text: String::from(r#"t == "public""#),
                kind: ConditionKind::Comparison,
                location: None,
                operator: Some(Operator::Eq),
            },
        ],
    }
}

/// `allow := true if input.x` and `allow := false if input.y` with both
/// `input.x` and `input.y` true, queried with `with input.y as true`. The
/// definitions conflict, so evaluation fails. This report accompanies that
/// error: `query_result` is absent because there is no result, not because
/// it is undefined, and the rule's outcome identifies the conflict.
pub fn conflict_report() -> ExplanationReport {
    let mut target = query("data.test.allow");
    target.with_overrides = true;
    ExplanationReport {
        query: target,
        query_result: Value::Undefined,
        rules: vec![RuleExplanation {
            name: String::from("data.test.allow"),
            call_instance: 0,
            kind: RuleKind::Complete,
            outcome: RuleOutcome::Conflict {
                values: vec![
                    ReportedValue::Known(Value::from(true)),
                    ReportedValue::Known(Value::from(false)),
                ],
            },
            result: ReportedValue::Known(Value::Undefined),
            emissions: Vec::new(),
            definitions: Vec::new(),
            results: None,
        }],
        checks: Vec::new(),
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
        call: None,
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
        call: None,
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
        call: None,
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
                status: ResidualAlternativeStatus::Exact,
                unresolved: None,
            },
            ResidualQuery {
                key: None,
                value: Value::from(true),
                conditions: vec![not_locked],
                status: ResidualAlternativeStatus::Exact,
                unresolved: None,
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
        call: None,
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
        call: None,
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
                status: ResidualAlternativeStatus::Exact,
                unresolved: None,
            },
            ResidualQuery {
                key: None,
                value: Value::from("locked"),
                conditions: vec![locked],
                status: ResidualAlternativeStatus::Exact,
                unresolved: None,
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
                call: None,
                rule: None,
                location: None,
            }],
            status: ResidualAlternativeStatus::Exact,
            unresolved: None,
        }],
        warnings: Vec::new(),
    }
}

/// `allow if startswith(input.name, "svc-")` and
/// `allow if regex.match("^prod-", data.env.name)`, with `input.name` and
/// `data.env.name` unknown.
pub fn partial_eval_builtin_call_result() -> PartialEvalResult {
    fn call(text: &str, name: &str, arguments: Vec<ResidualArgument>) -> ResidualQuery {
        ResidualQuery {
            key: None,
            value: Value::from(true),
            conditions: vec![ResidualCondition {
                text: String::from(text),
                kind: ResidualKind::BuiltinCall,
                operator: None,
                input_path: None,
                value: None,
                negated: Vec::new(),
                call: Some(ResidualCall {
                    name: String::from(name),
                    arguments,
                }),
                rule: None,
                location: None,
            }],
            status: ResidualAlternativeStatus::Exact,
            unresolved: None,
        }
    }
    PartialEvalResult {
        kind: RuleKind::Complete,
        status: ResidualStatus::Exact,
        result: Value::Undefined,
        residual_queries: vec![
            call(
                r#"startswith(input.name, "svc-")"#,
                "startswith",
                vec![
                    ResidualArgument::InputPath(String::from("input.name")),
                    ResidualArgument::Value(Value::from("svc-")),
                ],
            ),
            call(
                r#"regex.match("^prod-", data.env.name)"#,
                "regex.match",
                vec![
                    ResidualArgument::Value(Value::from("^prod-")),
                    ResidualArgument::InputPath(String::from("data.env.name")),
                ],
            ),
        ],
        warnings: Vec::new(),
    }
}

/// `deny contains "public access" if input.properties.publicNetworkAccess ==
/// "Enabled"` and `deny contains sprintf("bad sku %s", [input.sku.name]) if
/// input.sku.tier == "Free"`, with all of `input` unknown. The second
/// message can't be built, so its alternative is unresolved.
pub fn partial_eval_partial_result() -> PartialEvalResult {
    PartialEvalResult {
        kind: RuleKind::PartialSet,
        status: ResidualStatus::Partial,
        result: Value::Undefined,
        residual_queries: vec![
            ResidualQuery {
                key: None,
                value: Value::from("public access"),
                conditions: vec![residual_equals(
                    "input.properties.publicNetworkAccess",
                    "Enabled",
                )],
                status: ResidualAlternativeStatus::Exact,
                unresolved: None,
            },
            ResidualQuery {
                key: None,
                value: Value::Undefined,
                conditions: vec![residual_equals("input.sku.tier", "Free")],
                status: ResidualAlternativeStatus::Unresolved,
                unresolved: Some(ResidualUnresolved {
                    reason: ResidualUnresolvedReason::UnknownValue,
                    detail: Some(String::from(
                        r#"sprintf("bad sku %s", [input.sku.name]) depends on unknown input"#,
                    )),
                }),
            },
        ],
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

/// `ports := {80, 443} if input.public`: the residual value is a set, which
/// JSON can't distinguish from an array, so the whole result is
/// unsupported.
pub fn partial_eval_unsupported_result() -> PartialEvalResult {
    PartialEvalResult {
        kind: RuleKind::Complete,
        status: ResidualStatus::Unsupported,
        result: Value::Undefined,
        residual_queries: Vec::new(),
        warnings: vec![String::from(
            "data.test.ports: the value is a set, which JSON can't distinguish from an array",
        )],
    }
}

pub fn known(value: Value, path: Option<&str>) -> Operand {
    Operand {
        value: ReportedValue::Known(value),
        path: path.map(String::from),
        concrete_path: ConcretePath::NotCaptured,
    }
}

pub fn redacted(path: &str) -> Operand {
    Operand {
        value: ReportedValue::Redacted,
        path: Some(String::from(path)),
        concrete_path: ConcretePath::NotCaptured,
    }
}

/// A query naming `rule`, whose top-level evaluation is call instance 0.
pub fn query(rule: &str) -> QueryTarget {
    QueryTarget {
        entry_point: String::from(rule),
        rule: Some(String::from(rule)),
        call_instance: Some(0),
        with_overrides: false,
    }
}

pub fn owner(rule: &str, call_instance: u64) -> ConditionOwner {
    ConditionOwner {
        rule: String::from(rule),
        call_instance,
    }
}

/// Contract fixture for a collection whose nested set loses its type in
/// JSON: `input.x in [{1, 2}]` cannot be applied exactly by a JSON consumer.
/// A future producer must detect this recursively before creating residuals.
pub fn partial_eval_nested_collection_unsupported() -> PartialEvalResult {
    PartialEvalResult {
        kind: RuleKind::Complete,
        status: ResidualStatus::Unsupported,
        result: Value::Undefined,
        residual_queries: Vec::new(),
        warnings: vec![String::from(
            "input.x in [{1, 2}]: nested set is not JSON-lossless",
        )],
    }
}

/// `labels` with alternatives on mutually exclusive values of `input.mode`,
/// so none can hold together and an unresolved key can't conflict:
///
/// ```rego
/// labels["a"] := 1 if input.mode == "a"
/// labels[input.name] := 2 if input.mode == "b"
/// labels["c"] := 3 if { input.mode == "c"; glob.match("*.x", [], input.host) }
/// labels["d"] := 4 if { input.mode == "d"; every p in input.ports { p > 0 } }
/// ```
pub fn partial_eval_partial_object_result() -> PartialEvalResult {
    fn unresolved(
        key: Option<&str>,
        value: i64,
        mode: &str,
        reason: ResidualUnresolvedReason,
        detail: Option<&str>,
    ) -> ResidualQuery {
        ResidualQuery {
            key: key.map(Value::from),
            value: Value::from(value),
            conditions: vec![residual_equals("input.mode", mode)],
            status: ResidualAlternativeStatus::Unresolved,
            unresolved: Some(ResidualUnresolved {
                reason,
                detail: detail.map(String::from),
            }),
        }
    }
    PartialEvalResult {
        kind: RuleKind::PartialObject,
        status: ResidualStatus::Partial,
        result: Value::Undefined,
        residual_queries: vec![
            ResidualQuery {
                key: Some(Value::from("a")),
                value: Value::from(1),
                conditions: vec![residual_equals("input.mode", "a")],
                status: ResidualAlternativeStatus::Exact,
                unresolved: None,
            },
            unresolved(
                None,
                2,
                "b",
                ResidualUnresolvedReason::TaintedKey,
                Some("the key input.name is unknown"),
            ),
            unresolved(
                Some("c"),
                3,
                "c",
                ResidualUnresolvedReason::UnsupportedBuiltin,
                Some("glob.match"),
            ),
            unresolved(
                Some("d"),
                4,
                "d",
                ResidualUnresolvedReason::UnsupportedConstruct,
                None,
            ),
        ],
        warnings: Vec::new(),
    }
}

/// `path == "value"`, as a residual condition with no rule or location.
fn residual_equals(path: &str, value: &str) -> ResidualCondition {
    ResidualCondition {
        text: format!(r#"{path} == "{value}""#),
        kind: ResidualKind::ConditionHolds,
        operator: Some(Operator::Eq),
        input_path: Some(String::from(path)),
        value: Some(Value::from(value)),
        negated: Vec::new(),
        call: None,
        rule: None,
        location: None,
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
