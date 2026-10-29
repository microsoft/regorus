// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::fixtures::{
    complete_rule_report, known, partial_eval_conflict_result, partial_eval_object_result,
    partial_eval_result, partial_eval_set_result, partial_eval_unsupported_result,
    partial_object_report, partial_set_report, redacted,
};
use super::*;
use crate::rvm::program::RuleType;
use crate::rvm::vm::VmError;
use crate::value::Value;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

#[test]
fn complete_rule_report_json() -> Result<(), serde_json::Error> {
    let expected = concat!(
        r#"{"query_result":true,"rules":[{"name":"data.test.allow","kind":"complete","result":true,"#,
        r#""definitions":["#,
        r#"{"index":0,"body":0,"outcome":"failure","location":{"file":"test.rego","line":3,"column":1},"#,
        r#""conditions":[{"text":"input.role == \"admin\"","outcome":"failure","kind":"comparison","#,
        r#""location":{"file":"test.rego","line":4,"column":5},"operator":"==","#,
        r#""left":{"path":"input.role","value":"guest"},"#,
        r#""right":{"value":"admin"}}]},"#,
        r#"{"index":1,"body":1,"outcome":"success","location":{"file":"test.rego","line":7,"column":1},"#,
        r#""conditions":[{"text":"input.user.token == data.tokens[input.user.name]","#,
        r#""outcome":"success","kind":"comparison","#,
        r#""location":{"file":"test.rego","line":8,"column":5},"operator":"==","#,
        r#""left":{"path":"input.user.token","redacted":true},"#,
        r#""right":{"path":"data.tokens[input.user.name]","redacted":true}}]}]}]}"#,
    );
    assert_eq!(serde_json::to_string(&complete_rule_report())?, expected);
    Ok(())
}

#[test]
fn partial_set_report_json() -> Result<(), serde_json::Error> {
    let condition = concat!(
        r#"{"text":"some name in input.users","outcome":"success","kind":"iteration","#,
        r#""witness":{"iterations":2,"successes":1,"#,
        r#""sample_key":{"value":1},"#,
        r#""sample_value":{"path":"input.users","value":"bob"}},"#,
        r#""binding":"name"}"#,
    );
    let expected = [
        r#"{"query_result":["bob"],"rules":[{"name":"data.test.deny","kind":"partial_set","#,
        r#""result":["bob"],"emissions":[{"index":0,"definition":0,"value":"bob","#,
        r#""conditions":["#,
        condition,
        r#"]}],"definitions":[{"index":0,"body":0,"outcome":"success","#,
        r#""location":{"file":"test.rego","line":3,"column":1},"conditions":["#,
        condition,
        r#"]}]}]}"#,
    ]
    .concat();
    assert_eq!(serde_json::to_string(&partial_set_report())?, expected);
    Ok(())
}

#[test]
fn partial_object_report_json() -> Result<(), serde_json::Error> {
    let condition = concat!(
        r#"{"text":"some k, v in input.tags","outcome":"success","kind":"iteration","#,
        r#""location":{"file":"test.rego","line":4,"column":5},"#,
        r#""witness":{"iterations":1,"successes":1,"sample_key":{"value":"env"},"#,
        r#""sample_value":{"path":"input.tags","value":"prod"}}}"#,
    );
    let expected = [
        r#"{"query_result":{"env":"prod"},"rules":[{"name":"data.test.labels","#,
        r#""kind":"partial_object","result":{"env":"prod"},"#,
        r#""emissions":[{"index":0,"definition":0,"key":"env","value":"prod","conditions":["#,
        condition,
        r#"]}],"definitions":[{"index":0,"body":0,"outcome":"success","#,
        r#""location":{"file":"test.rego","line":3,"column":1},"conditions":["#,
        condition,
        r#"]}]}]}"#,
    ]
    .concat();
    assert_eq!(serde_json::to_string(&partial_object_report())?, expected);
    Ok(())
}

#[test]
fn partial_eval_result_json() -> Result<(), serde_json::Error> {
    let expected = concat!(
        r#"{"kind":"complete","status":"exact","residual_queries":["#,
        r#"{"value":true,"conditions":[{"text":"input.role == \"admin\"","kind":"condition_holds","#,
        r#""operator":"==","input_path":"input.role","value":"admin","rule":"data.test.allow","#,
        r#""location":{"file":"test.rego","line":3,"column":5}}]},"#,
        r#"{"value":true,"conditions":[{"text":"not input.locked","kind":"negation_holds","#,
        r#""negated":[{"text":"input.locked","kind":"truthy","input_path":"input.locked"}],"#,
        r#""rule":"data.test.allow"}]}]}"#,
    );
    assert_eq!(serde_json::to_string(&partial_eval_result())?, expected);
    Ok(())
}

#[test]
fn partial_eval_set_result_json() -> Result<(), serde_json::Error> {
    let expected = concat!(
        r#"{"kind":"partial_set","status":"exact","residual_queries":["#,
        r#"{"value":"admin","conditions":[{"text":"input.role == \"admin\"","#,
        r#""kind":"condition_holds","operator":"==","input_path":"input.role","value":"admin"}]},"#,
        r#"{"value":"locked","conditions":[{"text":"input.locked","kind":"truthy","#,
        r#""input_path":"input.locked"}]}]}"#,
    );
    assert_eq!(serde_json::to_string(&partial_eval_set_result())?, expected);
    Ok(())
}

#[test]
fn partial_eval_object_result_json() -> Result<(), serde_json::Error> {
    let expected = concat!(
        r#"{"kind":"partial_object","status":"exact","residual_queries":["#,
        r#"{"key":"env","value":"prod","conditions":[{"text":"input.env == \"prod\"","#,
        r#""kind":"condition_holds","operator":"==","input_path":"input.env","value":"prod"}]}]}"#,
    );
    assert_eq!(
        serde_json::to_string(&partial_eval_object_result())?,
        expected
    );
    Ok(())
}

/// Independent definitions that may conflict give no alternatives and a
/// status that consumers must not treat as exact.
#[test]
fn partial_eval_conflict_result_json_fails_closed() -> Result<(), serde_json::Error> {
    assert_eq!(
        serde_json::to_string(&partial_eval_conflict_result())?,
        concat!(
            r#"{"kind":"complete","status":"possible_conflict","residual_queries":[],"#,
            r#""warnings":["data.test.allow: definitions with different values may both hold"]}"#,
        )
    );
    Ok(())
}

#[test]
fn partial_eval_unsupported_result_json() -> Result<(), serde_json::Error> {
    assert_eq!(
        serde_json::to_string(&partial_eval_unsupported_result())?,
        concat!(
            r#"{"kind":"complete","status":"unsupported","residual_queries":[],"#,
            r#""warnings":["data.test.msg: the value depends on unknown input"]}"#,
        )
    );
    Ok(())
}

/// A result that is not exact carries nothing a consumer could apply.
#[test]
fn inexact_partial_eval_results_have_no_outcome() {
    for result in [
        partial_eval_conflict_result(),
        partial_eval_unsupported_result(),
    ] {
        assert_ne!(result.status, ResidualStatus::Exact);
        assert_eq!(result.result, Value::Undefined);
        assert!(result.residual_queries.is_empty());
        assert!(!result.warnings.is_empty());
    }
}

/// `p := true if input.enabled` and `p contains true if input.enabled` have
/// the same alternatives, so only `kind` tells consumers whether the result
/// is `true` or `{true}`, and undefined or an empty set. Partial object
/// alternatives also have a key; see `partial_eval_object_result_json`.
#[test]
fn partial_eval_kind_distinguishes_identical_residuals() -> Result<(), serde_json::Error> {
    let residuals = serde_json::to_value(&partial_eval_result().residual_queries)?;
    let mut seen: Vec<serde_json::Value> = Vec::new();
    for (kind, name) in [
        (RuleKind::Complete, "complete"),
        (RuleKind::PartialSet, "partial_set"),
        (RuleKind::Function, "function"),
    ] {
        let mut result = partial_eval_result();
        result.kind = kind;
        let json = serde_json::to_value(&result)?;
        assert_eq!(json.get("kind"), Some(&serde_json::json!(name)));
        assert_eq!(json.get("residual_queries"), Some(&residuals));
        assert!(!seen.contains(&json), "{name} serializes like another kind");
        seen.push(json);
    }
    Ok(())
}

/// With no alternatives, an exact result still says how to read the empty
/// outcome: undefined, an empty set or an empty object.
#[test]
fn exact_empty_partial_eval_result_keeps_kind_and_status() -> Result<(), serde_json::Error> {
    for (kind, name) in [
        (RuleKind::Complete, "complete"),
        (RuleKind::PartialSet, "partial_set"),
        (RuleKind::PartialObject, "partial_object"),
        (RuleKind::Function, "function"),
    ] {
        let mut result = partial_eval_result();
        result.kind = kind;
        result.residual_queries.clear();
        assert_eq!(
            serde_json::to_string(&result)?,
            [
                r#"{"kind":""#,
                name,
                r#"","status":"exact","residual_queries":[]}"#
            ]
            .concat()
        );
    }
    Ok(())
}

#[test]
fn operand_json_for_known_undefined_and_redacted_values() -> Result<(), serde_json::Error> {
    let json = |operand: &Operand| serde_json::to_string(operand);
    assert_eq!(
        json(&known(Value::from(false), Some("input.ok")))?,
        r#"{"path":"input.ok","value":false}"#
    );
    assert_eq!(json(&known(Value::Null, None))?, r#"{"value":null}"#);
    assert_eq!(
        json(&known(Value::Undefined, Some("input.missing")))?,
        r#"{"path":"input.missing"}"#
    );
    assert_eq!(
        json(&redacted("input.password"))?,
        r#"{"path":"input.password","redacted":true}"#
    );
    Ok(())
}

/// `labels` as a dependency of a query that returned `true`, with its
/// values redacted.
#[test]
fn redacted_rule_result_and_emission_json() -> Result<(), serde_json::Error> {
    let mut report = partial_object_report();
    report.query_result = Value::from(true);
    let rule = report.rules.first_mut();
    assert!(rule.is_some());
    if let Some(rule) = rule {
        rule.result = ReportedValue::Redacted;
        rule.definitions.clear();
        for emission in &mut rule.emissions {
            emission.key = Some(ReportedValue::Redacted);
            emission.value = ReportedValue::Redacted;
            emission.conditions.clear();
        }
    }
    assert_eq!(
        serde_json::to_string(&report)?,
        concat!(
            r#"{"query_result":true,"rules":[{"name":"data.test.labels","#,
            r#""kind":"partial_object","result_redacted":true,"emissions":[{"index":0,"#,
            r#""definition":0,"key_redacted":true,"value_redacted":true,"conditions":[]}]}]}"#,
        )
    );
    Ok(())
}

/// The `match` is exhaustive, so adding a variant fails to compile until its
/// serialization is tested.
#[test]
fn every_reported_value_variant_has_a_json_form() -> Result<(), serde_json::Error> {
    for value in [
        ReportedValue::Known(Value::from(1_u64)),
        ReportedValue::Redacted,
    ] {
        let operand = Operand {
            value: value.clone(),
            path: None,
        };
        let expected = match value {
            ReportedValue::Known(_) => r#"{"value":1}"#,
            ReportedValue::Redacted => r#"{"redacted":true}"#,
        };
        assert_eq!(serde_json::to_string(&operand)?, expected);
    }
    Ok(())
}

/// Undefined, `false`, `null` and the string `"<undefined>"` must serialize
/// differently in every position that holds a runtime value.
#[test]
fn undefined_is_distinct_in_every_value_position() -> Result<(), serde_json::Error> {
    type Setter = fn(&mut ExplanationReport, &mut PartialEvalResult, Value) -> Option<()>;
    fn rule(r: &mut ExplanationReport) -> Option<&mut RuleExplanation> {
        r.rules.first_mut()
    }
    fn emission(r: &mut ExplanationReport) -> Option<&mut EmissionExplanation> {
        rule(r)?.emissions.first_mut()
    }
    fn condition(r: &mut ExplanationReport) -> Option<&mut ConditionExplanation> {
        rule(r)?.definitions.first_mut()?.conditions.first_mut()
    }
    fn residual(p: &mut PartialEvalResult) -> Option<&mut ResidualQuery> {
        p.residual_queries.first_mut()
    }
    let positions: [(&str, Setter); 10] = [
        ("query_result", |r, _, v| {
            r.query_result = v;
            Some(())
        }),
        ("rule result", |r, _, v| {
            rule(r)?.result = ReportedValue::Known(v);
            Some(())
        }),
        ("emission value", |r, _, v| {
            emission(r)?.value = ReportedValue::Known(v);
            Some(())
        }),
        ("emission key", |r, _, v| {
            emission(r)?.key = Some(ReportedValue::Known(v));
            Some(())
        }),
        ("operand", |r, _, v| {
            condition(r)?.left = Some(known(v, None));
            Some(())
        }),
        ("loop sample", |r, _, v| {
            condition(r)?.witness.as_mut()?.sample_value = Some(known(v, None));
            Some(())
        }),
        ("partial eval result", |_, p, v| {
            p.result = v;
            Some(())
        }),
        ("residual query value", |_, p, v| {
            residual(p)?.value = v;
            Some(())
        }),
        ("residual query key", |_, p, v| {
            residual(p)?.key = Some(v);
            Some(())
        }),
        ("residual condition value", |_, p, v| {
            residual(p)?.conditions.first_mut()?.value = Some(v);
            Some(())
        }),
    ];
    for (name, set) in positions {
        let mut seen: Vec<String> = Vec::new();
        for value in [
            Value::Undefined,
            Value::from(false),
            Value::Null,
            Value::from("<undefined>"),
        ] {
            let mut report = partial_set_report();
            let mut partial = partial_eval_result();
            assert!(set(&mut report, &mut partial, value).is_some(), "{name}");
            let json = serde_json::to_string(&report)? + &serde_json::to_string(&partial)?;
            assert!(
                !seen.contains(&json),
                "{name}: two values serialize alike: {json}"
            );
            seen.push(json);
        }
    }
    Ok(())
}

/// The `match`es are exhaustive, so adding a variant fails to compile until
/// its name is checked here.
#[test]
fn every_enum_variant_serializes_to_its_documented_name() -> Result<(), serde_json::Error> {
    fn check<T: serde::Serialize + Copy>(
        values: &[T],
        name: fn(T) -> &'static str,
    ) -> Result<(), serde_json::Error> {
        for &value in values {
            assert_eq!(serde_json::to_value(value)?, serde_json::json!(name(value)));
        }
        Ok(())
    }
    use ConditionKind as C;
    use Outcome as O;
    use ResidualKind as R;
    use ResidualStatus as S;
    check(
        &[
            RuleKind::Complete,
            RuleKind::PartialSet,
            RuleKind::PartialObject,
            RuleKind::Function,
        ],
        |kind| match kind {
            RuleKind::Complete => "complete",
            RuleKind::PartialSet => "partial_set",
            RuleKind::PartialObject => "partial_object",
            RuleKind::Function => "function",
        },
    )?;
    check(
        &[O::Success, O::Failure, O::Undefined, O::Assumed],
        |outcome| match outcome {
            O::Success => "success",
            O::Failure => "failure",
            O::Undefined => "undefined",
            O::Assumed => "assumed",
        },
    )?;
    check(
        &[
            C::Comparison,
            C::Membership,
            C::Iteration,
            C::Truthiness,
            C::Existence,
            C::Negation,
            C::Binding,
        ],
        |kind| match kind {
            C::Comparison => "comparison",
            C::Membership => "membership",
            C::Iteration => "iteration",
            C::Truthiness => "truthiness",
            C::Existence => "existence",
            C::Negation => "negation",
            C::Binding => "binding",
        },
    )?;
    check(
        &[
            R::Exists,
            R::Truthy,
            R::ConditionHolds,
            R::CollectionExists,
            R::NegationHolds,
        ],
        |kind| match kind {
            R::Exists => "exists",
            R::Truthy => "truthy",
            R::ConditionHolds => "condition_holds",
            R::CollectionExists => "collection_exists",
            R::NegationHolds => "negation_holds",
        },
    )?;
    check(
        &[S::Exact, S::PossibleConflict, S::Unsupported],
        |status| match status {
            S::Exact => "exact",
            S::PossibleConflict => "possible_conflict",
            S::Unsupported => "unsupported",
        },
    )?;
    Ok(())
}

#[test]
fn operator_serializes_and_displays_as_rego_syntax() -> Result<(), serde_json::Error> {
    let operators = [
        (Operator::Eq, "=="),
        (Operator::Ne, "!="),
        (Operator::Lt, "<"),
        (Operator::Le, "<="),
        (Operator::Gt, ">"),
        (Operator::Ge, ">="),
        (Operator::In, "in"),
    ];
    for (operator, text) in operators {
        assert_eq!(operator.to_string(), text);
        assert_eq!(serde_json::to_value(operator)?, serde_json::json!(text));
    }
    Ok(())
}

#[test]
fn rule_kind_from_rule_type() {
    assert_eq!(RuleKind::from(RuleType::Complete), RuleKind::Complete);
    assert_eq!(RuleKind::from(RuleType::PartialSet), RuleKind::PartialSet);
    assert_eq!(
        RuleKind::from(RuleType::PartialObject),
        RuleKind::PartialObject
    );
}

#[test]
fn default_settings_redact_and_report_everything() {
    let settings = ExplanationSettings::default();
    assert_eq!(settings.value_mode, ValueMode::Redacted);
    assert_eq!(settings.condition_mode, ConditionMode::PrimaryOnly);
    assert_eq!(settings.scope, ExplanationScope::All);
}

#[test]
fn error_messages() {
    assert_eq!(
        ExplainError::NotEnabled.to_string(),
        "explanations were not enabled for this evaluation"
    );
    let out_of_range = ExplainError::EmissionIndexOutOfRange {
        rule: "data.test.deny".to_string(),
        index: 3,
        available: 1,
    };
    assert_eq!(
        out_of_range.to_string(),
        "emission index 3 is out of range for rule `data.test.deny` (1 emissions)"
    );

    let vm_error = VmError::LiteralIndexOutOfBounds { index: 7, pc: 2 };
    let message = vm_error.to_string();
    let wrapped = ExplainError::from(vm_error.clone());
    assert_eq!(wrapped, ExplainError::Vm(vm_error));
    assert_eq!(wrapped.to_string(), message);
    assert_eq!(message, "Literal index 7 out of bounds (pc=2)");
}
