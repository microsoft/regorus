// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use super::fixtures::{
    attributed_report, complete_rule_report, conflict_report, known,
    partial_eval_builtin_call_result, partial_eval_conflict_result, partial_eval_object_result,
    partial_eval_partial_object_result, partial_eval_partial_result, partial_eval_result,
    partial_eval_set_result, partial_eval_unsupported_result, partial_object_report,
    partial_set_report, redacted,
};
use super::*;
use crate::rvm::program::RuleType;
use crate::rvm::vm::VmError;
use crate::value::Value;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec;
use alloc::vec::Vec;
use anyhow::Context as _;

#[test]
fn complete_rule_report_json() -> Result<(), serde_json::Error> {
    let expected = concat!(
        r#"{"schema_version":2,"query":{"entry_point":"data.test.allow","rule":"data.test.allow","call_instance":0,"with_overrides":false},"#,
        r#""query_result":true,"rules":[{"name":"data.test.allow","call_instance":0,"kind":"complete","#,
        r#""outcome":{"status":"matched"},"result":true,"#,
        r#""definitions":["#,
        r#"{"index":0,"body":0,"outcome":"failure","location":{"file":"test.rego","line":3,"column":1},"#,
        r#""conditions":[{"site_id":0,"owner":{"rule":"data.test.allow","call_instance":0},"outcome":"failure","#,
        r#""left":{"path":"input.role","concrete_path":{"status":"not_captured"},"value":"guest"},"#,
        r#""right":{"concrete_path":{"status":"not_captured"},"value":"admin"}}]},"#,
        r#"{"index":1,"body":1,"outcome":"success","location":{"file":"test.rego","line":7,"column":1},"#,
        r#""conditions":[{"site_id":1,"owner":{"rule":"data.test.allow","call_instance":0},"outcome":"success","#,
        r#""left":{"path":"input.user.token","concrete_path":{"status":"not_captured"},"redacted":true},"#,
        r#""right":{"path":"data.tokens[input.user.name]","concrete_path":{"status":"not_captured"},"redacted":true}}]}]}],"#,
        r#""checks":[{"site_id":0,"text":"input.role == \"admin\"","kind":"comparison","#,
        r#""location":{"file":"test.rego","line":4,"column":5},"operator":"=="},{"site_id":1,"#,
        r#""text":"input.user.token == data.tokens[input.user.name]","kind":"comparison","#,
        r#""location":{"file":"test.rego","line":8,"column":5},"operator":"=="}]}"#,
    );
    assert_eq!(serde_json::to_string(&complete_rule_report())?, expected);
    Ok(())
}

#[test]
fn partial_set_report_json() -> Result<(), serde_json::Error> {
    let condition = concat!(
        r#"{"site_id":0,"owner":{"rule":"data.test.deny","call_instance":0},"outcome":"success","#,
        r#""witness":{"iterations":2,"successes":1,"#,
        r#""sample_key":{"concrete_path":{"status":"not_captured"},"value":1},"#,
        r#""sample_value":{"path":"input.users","concrete_path":{"status":"not_captured"},"value":"bob"}},"#,
        r#""binding":"name"}"#,
    );
    let expected = [
        r#"{"schema_version":2,"query":{"entry_point":"data.test.deny","rule":"data.test.deny","call_instance":0,"with_overrides":false},"#,
        r#""query_result":["bob"],"rules":[{"name":"data.test.deny","call_instance":0,"kind":"partial_set","#,
        r#""outcome":{"status":"matched"},"result":["bob"],"emissions":[{"index":0,"definition":0,"value":"bob","#,
        r#""conditions":["#,
        condition,
        r#"]}],"definitions":[{"index":0,"body":0,"outcome":"success","#,
        r#""location":{"file":"test.rego","line":3,"column":1},"conditions":["#,
        condition,
        r#"]}]}],"checks":[{"site_id":0,"text":"some name in input.users","kind":"iteration"}]}"#,
    ]
    .concat();
    assert_eq!(serde_json::to_string(&partial_set_report())?, expected);
    Ok(())
}

#[test]
fn partial_object_report_json() -> Result<(), serde_json::Error> {
    let condition = concat!(
        r#"{"site_id":0,"owner":{"rule":"data.test.labels","call_instance":0},"outcome":"success","#,
        r#""witness":{"iterations":1,"successes":1,"sample_key":{"concrete_path":{"status":"not_captured"},"value":"env"},"#,
        r#""sample_value":{"path":"input.tags","concrete_path":{"status":"not_captured"},"value":"prod"}}}"#,
    );
    let expected = [
        r#"{"schema_version":2,"query":{"entry_point":"data.test.labels","rule":"data.test.labels","call_instance":0,"with_overrides":false},"#,
        r#""query_result":{"env":"prod"},"rules":[{"name":"data.test.labels","#,
        r#""call_instance":0,"kind":"partial_object","outcome":{"status":"matched"},"result":{"env":"prod"},"#,
        r#""emissions":[{"index":0,"definition":0,"key":"env","value":"prod","conditions":["#,
        condition,
        r#"]}],"definitions":[{"index":0,"body":0,"outcome":"success","#,
        r#""location":{"file":"test.rego","line":3,"column":1},"conditions":["#,
        condition,
        r#"]}]}],"checks":[{"site_id":0,"text":"some k, v in input.tags","kind":"iteration","#,
        r#""location":{"file":"test.rego","line":4,"column":5}}]}"#,
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
            r#""warnings":["data.test.ports: the value is a set, which JSON can't distinguish from an array"]}"#,
        )
    );
    Ok(())
}

#[test]
fn partial_eval_builtin_call_result_json() -> Result<(), serde_json::Error> {
    let expected = concat!(
        r#"{"kind":"complete","status":"exact","residual_queries":["#,
        r#"{"value":true,"conditions":[{"text":"startswith(input.name, \"svc-\")","kind":"builtin_call","#,
        r#""call":{"name":"startswith","arguments":[{"input_path":"input.name"},{"value":"svc-"}]}}]},"#,
        r#"{"value":true,"conditions":[{"text":"regex.match(\"^prod-\", data.env.name)","kind":"builtin_call","#,
        r#""call":{"name":"regex.match","arguments":[{"value":"^prod-"},{"input_path":"data.env.name"}]}}]}]}"#,
    );
    assert_eq!(
        serde_json::to_string(&partial_eval_builtin_call_result())?,
        expected
    );
    Ok(())
}

/// A known call argument is always a string: any other value, including an
/// undefined one at any depth, fails to serialize.
#[test]
fn non_string_residual_call_argument_fails_to_serialize() -> Result<(), serde_json::Error> {
    let string = Value::from("svc-");
    for value in [
        Value::Undefined,
        Value::Null,
        Value::from(true),
        Value::from(1),
        Value::from(vec![string.clone()]),
        Value::from(vec![Value::Undefined]),
        Value::from(BTreeSet::from([string.clone()])),
        Value::from(BTreeMap::from([(Value::from("a"), string.clone())])),
    ] {
        let argument = ResidualArgument::Value(value.clone());
        assert_eq!(serde_json::to_string(&argument).ok(), None, "{value:?}");
    }
    assert_eq!(
        serde_json::to_string(&ResidualArgument::Value(string))?,
        r#"{"value":"svc-"}"#
    );
    Ok(())
}

/// An alternative's `unresolved` must be present exactly when its status
/// is unresolved, or serialization fails.
#[test]
fn residual_query_status_mismatch_fails_to_serialize() -> anyhow::Result<()> {
    let result = partial_eval_partial_result();
    let exact = result.residual_queries.first().context("exact")?;
    let unresolved = result.residual_queries.get(1).context("unresolved")?;
    serde_json::to_string(exact)?;
    serde_json::to_string(unresolved)?;

    let mut missing_reason = unresolved.clone();
    missing_reason.unresolved = None;
    assert_eq!(serde_json::to_string(&missing_reason).ok(), None);

    let mut exact_with_reason = exact.clone();
    exact_with_reason.unresolved = unresolved.unresolved.clone();
    assert_eq!(serde_json::to_string(&exact_with_reason).ok(), None);
    Ok(())
}

/// A result is `partial` exactly when an alternative is unresolved, or
/// serialization fails, so an older consumer never sees `exact` with an
/// unresolved alternative.
#[test]
fn partial_eval_status_mismatch_fails_to_serialize() -> Result<(), serde_json::Error> {
    let mut exact_with_unresolved = partial_eval_partial_result();
    exact_with_unresolved.status = ResidualStatus::Exact;
    assert_eq!(serde_json::to_string(&exact_with_unresolved).ok(), None);

    let mut partial_without_unresolved = partial_eval_set_result();
    partial_without_unresolved.status = ResidualStatus::Partial;
    assert_eq!(
        serde_json::to_string(&partial_without_unresolved).ok(),
        None
    );

    serde_json::to_string(&partial_eval_partial_result())?;
    serde_json::to_string(&partial_eval_set_result())?;
    Ok(())
}

/// A result that is neither exact nor partial has no alternatives, or
/// serialization fails.
#[test]
fn inexact_partial_eval_result_with_alternatives_fails_to_serialize() -> anyhow::Result<()> {
    let alternative = partial_eval_set_result()
        .residual_queries
        .first()
        .cloned()
        .context("alternative")?;
    for mut result in [
        partial_eval_conflict_result(),
        partial_eval_unsupported_result(),
    ] {
        serde_json::to_string(&result)?;
        result.residual_queries.push(alternative.clone());
        assert_eq!(serde_json::to_string(&result).ok(), None, "{result:?}");
    }
    Ok(())
}

#[test]
fn partial_eval_partial_result_json() -> anyhow::Result<()> {
    let prefix = concat!(
        r#"{"kind":"partial_set","status":"partial","residual_queries":["#,
        r#"{"value":"public access","conditions":[{"text":"input.properties.publicNetworkAccess == \"Enabled\"","#,
        r#""kind":"condition_holds","operator":"==","input_path":"input.properties.publicNetworkAccess","value":"Enabled"}]},"#,
        r#"{"conditions":[{"text":"input.sku.tier == \"Free\"","#,
        r#""kind":"condition_holds","operator":"==","input_path":"input.sku.tier","value":"Free"}],"#,
        r#""status":"unresolved","unresolved":{"reason":"unknown_value""#,
    );
    let mut result = partial_eval_partial_result();
    assert_eq!(
        serde_json::to_string(&result)?,
        [
            prefix,
            r#","detail":"sprintf(\"bad sku %s\", [input.sku.name]) depends on unknown input"}}]}"#,
        ]
        .concat()
    );
    result
        .residual_queries
        .get_mut(1)
        .and_then(|query| query.unresolved.as_mut())
        .context("unresolved alternative")?
        .detail = None;
    assert_eq!(serde_json::to_string(&result)?, [prefix, "}}]}"].concat());
    Ok(())
}

/// The unresolved alternatives of a partial object omit an unknown key and
/// keep a known one.
#[test]
fn partial_eval_partial_object_result_json() -> anyhow::Result<()> {
    let mode = |value: &str| {
        format!(
            r#"[{{"text":"input.mode == \"{value}\"","kind":"condition_holds","operator":"==","input_path":"input.mode","value":"{value}"}}]"#
        )
    };
    let expected = [
        r#"{"kind":"partial_object","status":"partial","residual_queries":["#,
        r#"{"key":"a","value":1,"conditions":"#,
        &mode("a"),
        r#"},{"value":2,"conditions":"#,
        &mode("b"),
        r#","status":"unresolved","unresolved":{"reason":"tainted_key","detail":"the key input.name is unknown"}},"#,
        r#"{"key":"c","value":3,"conditions":"#,
        &mode("c"),
        r#","status":"unresolved","unresolved":{"reason":"unsupported_builtin","detail":"glob.match"}},"#,
        r#"{"key":"d","value":4,"conditions":"#,
        &mode("d"),
        r#","status":"unresolved","unresolved":{"reason":"unsupported_construct"}}]}"#,
    ]
    .concat();
    let result = partial_eval_partial_object_result();
    assert_eq!(serde_json::to_string(&result)?, expected);
    let json = serde_json::to_value(&result)?;
    let tainted = json
        .pointer("/residual_queries/1")
        .and_then(serde_json::Value::as_object)
        .context("tainted-key alternative")?;
    assert!(!tainted.contains_key("key"));
    Ok(())
}

/// The result status is `partial` if and only if an alternative is
/// unresolved, and only unresolved alternatives say why.
#[test]
fn partial_eval_fixtures_keep_alternative_status_invariants() {
    for result in [
        partial_eval_result(),
        partial_eval_set_result(),
        partial_eval_object_result(),
        partial_eval_builtin_call_result(),
        partial_eval_partial_result(),
        partial_eval_partial_object_result(),
        partial_eval_conflict_result(),
        partial_eval_unsupported_result(),
        fixtures::partial_eval_nested_collection_unsupported(),
    ] {
        let unresolved = result
            .residual_queries
            .iter()
            .filter(|query| query.status == ResidualAlternativeStatus::Unresolved)
            .count();
        assert_eq!(result.status == ResidualStatus::Partial, unresolved > 0);
        for query in &result.residual_queries {
            assert_eq!(
                query.status == ResidualAlternativeStatus::Unresolved,
                query.unresolved.is_some()
            );
        }
    }
}

/// A result that is neither exact nor partial carries nothing a consumer
/// could apply.
#[test]
fn inexact_partial_eval_results_have_no_outcome() {
    for result in [
        partial_eval_conflict_result(),
        partial_eval_unsupported_result(),
        fixtures::partial_eval_nested_collection_unsupported(),
    ] {
        assert_ne!(result.status, ResidualStatus::Exact);
        assert_ne!(result.status, ResidualStatus::Partial);
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
        r#"{"path":"input.ok","concrete_path":{"status":"not_captured"},"value":false}"#
    );
    assert_eq!(
        json(&known(Value::Null, None))?,
        r#"{"concrete_path":{"status":"not_captured"},"value":null}"#
    );
    assert_eq!(
        json(&known(Value::Undefined, Some("input.missing")))?,
        r#"{"path":"input.missing","concrete_path":{"status":"not_captured"}}"#
    );
    assert_eq!(
        json(&redacted("input.password"))?,
        r#"{"path":"input.password","concrete_path":{"status":"not_captured"},"redacted":true}"#
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
            r#"{"schema_version":2,"query":{"entry_point":"data.test.labels","rule":"data.test.labels","call_instance":0,"with_overrides":false},"#,
            r#""query_result":true,"rules":[{"name":"data.test.labels","#,
            r#""call_instance":0,"kind":"partial_object","outcome":{"status":"matched"},"#,
            r#""result_redacted":true,"emissions":[{"index":0,"#,
            r#""definition":0,"key_redacted":true,"value_redacted":true,"conditions":[]}]}],"#,
            r#""checks":[{"site_id":0,"text":"some k, v in input.tags","kind":"iteration","#,
            r#""location":{"file":"test.rego","line":4,"column":5}}]}"#,
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
        ReportedValue::Elided,
    ] {
        let operand = Operand {
            call_uses: None,
            value: value.clone(),
            path: None,
            concrete_path: ConcretePath::NotCaptured,
            origins: None,
        };
        let expected = match value {
            ReportedValue::Known(_) => r#"{"concrete_path":{"status":"not_captured"},"value":1}"#,
            ReportedValue::Redacted => {
                r#"{"concrete_path":{"status":"not_captured"},"redacted":true}"#
            }
            ReportedValue::Elided => r#"{"concrete_path":{"status":"not_captured"},"elided":true}"#,
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
    fn binding(r: &mut ExplanationReport) -> Option<&mut IterationBinding> {
        let mut result = result_attribution();
        result.proofs.first_mut()?.bindings = Some(alloc::vec![IterationBinding {
            site_id: 0,
            collection: 0,
            key: ReportedValue::Known(Value::from(0)),
            value: ReportedValue::Known(Value::from(1)),
        }]);
        let rule = rule(r)?;
        rule.results = Some(alloc::vec![result]);
        rule.results
            .as_mut()?
            .first_mut()?
            .proofs
            .first_mut()?
            .bindings
            .as_mut()?
            .first_mut()
    }
    let positions: [(&str, Setter); 12] = [
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
        ("proof binding key", |r, _, v| {
            binding(r)?.key = ReportedValue::Known(v);
            Some(())
        }),
        ("proof binding value", |r, _, v| {
            binding(r)?.value = ReportedValue::Known(v);
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
    use ResidualUnresolvedReason as U;
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
            C::Comprehension,
        ],
        |kind| match kind {
            C::Comparison => "comparison",
            C::Membership => "membership",
            C::Iteration => "iteration",
            C::Truthiness => "truthiness",
            C::Existence => "existence",
            C::Negation => "negation",
            C::Binding => "binding",
            C::Comprehension => "comprehension",
        },
    )?;
    check(
        &[
            R::Exists,
            R::Truthy,
            R::ConditionHolds,
            R::CollectionExists,
            R::NegationHolds,
            R::BuiltinCall,
        ],
        |kind| match kind {
            R::Exists => "exists",
            R::Truthy => "truthy",
            R::ConditionHolds => "condition_holds",
            R::CollectionExists => "collection_exists",
            R::NegationHolds => "negation_holds",
            R::BuiltinCall => "builtin_call",
        },
    )?;
    check(
        &[S::Exact, S::Partial, S::PossibleConflict, S::Unsupported],
        |status| match status {
            S::Exact => "exact",
            S::Partial => "partial",
            S::PossibleConflict => "possible_conflict",
            S::Unsupported => "unsupported",
        },
    )?;
    check(
        &[
            ResidualAlternativeStatus::Exact,
            ResidualAlternativeStatus::Unresolved,
        ],
        |status| match status {
            ResidualAlternativeStatus::Exact => "exact",
            ResidualAlternativeStatus::Unresolved => "unresolved",
        },
    )?;
    check(
        &[
            U::UnknownValue,
            U::TaintedKey,
            U::UnsupportedBuiltin,
            U::UnsupportedConstruct,
        ],
        |reason| match reason {
            U::UnknownValue => "unknown_value",
            U::TaintedKey => "tainted_key",
            U::UnsupportedBuiltin => "unsupported_builtin",
            U::UnsupportedConstruct => "unsupported_construct",
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
    assert!(!settings.capture_paths);
    assert_eq!(settings.max_derivations, 64);
}

#[test]
fn empty_partial_rule_results_are_defined_not_omitted() -> Result<(), serde_json::Error> {
    for (kind, value, expected) in [
        (
            RuleKind::PartialSet,
            Value::new_set(),
            r#"{"name":"data.test.empty","call_instance":0,"kind":"partial_set","outcome":{"status":"no_match"},"result":[]}"#,
        ),
        (
            RuleKind::PartialObject,
            Value::new_object(),
            r#"{"name":"data.test.empty","call_instance":0,"kind":"partial_object","outcome":{"status":"no_match"},"result":{}}"#,
        ),
        (
            RuleKind::Complete,
            Value::Undefined,
            r#"{"name":"data.test.empty","call_instance":0,"kind":"complete","outcome":{"status":"no_match"}}"#,
        ),
        (
            RuleKind::Function,
            Value::Undefined,
            r#"{"name":"data.test.empty","call_instance":0,"kind":"function","outcome":{"status":"no_match"}}"#,
        ),
    ] {
        let rule = RuleExplanation {
            name: String::from("data.test.empty"),
            call_instance: 0,
            kind,
            outcome: RuleOutcome::NoMatch,
            result: ReportedValue::Known(value),
            emissions: Vec::new(),
            definitions: Vec::new(),
            results: None,
            attempts: None,
            scopes: None,
            calls: None,
        };
        assert_eq!(serde_json::to_string(&rule)?, expected);
    }
    Ok(())
}

/// This is a contract fixture, not a residual producer test. The producer
/// must recursively reject nested sets/non-string keys before claiming Exact.
#[test]
fn nested_membership_collection_is_unsupported() -> anyhow::Result<()> {
    let result = fixtures::partial_eval_nested_collection_unsupported();
    assert_eq!(
        serde_json::to_string(&result)?,
        r#"{"kind":"complete","status":"unsupported","residual_queries":[],"warnings":["input.x in [{1, 2}]: nested set is not JSON-lossless"]}"#
    );
    // Its nearest supported counterpart has a set only at the outermost
    // membership container, represented as a JSON array.
    let mut supported = partial_eval_result();
    supported.residual_queries.truncate(1);
    let condition = supported
        .residual_queries
        .first_mut()
        .and_then(|query| query.conditions.first_mut())
        .context("residual condition")?;
    condition.text = String::from("input.x in {1, 2}");
    condition.operator = Some(Operator::In);
    condition.input_path = Some(String::from("input.x"));
    let set: alloc::collections::BTreeSet<Value> =
        [Value::from(1), Value::from(2)].into_iter().collect();
    condition.value = Some(Value::from(set));
    assert!(matches!(condition.value, Some(Value::Set(_))));
    let json = serde_json::to_value(&supported)?;
    assert_eq!(json.get("status"), Some(&serde_json::json!("exact")));
    assert_eq!(
        json.pointer("/residual_queries/0/conditions/0/value"),
        Some(&serde_json::json!([1, 2]))
    );
    Ok(())
}

fn result_attribution() -> ResultExplanation {
    ResultExplanation {
        key: None,
        value: ReportedValue::Known(Value::from("same")),
        conditionality: None,
        derivations_total: Count::Exact(200),
        distinct_elements: alloc::vec![DistinctElements {
            site_id: 0,
            loop_name: String::from("input.resources[_]"),
            collection: 0,
            count: Some(Count::Exact(200)),
        }],
        proofs: alloc::vec![Derivation {
            call_uses: None,
            definition: 0,
            body: 0,
            attempt: None,
            conditionality: None,
            conditions: Vec::new(),
            bindings: None,
        }],
    }
}

#[test]
fn per_result_counts_survive_proof_cap_and_unavailable_is_not_zero() -> anyhow::Result<()> {
    let mut result = result_attribution();
    assert_eq!(
        serde_json::to_string(&result)?,
        concat!(
            r#"{"value":"same","derivations_total":{"exact":200},"derivations_shown":1,"derivations_dropped":{"exact":199},"#,
            r#""distinct_elements":[{"site_id":0,"loop":"input.resources[_]","collection":0,"count":{"exact":200}}],"#,
            r#""proofs":[{"definition":0,"body":0,"conditions":[]}]}"#,
        )
    );
    // A zero proof budget still retains exact derivation/element counts.
    result.proofs.clear();
    let json = serde_json::to_value(&result)?;
    assert_eq!(
        json.get("derivations_total"),
        Some(&serde_json::json!({"exact": 200}))
    );
    assert_eq!(json.get("derivations_shown"), Some(&serde_json::json!(0)));
    assert_eq!(
        json.get("derivations_dropped"),
        Some(&serde_json::json!({"exact": 200}))
    );
    assert_eq!(
        json.pointer("/distinct_elements/0/count"),
        Some(&serde_json::json!({"exact": 200}))
    );
    let mut seen = Vec::new();
    let distinct = result
        .distinct_elements
        .first_mut()
        .context("distinct count")?;
    for count in [
        None,
        Some(Count::Exact(0)),
        Some(Count::Exact(200)),
        Some(Count::AtLeast(200)),
    ] {
        distinct.count = count;
        let count_json = serde_json::to_string(&distinct)?;
        assert!(!seen.contains(&count_json));
        seen.push(count_json);
    }
    assert_eq!(
        seen.first().map(String::as_str),
        Some(r#"{"site_id":0,"loop":"input.resources[_]","collection":0,"count":null}"#)
    );
    assert_eq!(
        seen.get(1).map(String::as_str),
        Some(r#"{"site_id":0,"loop":"input.resources[_]","collection":0,"count":{"exact":0}}"#)
    );
    assert_eq!(
        seen.get(3).map(String::as_str),
        Some(
            r#"{"site_id":0,"loop":"input.resources[_]","collection":0,"count":{"at_least":200}}"#
        )
    );
    Ok(())
}

#[test]
fn proofs_reference_shared_sites_but_keep_helper_call_ownership() -> anyhow::Result<()> {
    let mut report = partial_set_report();
    report.query_result = Value::from(
        [Value::from("same")]
            .into_iter()
            .collect::<alloc::collections::BTreeSet<_>>(),
    );
    let rule = report.rules.first_mut().context("queried rule")?;
    rule.result = ReportedValue::Known(report.query_result.clone());
    let emission = rule.emissions.first_mut().context("emission")?;
    emission.value = ReportedValue::Known(Value::from("same"));
    let mut second_emission = emission.clone();
    second_emission.index = 1;
    rule.emissions.push(second_emission);
    for condition in rule
        .definitions
        .iter_mut()
        .flat_map(|definition| &mut definition.conditions)
        .chain(
            rule.emissions
                .iter_mut()
                .flat_map(|contribution| &mut contribution.conditions),
        )
    {
        if let Some(witness) = condition.witness.as_mut() {
            witness.successes = 2;
            witness.sample_value = Some(known(Value::from(1), Some("input.users")));
        }
    }
    let mut helper = rule.clone();
    helper.name = String::from("data.test.is_public");
    helper.kind = RuleKind::Function;
    helper.result = ReportedValue::Known(Value::from("same"));
    helper.emissions.clear();
    helper.definitions.clear();
    let mut result = result_attribution();
    result.derivations_total = Count::Exact(2);
    result.proofs.clear();
    result.distinct_elements = alloc::vec![DistinctElements {
        site_id: 0,
        loop_name: String::from("input.users[_]"),
        collection: 0,
        count: Some(Count::Exact(2)),
    }];
    let check = rule
        .definitions
        .first()
        .and_then(|definition| definition.conditions.first())
        .context("caller check")?
        .clone();
    report.checks.push(ConditionSite {
        site_id: 1,
        text: String::from("name > 0"),
        kind: ConditionKind::Comparison,
        location: None,
        operator: Some(Operator::Gt),
    });
    for call_instance in [1, 2] {
        let mut condition = check.clone();
        condition.site_id = 1;
        condition.owner = fixtures::owner("data.test.is_public", call_instance);
        condition.left = Some(known(Value::from(call_instance), None));
        condition.right = Some(known(Value::from(0), None));
        condition.witness = None;
        condition.binding = None;
        let proof = Derivation {
            call_uses: None,
            definition: 0,
            body: 0,
            attempt: None,
            conditionality: None,
            conditions: alloc::vec![check.clone(), condition],
            bindings: None,
        };
        result.proofs.push(proof);
        helper.call_instance = call_instance;
        report.rules.push(helper.clone());
    }
    report.rules.first_mut().context("queried rule")?.results = Some(alloc::vec![result]);
    let json = serde_json::to_value(&report)?;
    let proofs = json
        .pointer("/rules/0/results/0/proofs")
        .context("proofs")?;
    assert_eq!(
        proofs.pointer("/0/conditions/1/site_id"),
        Some(&serde_json::json!(1))
    );
    assert_eq!(
        proofs.pointer("/1/conditions/1/site_id"),
        Some(&serde_json::json!(1))
    );
    assert_eq!(
        proofs.pointer("/0/conditions/1/owner/rule"),
        Some(&serde_json::json!("data.test.is_public"))
    );
    assert_eq!(
        proofs.pointer("/0/conditions/1/owner/call_instance"),
        Some(&serde_json::json!(1))
    );
    assert_eq!(
        proofs.pointer("/1/conditions/1/owner/call_instance"),
        Some(&serde_json::json!(2))
    );
    assert_ne!(
        proofs.pointer("/0/conditions/1/left"),
        proofs.pointer("/1/conditions/1/left")
    );
    assert!(proofs.pointer("/0/conditions/1/text").is_none());
    assert_eq!(
        json.get("checks")
            .and_then(serde_json::Value::as_array)
            .map(Vec::len),
        Some(2)
    );
    assert!(json.pointer("/rules/1/results").is_none());
    Ok(())
}

#[test]
fn concrete_path_states_and_typed_segments_are_distinct() -> Result<(), serde_json::Error> {
    let mut operand = known(Value::from(true), Some("input.resources[i]"));
    let not_captured = serde_json::to_value(&operand)?;
    operand.concrete_path = ConcretePath::NoPath;
    let no_path = serde_json::to_value(&operand)?;
    operand.concrete_path = ConcretePath::Unrepresentable;
    let unrepresentable = serde_json::to_value(&operand)?;
    assert_eq!(
        unrepresentable.get("concrete_path"),
        Some(&serde_json::json!({"status":"unrepresentable"}))
    );
    assert_ne!(unrepresentable, not_captured);
    assert_ne!(unrepresentable, no_path);
    operand.concrete_path = ConcretePath::Captured {
        root: PathRoot::Input,
        segments: alloc::vec![
            PathSegment::Key(String::from("resources")),
            PathSegment::Index(0),
            PathSegment::Key(String::from("0")),
            PathSegment::Key(String::from("a.b[\"c\"]\\d")),
        ],
    };
    let captured = serde_json::to_value(&operand)?;
    assert_eq!(
        not_captured.get("concrete_path"),
        Some(&serde_json::json!({"status":"not_captured"}))
    );
    assert_eq!(
        no_path.get("concrete_path"),
        Some(&serde_json::json!({"status":"no_path"}))
    );
    assert_ne!(not_captured, no_path);
    assert_eq!(
        captured.get("concrete_path"),
        Some(&serde_json::json!({
            "status":"captured", "root":"input",
            "segments":[{"key":"resources"},{"index":0},{"key":"0"},{"key":"a.b[\"c\"]\\d"}]
        }))
    );
    assert_eq!(
        captured.get("path"),
        Some(&serde_json::json!("input.resources[i]"))
    );
    operand.concrete_path = ConcretePath::Captured {
        root: PathRoot::Data,
        segments: Vec::new(),
    };
    assert_eq!(
        serde_json::to_value(&operand)?.get("concrete_path"),
        Some(&serde_json::json!({"status":"captured","root":"data","segments":[]}))
    );
    Ok(())
}

#[test]
fn sensitive_concrete_path_can_be_withheld_independently_of_source_template(
) -> Result<(), serde_json::Error> {
    let operand = Operand {
        call_uses: None,
        value: ReportedValue::Redacted,
        path: Some(String::from("data.tokens[input.user.token]")),
        concrete_path: ConcretePath::Redacted,
        origins: None,
    };
    assert_eq!(
        serde_json::to_string(&operand)?,
        r#"{"path":"data.tokens[input.user.token]","concrete_path":{"status":"redacted"},"redacted":true}"#
    );
    Ok(())
}

#[test]
fn identical_loop_templates_keep_separate_site_counts_without_proofs(
) -> Result<(), serde_json::Error> {
    let counts = alloc::vec![
        DistinctElements {
            site_id: 0,
            loop_name: String::from("input.resources[_]"),
            collection: 0,
            count: Some(Count::Exact(200))
        },
        DistinctElements {
            site_id: 1,
            loop_name: String::from("input.resources[_]"),
            collection: 0,
            count: Some(Count::Exact(20))
        },
    ];
    assert_eq!(
        serde_json::to_string(&counts)?,
        concat!(
            r#"[{"site_id":0,"loop":"input.resources[_]","collection":0,"count":{"exact":200}},"#,
            r#"{"site_id":1,"loop":"input.resources[_]","collection":0,"count":{"exact":20}}]"#,
        )
    );
    Ok(())
}

#[test]
fn elided_is_distinct_from_undefined_and_redacted_in_all_reported_positions() -> anyhow::Result<()>
{
    for value in [
        ReportedValue::Known(Value::Undefined),
        ReportedValue::Redacted,
        ReportedValue::Elided,
    ] {
        let mut report = partial_object_report();
        let rule = report.rules.first_mut().context("rule")?;
        rule.result = value.clone();
        let emission = rule.emissions.first_mut().context("emission")?;
        emission.key = Some(value.clone());
        emission.value = value.clone();
        let mut result = result_attribution();
        result.key = Some(value.clone());
        result.value = value.clone();
        result.proofs.first_mut().context("proof")?.bindings =
            Some(alloc::vec![IterationBinding {
                site_id: 0,
                collection: 0,
                key: value.clone(),
                value: value.clone(),
            }]);
        rule.results = Some(alloc::vec![result]);
        // A conflict has at least two distinct defined values; only withheld
        // ones are checked here.
        let withheld = !matches!(value, ReportedValue::Known(_));
        if withheld {
            rule.outcome = RuleOutcome::Conflict {
                key: None,
                values: alloc::vec![ReportedValue::Known(Value::from(1)), value.clone()],
            };
        }
        let json = serde_json::to_value(&report)?;
        let conflict = json.pointer("/rules/0/outcome/values/1");
        assert_eq!(conflict.is_some(), withheld);
        if let Some(conflict) = conflict {
            assert!(conflict.get("value").is_none());
            assert_eq!(
                conflict.get("elided"),
                matches!(value, ReportedValue::Elided).then_some(&serde_json::Value::Bool(true))
            );
            assert_eq!(
                conflict.get("redacted"),
                matches!(value, ReportedValue::Redacted).then_some(&serde_json::Value::Bool(true))
            );
        }
        for (pointer, name) in [
            ("/rules/0", "result"),
            ("/rules/0/emissions/0", "key"),
            ("/rules/0/emissions/0", "value"),
            ("/rules/0/results/0", "key"),
            ("/rules/0/results/0", "value"),
            ("/rules/0/results/0/proofs/0/bindings/0", "key"),
            ("/rules/0/results/0/proofs/0/bindings/0", "value"),
        ] {
            let position = json.pointer(pointer).context("reported value position")?;
            assert!(position.get(name).is_none());
            assert_eq!(
                position.get(format!("{name}_elided")),
                matches!(value, ReportedValue::Elided).then_some(&serde_json::Value::Bool(true))
            );
            assert_eq!(
                position.get(format!("{name}_redacted")),
                matches!(value, ReportedValue::Redacted).then_some(&serde_json::Value::Bool(true))
            );
        }
    }
    Ok(())
}

#[test]
fn result_attribution_not_captured_is_distinct_from_no_results() -> anyhow::Result<()> {
    let mut report = partial_set_report();
    report.query_result = Value::new_set();
    let rule = report.rules.first_mut().context("rule")?;
    rule.result = ReportedValue::Known(Value::new_set());
    rule.emissions.clear();
    rule.definitions.clear();
    let absent = serde_json::to_value(&report)?;
    report.rules.first_mut().context("rule")?.results = Some(Vec::new());
    let captured = serde_json::to_value(&report)?;
    assert!(absent.pointer("/rules/0/results").is_none());
    assert_eq!(
        captured.pointer("/rules/0/results"),
        Some(&serde_json::json!([]))
    );
    Ok(())
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

/// Every new top-level, rule, result and proof field appears in the exact
/// JSON, so dropping any of them fails this test.
#[test]
fn attributed_report_json() -> Result<(), serde_json::Error> {
    let expected = concat!(
        r#"{"schema_version":2,"#,
        r#""query":{"entry_point":"data.test.deny","rule":"data.test.deny","call_instance":0,"with_overrides":false},"#,
        r#""query_result":["public"],"rules":[{"name":"data.test.deny","call_instance":0,"kind":"partial_set","#,
        r#""outcome":{"status":"matched"},"result":["public"],"results":[{"value":"public","#,
        r#""derivations_total":{"exact":2},"derivations_shown":1,"derivations_dropped":{"exact":1},"#,
        r#""distinct_elements":["#,
        r#"{"site_id":0,"loop":"input.resources[_]","collection":0,"count":{"exact":2}},"#,
        r#"{"site_id":1,"loop":"r.tags[_]","collection":1,"count":{"exact":1}},"#,
        r#"{"site_id":1,"loop":"r.tags[_]","collection":2,"count":{"exact":1}}],"#,
        r#""proofs":[{"definition":0,"body":0,"conditions":[{"site_id":2,"#,
        r#""owner":{"rule":"data.test.deny","call_instance":0},"outcome":"success","#,
        r#""left":{"path":"t","concrete_path":{"status":"not_captured"},"value":"public"},"#,
        r#""right":{"concrete_path":{"status":"not_captured"},"value":"public"}}],"#,
        r#""bindings":[{"site_id":0,"collection":0,"key":0,"value_elided":true},"#,
        r#"{"site_id":1,"collection":1,"key":0,"value":"public"}]}]}]}],"#,
        r#""checks":[{"site_id":0,"text":"some r in input.resources","kind":"iteration"},"#,
        r#"{"site_id":1,"text":"some t in r.tags","kind":"iteration"},"#,
        r#"{"site_id":2,"text":"t == \"public\"","kind":"comparison","operator":"=="}]}"#,
    );
    assert_eq!(serde_json::to_string(&attributed_report())?, expected);
    Ok(())
}

#[test]
fn schema_version_is_serialized_first_in_every_report() -> Result<(), serde_json::Error> {
    assert_eq!(ExplanationReport::SCHEMA_VERSION, 2);
    for report in [
        complete_rule_report(),
        partial_set_report(),
        partial_object_report(),
        attributed_report(),
        conflict_report(),
    ] {
        assert!(serde_json::to_string(&report)?.starts_with(r#"{"schema_version":2,"query":{"#));
    }
    Ok(())
}

#[test]
fn query_target_identifies_entry_point_and_with_overrides() -> Result<(), serde_json::Error> {
    let mut target = fixtures::query("data.test.allow");
    assert_eq!(
        serde_json::to_string(&target)?,
        r#"{"entry_point":"data.test.allow","rule":"data.test.allow","call_instance":0,"with_overrides":false}"#
    );
    target.with_overrides = true;
    assert_eq!(
        serde_json::to_value(&target)?.get("with_overrides"),
        Some(&serde_json::json!(true))
    );
    let expression = QueryTarget {
        calls: None,
        scopes: None,
        entry_point: String::from("data.test.allow == data.test.deny"),
        rule: None,
        call_instance: None,
        with_overrides: false,
    };
    assert_eq!(
        serde_json::to_string(&expression)?,
        r#"{"entry_point":"data.test.allow == data.test.deny","with_overrides":false}"#
    );
    Ok(())
}

/// A conflict and an absent match both leave the rule undefined; only the
/// outcome tells them apart.
#[test]
fn conflict_report_json_is_distinct_from_no_match() -> anyhow::Result<()> {
    let report = conflict_report();
    assert_eq!(
        serde_json::to_string(&report)?,
        concat!(
            r#"{"schema_version":2,"query":{"entry_point":"data.test.allow","rule":"data.test.allow","#,
            r#""call_instance":0,"with_overrides":true},"rules":[{"name":"data.test.allow","#,
            r#""call_instance":0,"kind":"complete","#,
            r#""outcome":{"status":"conflict","values":[{"value":true},{"value":false}]}}],"checks":[]}"#,
        )
    );
    let mut no_match = report.clone();
    no_match.rules.first_mut().context("rule")?.outcome = RuleOutcome::NoMatch;
    let conflict_json = serde_json::to_value(&report)?;
    let no_match_json = serde_json::to_value(&no_match)?;
    assert_eq!(
        conflict_json.pointer("/rules/0/result"),
        no_match_json.pointer("/rules/0/result")
    );
    assert_ne!(conflict_json, no_match_json);
    Ok(())
}

/// The `match` is exhaustive, so adding a variant fails to compile until
/// its serialization is checked here.
#[test]
fn every_rule_outcome_and_count_variant_has_a_json_form() -> Result<(), serde_json::Error> {
    for outcome in [
        RuleOutcome::Matched,
        RuleOutcome::NoMatch,
        RuleOutcome::Conflict {
            key: None,
            values: alloc::vec![
                ReportedValue::Known(Value::from(1)),
                ReportedValue::Known(Value::from(2)),
                ReportedValue::Redacted,
                ReportedValue::Elided,
            ],
        },
    ] {
        let expected = match outcome {
            RuleOutcome::Matched => serde_json::json!({"status": "matched"}),
            RuleOutcome::NoMatch => serde_json::json!({"status": "no_match"}),
            RuleOutcome::Conflict { .. } => serde_json::json!({
                "status": "conflict",
                "values": [{"value": 1}, {"value": 2}, {"redacted": true}, {"elided": true}],
            }),
        };
        assert_eq!(serde_json::to_value(&outcome)?, expected);
    }
    for count in [Count::Exact(3), Count::AtLeast(3)] {
        let expected = match count {
            Count::Exact(_) => serde_json::json!({"exact": 3}),
            Count::AtLeast(_) => serde_json::json!({"at_least": 3}),
        };
        assert_eq!(serde_json::to_value(count)?, expected);
        assert_eq!(count.value(), 3);
    }
    assert!(Count::Exact(3).is_exact());
    assert!(!Count::AtLeast(3).is_exact());
    Ok(())
}

/// `allow if { some r in input.resources; r.public }` stops at the first
/// public resource, so neither count can claim to be exact.
#[test]
fn early_exit_counts_are_lower_bounds() -> anyhow::Result<()> {
    let mut result = result_attribution();
    result.value = ReportedValue::Known(Value::from(true));
    result.derivations_total = Count::AtLeast(1);
    result
        .distinct_elements
        .first_mut()
        .context("distinct")?
        .count = Some(Count::AtLeast(1));
    let json = serde_json::to_value(&result)?;
    assert_eq!(
        json.get("derivations_total"),
        Some(&serde_json::json!({"at_least": 1}))
    );
    assert_eq!(json.get("derivations_shown"), Some(&serde_json::json!(1)));
    assert_eq!(
        json.get("derivations_dropped"),
        Some(&serde_json::json!({"at_least": 0}))
    );
    assert_eq!(
        json.pointer("/distinct_elements/0/count"),
        Some(&serde_json::json!({"at_least": 1}))
    );
    let mut exact = result.clone();
    exact.derivations_total = Count::Exact(1);
    assert_ne!(serde_json::to_value(&exact)?, json);
    Ok(())
}

/// `shown`/`dropped` are derived from `proofs` and the total, so they can't
/// disagree with them, and more proofs than derivations is rejected.
#[test]
fn derivation_counts_are_derived_and_validated() -> anyhow::Result<()> {
    let proof = result_attribution()
        .proofs
        .first()
        .context("proof")?
        .clone();
    let built = ResultExplanation::new(
        None,
        ReportedValue::Known(Value::from("same")),
        Count::Exact(5),
        Vec::new(),
        alloc::vec![proof.clone(), proof.clone()],
    )
    .context("consistent counts")?;
    assert_eq!(built.derivations_shown(), 2);
    assert_eq!(built.derivations_dropped(), Some(Count::Exact(3)));
    let json = serde_json::to_value(&built)?;
    assert_eq!(json.get("derivations_shown"), Some(&serde_json::json!(2)));
    assert_eq!(
        json.get("derivations_dropped"),
        Some(&serde_json::json!({"exact": 3}))
    );
    assert!(ResultExplanation::new(
        None,
        ReportedValue::Known(Value::from("same")),
        Count::AtLeast(1),
        Vec::new(),
        alloc::vec![proof.clone(), proof],
    )
    .is_none());
    let mut broken = built;
    broken.derivations_total = Count::Exact(1);
    assert_eq!(broken.derivations_dropped(), None);
    let error = serde_json::to_string(&broken)
        .err()
        .context("inconsistent counts must not serialize")?;
    assert!(error
        .to_string()
        .contains("more proofs than derivations_total"));
    Ok(())
}

/// A nested loop over each resource's tags iterates a different collection
/// per resource. Elements at the same index of different collections are
/// different elements, and only `collection` tells their entries and proof
/// bindings apart.
#[test]
fn distinct_elements_of_different_collections_are_not_merged() -> anyhow::Result<()> {
    let json = serde_json::to_value(attributed_report())?;
    let result = json.pointer("/rules/0/results/0").context("result")?;
    let inner: Vec<&serde_json::Value> = result
        .get("distinct_elements")
        .and_then(serde_json::Value::as_array)
        .context("distinct elements")?
        .iter()
        .filter(|entry| entry.get("site_id") == Some(&serde_json::json!(1)))
        .collect();
    assert_eq!(inner.len(), 2);
    let without_collection = |entry: &serde_json::Value| {
        let mut entry = entry.clone();
        entry
            .as_object_mut()
            .and_then(|fields| fields.remove("collection"));
        entry
    };
    let (first, second) = (
        *inner.first().context("first")?,
        *inner.get(1).context("second")?,
    );
    assert_ne!(first, second);
    assert_eq!(without_collection(first), without_collection(second));
    assert_eq!(
        result.pointer("/proofs/0/bindings/1/collection"),
        first.get("collection")
    );
    Ok(())
}

/// Exact shape of redacted values in the new positions: a proof binding's
/// key and value, a dependency's conflict value, and a result key.
#[test]
fn redacted_binding_conflict_and_result_key_json() -> Result<(), serde_json::Error> {
    let conflict = RuleOutcome::Conflict {
        key: None,
        values: alloc::vec![
            ReportedValue::Known(Value::from("a")),
            ReportedValue::Redacted
        ],
    };
    let result = ResultExplanation {
        key: Some(ReportedValue::Redacted),
        value: ReportedValue::Known(Value::from("prod")),
        conditionality: None,
        derivations_total: Count::Exact(1),
        distinct_elements: Vec::new(),
        proofs: alloc::vec![Derivation {
            call_uses: None,
            definition: 0,
            body: 0,
            attempt: None,
            conditionality: None,
            conditions: Vec::new(),
            bindings: Some(alloc::vec![IterationBinding {
                site_id: 0,
                collection: 3,
                key: ReportedValue::Redacted,
                value: ReportedValue::Redacted,
            }]),
        }],
    };
    assert_eq!(
        serde_json::to_string(&conflict)?,
        r#"{"status":"conflict","values":[{"value":"a"},{"redacted":true}]}"#
    );
    assert_eq!(
        serde_json::to_string(&result)?,
        concat!(
            r#"{"key_redacted":true,"value":"prod","derivations_total":{"exact":1},"#,
            r#""derivations_shown":1,"derivations_dropped":{"exact":0},"distinct_elements":[],"#,
            r#""proofs":[{"definition":0,"body":0,"conditions":[],"#,
            r#""bindings":[{"site_id":0,"collection":3,"key_redacted":true,"value_redacted":true}]}]}"#,
        )
    );
    Ok(())
}

#[test]
fn attempts_scopes_and_cached_uses_keep_ownership() -> anyhow::Result<()> {
    let mut report = complete_rule_report();
    let rule = report.rules.first_mut().context("queried rule")?;
    rule.call_instance = 1;
    let mut failed_conditions = rule
        .definitions
        .first()
        .context("failed primary body")?
        .conditions
        .clone();
    for condition in &mut failed_conditions {
        condition.owner.call_instance = 1;
        condition.owner.attempt = Some(1);
    }
    let failed_context = serde_json::to_value(&failed_conditions)?;
    rule.attempts = Some(alloc::vec![
        AttemptExplanation {
            attempt: 1,
            definition: 0,
            body: 0,
            outcome: Some(Outcome::Failure),
            conditions: Some(failed_conditions),
        },
        AttemptExplanation {
            attempt: 2,
            definition: 0,
            body: 1,
            outcome: Some(Outcome::Success),
            conditions: None,
        },
    ]);
    rule.scopes = Some(alloc::vec![
        ScopeExplanation {
            scope: 1,
            kind: ScopeKind::Negation,
            parent: None,
            attempt: 2,
            site_id: 2,
            outcome: Some(Outcome::Success),
        },
        ScopeExplanation {
            scope: 2,
            kind: ScopeKind::ArrayComprehension,
            parent: Some(1),
            attempt: 2,
            site_id: 3,
            outcome: Some(Outcome::Success),
        },
    ]);
    rule.calls = Some(alloc::vec![
        CallUse {
            use_id: 1,
            call_instance: 2,
            attempt: Some(2),
            scope: None
        },
        CallUse {
            use_id: 2,
            call_instance: 2,
            attempt: Some(2),
            scope: Some(1)
        },
    ]);
    let mut helper = rule.clone();
    helper.name = String::from("data.test.helper");
    helper.call_instance = 2;
    helper.result = ReportedValue::Known(Value::from(false));
    helper.attempts = Some(alloc::vec![
        AttemptExplanation {
            attempt: 3,
            definition: 0,
            body: 0,
            outcome: Some(Outcome::Undefined),
            conditions: Some(Vec::new()),
        },
        AttemptExplanation {
            attempt: 4,
            definition: 1,
            body: 0,
            outcome: Some(Outcome::Success),
            conditions: None,
        },
    ]);
    helper.scopes = Some(Vec::new());
    helper.calls = Some(Vec::new());
    helper.definitions.clear();
    // The failed helper attempt is context; only attempt 4 owns its cause.
    let mut helper_condition = rule
        .definitions
        .get(1)
        .and_then(|definition| definition.conditions.first())
        .context("helper check fixture")?
        .clone();
    helper_condition.owner = ConditionOwner {
        rule: helper.name.clone(),
        call_instance: 2,
        attempt: Some(4),
        scope: None,
    };
    helper.definitions.push(DefinitionExplanation {
        index: 1,
        body: 0,
        outcome: Outcome::Success,
        location: Some(SourceLocation {
            file: String::from("p.rego"),
            line: 7,
            column: 1,
        }),
        conditions: alloc::vec![helper_condition],
    });
    let mut deciding_body = rule.definitions.get(1).context("else body")?.clone();
    deciding_body.index = 0;
    for condition in &mut deciding_body.conditions {
        condition.owner.call_instance = 1;
        condition.owner.attempt = Some(2);
    }
    rule.definitions = alloc::vec![deciding_body];
    let retained_check = helper
        .definitions
        .first()
        .and_then(|definition| definition.conditions.first())
        .context("retained callee check")?
        .clone();
    let proof = |use_id| {
        let mut condition = retained_check.clone();
        condition.call_uses = Some(vec![vec![use_id]]);
        Derivation {
            definition: 0,
            body: 1,
            attempt: Some(2),
            conditionality: Some(Conditionality::Concrete),
            call_uses: Some(vec![use_id]),
            conditions: vec![condition],
            bindings: Some(Vec::new()),
        }
    };
    rule.results = Some(vec![ResultExplanation::new(
        None,
        rule.result.clone(),
        Count::Exact(2),
        Vec::new(),
        vec![proof(1), proof(2)],
    )
    .context("two cached-use proofs")?]);
    report.query.call_instance = Some(1);
    for (site_id, kind) in [
        (2, ConditionKind::Negation),
        (3, ConditionKind::Comprehension),
    ] {
        report.checks.push(ConditionSite {
            site_id,
            text: String::from("nested construct"),
            kind,
            location: None,
            operator: None,
        });
    }
    report.rules.push(helper);
    let json = serde_json::to_value(&report)?;
    assert_eq!(
        json.pointer("/rules/0/attempts"),
        Some(&serde_json::json!([
            {"attempt":1,"definition":0,"body":0,"outcome":"failure","conditions":failed_context},
            {"attempt":2,"definition":0,"body":1,"outcome":"success"}
        ]))
    );
    assert_eq!(
        json.pointer("/rules/0/definitions/0/body"),
        Some(&serde_json::json!(1))
    );
    assert_eq!(
        report
            .rules
            .first()
            .context("queried rule")?
            .definitions
            .len(),
        1
    );
    assert_eq!(
        json.pointer("/rules/0/attempts/0/conditions/0/outcome"),
        Some(&serde_json::json!("failure"))
    );
    assert_eq!(
        json.pointer("/rules/0/attempts/0/conditions/0/owner/attempt"),
        Some(&serde_json::json!(1))
    );
    assert_eq!(
        json.pointer("/rules/1/attempts/0/conditions"),
        Some(&serde_json::json!([]))
    );
    assert_eq!(
        json.pointer("/rules/0/scopes"),
        Some(&serde_json::json!([
            {"scope":1,"kind":"negation","attempt":2,"site_id":2,"outcome":"success"},
            {"scope":2,"kind":"array_comprehension","parent":1,"attempt":2,"site_id":3,"outcome":"success"}
        ]))
    );
    assert_eq!(
        json.pointer("/rules/0/calls"),
        Some(&serde_json::json!([
            {"use_id":1,"call_instance":2,"attempt":2},
            {"use_id":2,"call_instance":2,"attempt":2,"scope":1}
        ]))
    );
    assert_eq!(
        json.pointer("/rules/1/definitions/0/conditions/0/owner"),
        Some(&serde_json::json!({"rule":"data.test.helper","call_instance":2,"attempt":4}))
    );
    assert_eq!(
        json.pointer("/rules/1/result"),
        Some(&serde_json::json!(false))
    );
    for (index, use_id, scope) in [(0, 1, None), (1, 2, Some(1))] {
        let proof_json = json
            .pointer(&format!("/rules/0/results/0/proofs/{index}"))
            .context("cached-use proof")?;
        assert_eq!(
            proof_json.get("call_uses"),
            Some(&serde_json::json!([use_id]))
        );
        assert_eq!(
            proof_json.pointer("/conditions/0/call_uses"),
            Some(&serde_json::json!([[use_id]]))
        );
        assert_eq!(
            proof_json.pointer("/conditions/0/owner"),
            json.pointer("/rules/1/definitions/0/conditions/0/owner")
        );
        let use_edge = report
            .rules
            .first()
            .and_then(|caller| caller.calls.as_ref())
            .and_then(|calls| calls.iter().find(|call| call.use_id == use_id))
            .context("exact contributing use")?;
        assert_eq!((use_edge.call_instance, use_edge.scope), (2, scope));
    }
    assert_eq!(
        json.pointer("/rules/1/scopes"),
        Some(&serde_json::json!([]))
    );
    let uncaptured_helper = report.rules.get_mut(1).context("helper invocation")?;
    uncaptured_helper.attempts = None;
    uncaptured_helper.scopes = None;
    uncaptured_helper.calls = None;
    let uncaptured = serde_json::to_value(&report)?;
    assert!(uncaptured.pointer("/rules/1/attempts").is_none());
    assert!(uncaptured.pointer("/rules/1/scopes").is_none());
    assert!(uncaptured.pointer("/rules/1/calls").is_none());
    Ok(())
}

#[test]
fn arbitrary_queries_own_cached_uses_and_negation_scopes() -> anyhow::Result<()> {
    let mut report = complete_rule_report();
    let rule = report.rules.first_mut().context("queried rule")?;
    rule.call_instance = 1;
    for definition in &mut rule.definitions {
        for condition in &mut definition.conditions {
            condition.owner.call_instance = 1;
        }
    }
    report.query.entry_point = String::from("data.test.allow; not data.test.allow == false");
    report.query.rule = None;
    report.query.call_instance = None;
    let truthiness_site = u32::try_from(report.checks.len())?;
    report.checks.push(ConditionSite {
        site_id: truthiness_site,
        text: String::from("data.test.allow"),
        kind: ConditionKind::Truthiness,
        location: None,
        operator: None,
    });
    let site_id = u32::try_from(report.checks.len())?;
    report.checks.push(ConditionSite {
        site_id,
        text: String::from("not data.test.allow == false"),
        kind: ConditionKind::Negation,
        location: None,
        operator: Some(Operator::Eq),
    });
    report.query.calls = Some(vec![
        CallUse {
            use_id: 1,
            call_instance: 1,
            attempt: None,
            scope: None,
        },
        CallUse {
            use_id: 2,
            call_instance: 1,
            attempt: None,
            scope: Some(1),
        },
    ]);
    report.query.scopes = Some(vec![QueryScopeExplanation {
        scope: 1,
        kind: ScopeKind::Negation,
        parent: None,
        site_id,
        outcome: Some(Outcome::Success),
    }]);
    report.query_conditions = Some(vec![
        QueryConditionExplanation {
            witness: None,
            binding: None,
            site_id: truthiness_site,
            scope: None,
            completed_scope: None,
            outcome: Outcome::Success,
            left: Some(known(Value::from(true), None)),
            right: None,
            call_uses: Some(vec![vec![1]]),
        },
        QueryConditionExplanation {
            witness: None,
            binding: None,
            site_id,
            scope: None,
            completed_scope: Some(1),
            outcome: Outcome::Success,
            left: Some(known(Value::from(true), None)),
            right: Some(known(Value::from(false), None)),
            call_uses: Some(vec![vec![2]]),
        },
    ]);
    let json = serde_json::to_value(&report)?;
    assert!(json.pointer("/query/rule").is_none());
    assert!(json.pointer("/query/call_instance").is_none());
    assert_eq!(
        json.pointer("/query/calls"),
        Some(&serde_json::json!([
            {"use_id":1,"call_instance":1},
            {"use_id":2,"call_instance":1,"scope":1}
        ]))
    );
    assert_eq!(
        json.pointer("/query/scopes"),
        Some(&serde_json::json!([
            {"scope":1,"kind":"negation","site_id":site_id,"outcome":"success"}
        ]))
    );
    assert_eq!(
        json.pointer("/query_conditions/0/call_uses"),
        Some(&serde_json::json!([[1]]))
    );
    assert_eq!(
        json.pointer("/query_conditions/1/call_uses"),
        Some(&serde_json::json!([[2]]))
    );
    assert_eq!(
        json.pointer("/query_conditions/1/completed_scope"),
        Some(&serde_json::json!(1))
    );
    assert!(json.pointer("/query_conditions/1/scope").is_none());
    assert!(json.pointer("/query_conditions/1/owner").is_none());
    report.query.calls = Some(Vec::new());
    report.query.scopes = Some(Vec::new());
    report.query_conditions = Some(Vec::new());
    let empty = serde_json::to_value(&report)?;
    assert_eq!(empty.pointer("/query/calls"), Some(&serde_json::json!([])));
    assert_eq!(empty.pointer("/query/scopes"), Some(&serde_json::json!([])));
    assert_eq!(empty.get("query_conditions"), Some(&serde_json::json!([])));
    report.query.calls = None;
    report.query.scopes = None;
    report.query_conditions = None;
    let uncaptured = serde_json::to_value(&report)?;
    assert!(uncaptured.pointer("/query/calls").is_none());
    assert!(uncaptured.pointer("/query/scopes").is_none());
    assert!(uncaptured.get("query_conditions").is_none());
    Ok(())
}

#[test]
fn query_iterations_and_bindings_keep_their_evidence() -> anyhow::Result<()> {
    let mut report = complete_rule_report();
    report.query.rule = None;
    report.query.call_instance = None;
    report.query.entry_point = String::from("some x in input.xs; y := x");
    report.rules.clear();
    report.checks = vec![
        ConditionSite {
            site_id: 0,
            text: String::from("input.xs"),
            kind: ConditionKind::Iteration,
            location: None,
            operator: None,
        },
        ConditionSite {
            site_id: 1,
            text: String::from("y := x"),
            kind: ConditionKind::Binding,
            location: None,
            operator: None,
        },
    ];
    report.query_conditions = Some(vec![
        QueryConditionExplanation {
            site_id: 0,
            scope: None,
            completed_scope: None,
            outcome: Outcome::Success,
            left: Some(known(
                Value::from(vec![Value::from(false)]),
                Some("input.xs"),
            )),
            right: None,
            call_uses: Some(Vec::new()),
            binding: Some(String::from("x")),
            witness: Some(LoopWitness {
                iterations: 1,
                successes: 1,
                sample_key: Some(known(Value::from(0), None)),
                sample_value: Some(known(Value::from(false), Some("input.xs"))),
            }),
        },
        QueryConditionExplanation {
            site_id: 1,
            scope: None,
            completed_scope: None,
            outcome: Outcome::Success,
            left: Some(known(Value::from(false), None)),
            right: None,
            call_uses: Some(Vec::new()),
            binding: Some(String::from("y")),
            witness: None,
        },
    ]);
    let json = serde_json::to_value(&report)?;
    assert_eq!(
        json.pointer("/query_conditions/0/binding"),
        Some(&serde_json::json!("x"))
    );
    assert_eq!(
        json.pointer("/query_conditions/0/witness"),
        Some(&serde_json::json!({
            "iterations":1,"successes":1,
            "sample_key":{"concrete_path":{"status":"not_captured"},"value":0},
            "sample_value":{"path":"input.xs","concrete_path":{"status":"not_captured"},"value":false}
        }))
    );
    assert_eq!(
        json.pointer("/query_conditions/1/binding"),
        Some(&serde_json::json!("y"))
    );
    assert_eq!(
        json.pointer("/query_conditions/1/left/value"),
        Some(&serde_json::json!(false))
    );
    assert!(json.pointer("/query_conditions/1/witness").is_none());
    for check in json
        .get("query_conditions")
        .and_then(serde_json::Value::as_array)
        .context("query checks")?
    {
        assert!(check.get("owner").is_none());
    }
    report
        .query_conditions
        .as_mut()
        .and_then(|checks| checks.first_mut())
        .context("iteration check")?
        .binding = None;
    assert!(serde_json::to_value(&report)?
        .pointer("/query_conditions/0/binding")
        .is_none());
    Ok(())
}

#[test]
fn conditionality_is_independent_of_bounded_proofs() -> anyhow::Result<()> {
    let proof = |conditionality| Derivation {
        call_uses: None,
        definition: 0,
        body: 0,
        attempt: Some(1),
        conditionality: Some(conditionality),
        conditions: Vec::new(),
        bindings: Some(Vec::new()),
    };
    let mut result = ResultExplanation::new(
        None,
        ReportedValue::Known(Value::from("finding")),
        Count::Exact(2),
        Vec::new(),
        alloc::vec![
            proof(Conditionality::Concrete),
            proof(Conditionality::Assumed)
        ],
    )
    .context("valid proof count")?;
    result.conditionality = Some(Conditionality::Concrete);
    assert_eq!(
        serde_json::to_value(&result)?,
        serde_json::json!({
            "value":"finding","conditionality":"concrete","derivations_total":{"exact":2},
            "derivations_shown":2,"derivations_dropped":{"exact":0},"distinct_elements":[],
            "proofs":[
                {"definition":0,"body":0,"attempt":1,"conditionality":"concrete","conditions":[],"bindings":[]},
                {"definition":0,"body":0,"attempt":1,"conditionality":"assumed","conditions":[],"bindings":[]}
            ]
        })
    );
    result.proofs.remove(0);
    let capped = serde_json::to_value(&result)?;
    assert_eq!(
        capped.get("conditionality"),
        Some(&serde_json::json!("concrete"))
    );
    assert_eq!(
        capped.pointer("/proofs/0/conditionality"),
        Some(&serde_json::json!("assumed"))
    );
    result.proofs.clear();
    assert_eq!(
        serde_json::to_value(&result)?.get("conditionality"),
        Some(&serde_json::json!("concrete"))
    );
    result.conditionality = None;
    assert!(serde_json::to_value(&result)?
        .get("conditionality")
        .is_none());
    result.conditionality = Some(Conditionality::Assumed);
    assert_eq!(
        serde_json::to_value(&result)?.get("conditionality"),
        Some(&serde_json::json!("assumed"))
    );
    Ok(())
}

#[test]
fn caller_checks_keep_separate_sibling_dependency_paths() -> anyhow::Result<()> {
    let mut report = attributed_report();
    let first_site = u32::try_from(report.checks.len())?;
    for (offset, text) in [
        (0, "f(input.a) == g(input.b)"),
        (1, "h(input.a) == j(input.b)"),
    ] {
        report.checks.push(ConditionSite {
            site_id: first_site + offset,
            text: String::from(text),
            kind: ConditionKind::Comparison,
            location: None,
            operator: Some(Operator::Eq),
        });
    }
    report.query.call_instance = Some(1);
    let rule = report.rules.first_mut().context("queried rule")?;
    rule.call_instance = 1;
    let template = rule.clone();
    rule.calls = Some(
        (1..=4)
            .map(|use_id| CallUse {
                use_id,
                call_instance: use_id + 1,
                attempt: Some(1),
                scope: None,
            })
            .collect(),
    );
    let proof = rule
        .results
        .as_mut()
        .and_then(|results| results.first_mut())
        .and_then(|result| result.proofs.first_mut())
        .context("retained proof")?;
    let mut first = proof.conditions.first().context("caller check")?.clone();
    first.site_id = first_site;
    first.owner.call_instance = 1;
    first.owner.attempt = Some(1);
    first.call_uses = Some(vec![vec![1], vec![2]]);
    let mut left = known(Value::from(false), None);
    left.call_uses = Some(vec![vec![1]]);
    let mut right = left.clone();
    right.call_uses = Some(vec![vec![2]]);
    first.left = Some(left);
    first.right = Some(right);
    let mut second = first.clone();
    second.site_id = first_site + 1;
    second.call_uses = Some(vec![vec![3], vec![4]]);
    second.left.as_mut().context("second left")?.call_uses = Some(vec![vec![3]]);
    second.right.as_mut().context("second right")?.call_uses = Some(vec![vec![4]]);
    proof.call_uses = Some(vec![1, 2, 3, 4]);
    proof.conditions = vec![first, second];
    for (call_instance, name) in [(2, "f"), (3, "g"), (4, "h"), (5, "j")] {
        let mut helper = template.clone();
        helper.name = format!("data.test.{name}");
        helper.call_instance = call_instance;
        helper.kind = RuleKind::Function;
        helper.result = ReportedValue::Known(Value::from(false));
        helper.results = None;
        helper.emissions.clear();
        helper.definitions.clear();
        report.rules.push(helper);
    }
    let json = serde_json::to_value(&report)?;
    assert_eq!(
        json.pointer("/rules/0/results/0/proofs/0/conditions/0/call_uses"),
        Some(&serde_json::json!([[1], [2]]))
    );
    assert_eq!(
        json.pointer("/rules/0/results/0/proofs/0/conditions/1/call_uses"),
        Some(&serde_json::json!([[3], [4]]))
    );
    assert_eq!(
        json.pointer("/rules/0/results/0/proofs/0/call_uses"),
        Some(&serde_json::json!([1, 2, 3, 4]))
    );
    assert_eq!(
        json.pointer("/rules/0/results/0/proofs/0/conditions/0/owner/call_instance"),
        Some(&serde_json::json!(1))
    );
    for (index, uses, names) in [(0, [1, 2], ["f", "g"]), (1, [3, 4], ["h", "j"])] {
        let check = json
            .pointer(&format!("/rules/0/results/0/proofs/0/conditions/{index}"))
            .context("sibling comparison")?;
        assert_eq!(
            check.get("site_id"),
            Some(&serde_json::json!(first_site + index))
        );
        assert_eq!(check.pointer("/left/value"), check.pointer("/right/value"));
        for ((side, use_id), name) in ["left", "right"].into_iter().zip(uses).zip(names) {
            assert_eq!(
                check.pointer(&format!("/{side}/call_uses")),
                Some(&serde_json::json!([[use_id]]))
            );
            let edge = report
                .rules
                .first()
                .and_then(|root| root.calls.as_ref())
                .and_then(|calls| calls.iter().find(|call| call.use_id == use_id))
                .context("operand producer edge")?;
            let producer = report
                .rules
                .iter()
                .find(|helper| helper.call_instance == edge.call_instance)
                .context("operand producer")?;
            assert_eq!(producer.result, ReportedValue::Known(Value::from(false)));
            assert_eq!(producer.name, format!("data.test.{name}"));
        }
    }
    Ok(())
}

#[test]
fn nested_use_paths_resolve_in_caller_to_callee_order() -> anyhow::Result<()> {
    let mut report = attributed_report();
    let query_site = u32::try_from(report.checks.len())?;
    report.checks.push(ConditionSite {
        site_id: query_site,
        text: String::from("data.test.deny"),
        kind: ConditionKind::Truthiness,
        location: None,
        operator: None,
    });
    let negation_site = query_site + 1;
    report.checks.push(ConditionSite {
        site_id: negation_site,
        text: String::from("not data.test.deny == set()"),
        kind: ConditionKind::Negation,
        location: None,
        operator: Some(Operator::Eq),
    });
    report.query.rule = None;
    report.query.call_instance = None;
    report.query.entry_point = String::from("data.test.deny; not data.test.deny == set()");
    report.query.calls = Some(vec![
        CallUse {
            use_id: 1,
            call_instance: 2,
            attempt: None,
            scope: None,
        },
        CallUse {
            use_id: 4,
            call_instance: 2,
            attempt: None,
            scope: Some(1),
        },
    ]);
    report.query.scopes = Some(vec![QueryScopeExplanation {
        scope: 1,
        kind: ScopeKind::Negation,
        parent: None,
        site_id: negation_site,
        outcome: Some(Outcome::Success),
    }]);
    let root = report.rules.first_mut().context("caller")?;
    root.call_instance = 2;
    root.calls = Some(vec![CallUse {
        use_id: 2,
        call_instance: 3,
        attempt: Some(1),
        scope: None,
    }]);
    let mut callee = root.clone();
    let mut middle = root.clone();
    middle.name = String::from("data.test.middle");
    middle.call_instance = 3;
    middle.results = None;
    middle.definitions.clear();
    middle.emissions.clear();
    middle.calls = Some(vec![CallUse {
        use_id: 3,
        call_instance: 4,
        attempt: Some(1),
        scope: None,
    }]);
    callee.name = String::from("data.test.helper");
    callee.call_instance = 4;
    callee.calls = Some(Vec::new());
    callee.emissions.clear();
    let mut check = callee
        .results
        .as_ref()
        .and_then(|results| results.first())
        .and_then(|result| result.proofs.first())
        .and_then(|proof| proof.conditions.first())
        .context("physical callee check")?
        .clone();
    callee.results = None;
    check.owner.rule = callee.name.clone();
    check.owner.call_instance = 4;
    check.owner.attempt = Some(1);
    check.call_uses = None;
    callee.definitions = vec![DefinitionExplanation {
        index: 0,
        body: 0,
        outcome: Outcome::Success,
        location: None,
        conditions: vec![check.clone()],
    }];
    let retained = root
        .results
        .as_mut()
        .and_then(|results| results.first_mut())
        .and_then(|result| result.proofs.first_mut())
        .context("contributing proof")?;
    check.call_uses = Some(vec![vec![2, 3]]);
    retained.conditions = vec![check];
    retained.call_uses = Some(vec![2, 3]);
    report.rules.push(middle);
    report.rules.push(callee);
    report.query_conditions = Some(
        [(1, query_site, None), (4, negation_site, Some(1))]
            .into_iter()
            .map(
                |(use_id, site_id, completed_scope)| QueryConditionExplanation {
                    site_id,
                    scope: None,
                    completed_scope,
                    outcome: Outcome::Success,
                    left: Some(known(report.query_result.clone(), None)),
                    right: completed_scope
                        .map(|_| known(Value::from(BTreeSet::<Value>::new()), None)),
                    witness: None,
                    binding: None,
                    call_uses: Some(vec![vec![use_id, 2, 3]]),
                },
            )
            .collect(),
    );
    let json = serde_json::to_value(&report)?;
    assert_eq!(
        json.pointer("/rules/0/results/0/proofs/0/conditions/0/call_uses"),
        Some(&serde_json::json!([[2, 3]]))
    );
    assert_eq!(
        json.pointer("/rules/0/results/0/proofs/0/conditions/0/owner"),
        json.pointer("/rules/2/definitions/0/conditions/0/owner")
    );
    assert_eq!(
        json.pointer("/rules/0/results/0/proofs/0/call_uses"),
        Some(&serde_json::json!([2, 3]))
    );
    assert_eq!(
        json.pointer("/query_conditions/0/call_uses"),
        Some(&serde_json::json!([[1, 2, 3]]))
    );
    assert_eq!(
        json.pointer("/query_conditions/1/call_uses"),
        Some(&serde_json::json!([[4, 2, 3]]))
    );
    assert_eq!(
        json.pointer("/query_conditions/0/site_id"),
        Some(&serde_json::json!(query_site))
    );
    assert_eq!(
        json.pointer("/query_conditions/1/site_id"),
        Some(&serde_json::json!(negation_site))
    );
    assert!(json.pointer("/query_conditions/1/scope").is_none());
    assert_eq!(
        json.pointer("/query_conditions/1/completed_scope"),
        Some(&serde_json::json!(1))
    );
    let path = report
        .rules
        .first()
        .and_then(|rule| rule.results.as_ref())
        .and_then(|results| results.first())
        .and_then(|result| result.proofs.first())
        .and_then(|proof| proof.conditions.first())
        .and_then(|condition| condition.call_uses.as_ref())
        .and_then(|paths| paths.first())
        .context("nested use path")?;
    let mut calls = report
        .rules
        .first()
        .and_then(|rule| rule.calls.as_ref())
        .context("proof-owning invocation uses")?;
    let mut reached = None;
    for use_id in path {
        let edge = calls
            .iter()
            .find(|edge| edge.use_id == *use_id)
            .context("contiguous use")?;
        assert_eq!(
            calls
                .iter()
                .filter(|candidate| candidate.use_id == *use_id)
                .count(),
            1
        );
        let rule = report
            .rules
            .iter()
            .find(|rule| rule.call_instance == edge.call_instance)
            .context("physical callee")?;
        reached = Some(rule.call_instance);
        calls = rule.calls.as_ref().context("callee uses")?;
    }
    assert_eq!(reached, Some(4));
    Ok(())
}

#[test]
fn captured_empty_use_dependencies_are_not_uncaptured() -> anyhow::Result<()> {
    let report = attributed_report();
    let mut proof = report
        .rules
        .first()
        .and_then(|rule| rule.results.as_ref())
        .and_then(|results| results.first())
        .and_then(|result| result.proofs.first())
        .context("proof")?
        .clone();
    let mut condition = proof.conditions.first().context("condition")?.clone();
    let mut query_condition = QueryConditionExplanation {
        witness: None,
        binding: None,
        site_id: condition.site_id,
        scope: None,
        completed_scope: None,
        outcome: condition.outcome,
        left: condition.left.clone(),
        right: condition.right.clone(),
        call_uses: None,
    };
    proof.call_uses = None;
    condition.call_uses = None;
    let mut operand = known(Value::from(false), None);
    for value in [
        serde_json::to_value(&proof)?,
        serde_json::to_value(&condition)?,
        serde_json::to_value(&query_condition)?,
        serde_json::to_value(&operand)?,
    ] {
        assert!(value.get("call_uses").is_none());
    }
    proof.call_uses = Some(Vec::new());
    condition.call_uses = Some(Vec::new());
    query_condition.call_uses = Some(Vec::new());
    operand.call_uses = Some(Vec::new());
    for value in [
        serde_json::to_value(&proof)?,
        serde_json::to_value(&condition)?,
        serde_json::to_value(&query_condition)?,
        serde_json::to_value(&operand)?,
    ] {
        assert_eq!(value.get("call_uses"), Some(&serde_json::json!([])));
    }
    Ok(())
}

#[test]
fn repeated_negation_completions_name_their_operand_scopes() -> anyhow::Result<()> {
    let mut report = complete_rule_report();
    let rule = report.rules.first_mut().context("queried rule")?;
    let mut condition = rule
        .definitions
        .get(1)
        .and_then(|definition| definition.conditions.first())
        .context("check fixture")?
        .clone();
    let construct_site = u32::try_from(report.checks.len())?;
    let check_site = construct_site.checked_add(1).context("next site")?;
    for (site_id, kind, text) in [
        (
            construct_site,
            ConditionKind::Comprehension,
            "[true | not x]",
        ),
        (check_site, ConditionKind::Negation, "not x"),
    ] {
        report.checks.push(ConditionSite {
            site_id,
            text: String::from(text),
            kind,
            location: None,
            operator: None,
        });
    }
    condition.site_id = check_site;
    condition.owner.attempt = Some(2);
    condition.owner.scope = Some(1);
    condition.completed_scope = Some(2);
    let mut repeated = condition.clone();
    repeated.completed_scope = Some(3);
    rule.attempts = Some(vec![AttemptExplanation {
        attempt: 2,
        definition: 0,
        body: 1,
        outcome: Some(Outcome::Success),
        conditions: Some(vec![condition, repeated]),
    }]);
    rule.scopes = Some(
        [1, 2, 3]
            .into_iter()
            .map(|scope| ScopeExplanation {
                scope,
                kind: if scope == 1 {
                    ScopeKind::ArrayComprehension
                } else {
                    ScopeKind::Negation
                },
                parent: (scope != 1).then_some(1),
                attempt: 2,
                site_id: if scope == 1 {
                    construct_site
                } else {
                    check_site
                },
                outcome: Some(Outcome::Success),
            })
            .collect(),
    );
    let json = serde_json::to_value(&report)?;
    for (index, scope) in [(0, 2), (1, 3)] {
        let check = json
            .pointer(&format!("/rules/0/attempts/0/conditions/{index}"))
            .context("completed check")?;
        assert_eq!(check.get("site_id"), Some(&serde_json::json!(check_site)));
        assert_eq!(check.pointer("/owner/scope"), Some(&serde_json::json!(1)));
        assert_eq!(
            check.get("completed_scope"),
            Some(&serde_json::json!(scope))
        );
    }
    Ok(())
}

#[test]
fn nested_comprehension_conditions_do_not_replace_the_finding_subject() -> anyhow::Result<()> {
    // deny contains name if { some name in input.users; not count([tag |
    // some tag in input.tags; tag == "public"]) == 0 }
    let mut report = partial_set_report();
    report.query.call_instance = Some(1);
    let rule = report.rules.first_mut().context("queried rule")?;
    rule.call_instance = 1;
    let owner = |scope| ConditionOwner {
        rule: String::from("data.test.deny"),
        call_instance: 1,
        attempt: Some(1),
        scope,
    };
    let subject = rule
        .definitions
        .first_mut()
        .context("queried definition")?
        .conditions
        .first_mut()
        .context("subject loop")?;
    subject.owner = owner(None);
    subject.witness = None;
    let local = ConditionExplanation {
        completed_scope: None,
        call_uses: None,
        site_id: 3,
        owner: owner(Some(2)),
        outcome: Outcome::Success,
        left: None,
        right: None,
        witness: Some(LoopWitness {
            iterations: 1,
            successes: 1,
            sample_key: Some(known(Value::from(0), None)),
            sample_value: Some(known(Value::from("public"), Some("input.tags"))),
        }),
        binding: Some(String::from("tag")),
    };
    let predicate = ConditionExplanation {
        completed_scope: None,
        call_uses: None,
        site_id: 4,
        owner: owner(Some(2)),
        outcome: Outcome::Success,
        left: Some(known(Value::from("public"), Some("tag"))),
        right: Some(known(Value::from("public"), None)),
        witness: None,
        binding: None,
    };
    let negation = ConditionExplanation {
        completed_scope: Some(1),
        call_uses: None,
        site_id: 1,
        owner: owner(None),
        outcome: Outcome::Success,
        left: Some(known(Value::from(1), None)),
        right: Some(known(Value::from(0), None)),
        witness: None,
        binding: None,
    };
    let conditions = vec![subject.clone(), local, predicate, negation];
    rule.definitions
        .first_mut()
        .context("queried definition")?
        .conditions = conditions.clone();
    rule.emissions
        .first_mut()
        .context("queried emission")?
        .conditions = conditions.clone();
    rule.attempts = Some(vec![AttemptExplanation {
        attempt: 1,
        definition: 0,
        body: 0,
        outcome: Some(Outcome::Success),
        conditions: Some(conditions.clone()),
    }]);
    rule.scopes = Some(vec![
        ScopeExplanation {
            scope: 1,
            kind: ScopeKind::Negation,
            parent: None,
            attempt: 1,
            site_id: 1,
            outcome: Some(Outcome::Success),
        },
        ScopeExplanation {
            scope: 2,
            kind: ScopeKind::ArrayComprehension,
            parent: Some(1),
            attempt: 1,
            site_id: 2,
            outcome: Some(Outcome::Success),
        },
    ]);
    rule.results = Some(vec![ResultExplanation::new(
        None,
        ReportedValue::Known(Value::from("bob")),
        Count::Exact(1),
        vec![DistinctElements {
            site_id: 0,
            loop_name: String::from("input.users[_]"),
            collection: 1,
            count: Some(Count::Exact(1)),
        }],
        vec![Derivation {
            call_uses: None,
            definition: 0,
            body: 0,
            attempt: Some(1),
            conditionality: Some(Conditionality::Concrete),
            conditions,
            bindings: Some(vec![IterationBinding {
                site_id: 0,
                collection: 1,
                key: ReportedValue::Known(Value::from(0)),
                value: ReportedValue::Known(Value::from("bob")),
            }]),
        }],
    )
    .context("valid proof count")?]);
    for (site_id, text, kind, operator) in [
        (
            1,
            r#"not count([tag | some tag in input.tags; tag == "public"]) == 0"#,
            ConditionKind::Negation,
            Some(Operator::Eq),
        ),
        (
            2,
            r#"[tag | some tag in input.tags; tag == "public"]"#,
            ConditionKind::Comprehension,
            None,
        ),
        (3, "some tag in input.tags", ConditionKind::Iteration, None),
        (
            4,
            r#"tag == "public""#,
            ConditionKind::Comparison,
            Some(Operator::Eq),
        ),
    ] {
        report.checks.push(ConditionSite {
            site_id,
            text: String::from(text),
            kind,
            location: None,
            operator,
        });
    }
    let json = serde_json::to_value(&report)?;
    let proof = json
        .pointer("/rules/0/results/0/proofs/0")
        .context("proof")?;
    assert_eq!(
        proof.get("bindings"),
        Some(&serde_json::json!([
            {"site_id":0,"collection":1,"key":0,"value":"bob"}
        ]))
    );
    assert_eq!(
        proof.pointer("/conditions/1"),
        Some(&serde_json::json!({
            "site_id":3,"owner":{"rule":"data.test.deny","call_instance":1,"attempt":1,"scope":2},
            "outcome":"success","binding":"tag",
            "witness":{"iterations":1,"successes":1,
                "sample_key":{"concrete_path":{"status":"not_captured"},"value":0},
                "sample_value":{"path":"input.tags","concrete_path":{"status":"not_captured"},"value":"public"}}
        }))
    );
    assert_eq!(
        proof.pointer("/conditions/2/owner/scope"),
        Some(&serde_json::json!(2))
    );
    assert_eq!(proof.pointer("/conditions/3/owner/scope"), None);
    assert_eq!(
        proof.pointer("/conditions/3/completed_scope"),
        Some(&serde_json::json!(1))
    );
    assert_eq!(proof.pointer("/conditions/0/owner/scope"), None);
    assert_eq!(
        json.pointer("/rules/0/scopes"),
        Some(&serde_json::json!([
            {"scope":1,"kind":"negation","attempt":1,"site_id":1,"outcome":"success"},
            {"scope":2,"kind":"array_comprehension","parent":1,"attempt":1,"site_id":2,"outcome":"success"}
        ]))
    );
    Ok(())
}

#[test]
fn value_only_helpers_keep_argument_origins_without_body_predicates() -> anyhow::Result<()> {
    // identity(x) := x; allow := [identity(input.a > 0), identity(input.b > 0)].
    let mut report = complete_rule_report();
    report.query.call_instance = Some(1);
    report.query_result = Value::from(vec![Value::from(false), Value::from(false)]);
    report.checks = vec![ConditionSite {
        site_id: 0,
        text: String::from("x"),
        kind: ConditionKind::Binding,
        location: Some(SourceLocation {
            file: String::from("p.rego"),
            line: 2,
            column: 10,
        }),
        operator: None,
    }];
    let rule = report.rules.first_mut().context("queried rule")?;
    rule.call_instance = 1;
    rule.result = ReportedValue::Known(report.query_result.clone());
    rule.definitions = vec![DefinitionExplanation {
        index: 0,
        body: 0,
        outcome: Outcome::Success,
        location: None,
        conditions: Vec::new(),
    }];
    rule.attempts = Some(vec![AttemptExplanation {
        attempt: 1,
        definition: 0,
        body: 0,
        outcome: Some(Outcome::Success),
        conditions: Some(Vec::new()),
    }]);
    rule.scopes = Some(Vec::new());
    rule.calls = Some(vec![
        CallUse {
            use_id: 1,
            call_instance: 2,
            attempt: Some(1),
            scope: None,
        },
        CallUse {
            use_id: 2,
            call_instance: 3,
            attempt: Some(1),
            scope: None,
        },
    ]);
    let template = rule.clone();
    let mut contributions = Vec::new();
    for (call_instance, key) in [(2, "a"), (3, "b")] {
        let mut argument = known(Value::from(false), None);
        argument.concrete_path = ConcretePath::NoPath;
        argument.origins = Some(CausalOrigins {
            paths: vec![ConcretePath::Captured {
                root: PathRoot::Input,
                segments: vec![PathSegment::Key(String::from(key))],
            }],
            complete: true,
        });
        let binding = ConditionExplanation {
            completed_scope: None,
            call_uses: None,
            site_id: 0,
            owner: ConditionOwner {
                rule: String::from("data.test.identity"),
                call_instance,
                attempt: Some(call_instance),
                scope: None,
            },
            outcome: Outcome::Success,
            left: Some(argument),
            right: None,
            witness: None,
            binding: Some(String::from("x")),
        };
        let mut helper = template.clone();
        helper.name = String::from("data.test.identity");
        helper.call_instance = call_instance;
        helper.kind = RuleKind::Function;
        helper.result = ReportedValue::Known(Value::from(false));
        helper.attempts = Some(vec![AttemptExplanation {
            attempt: call_instance,
            definition: 0,
            body: 0,
            outcome: Some(Outcome::Success),
            conditions: Some(vec![binding.clone()]),
        }]);
        helper.calls = Some(Vec::new());
        contributions.push(binding);
        report.rules.push(helper);
    }
    report.rules.first_mut().context("queried rule")?.results = Some(vec![ResultExplanation::new(
        None,
        ReportedValue::Known(report.query_result.clone()),
        Count::Exact(1),
        Vec::new(),
        vec![Derivation {
            call_uses: None,
            definition: 0,
            body: 0,
            attempt: Some(1),
            conditionality: Some(Conditionality::Concrete),
            conditions: contributions,
            bindings: Some(Vec::new()),
        }],
    )
    .context("valid proof count")?]);
    let json = serde_json::to_value(&report)?;
    for (index, call_instance, key) in [(1, 2, "a"), (2, 3, "b")] {
        let helper = json.pointer(&format!("/rules/{index}")).context("helper")?;
        assert_eq!(helper.get("result"), Some(&serde_json::json!(false)));
        assert_eq!(
            helper.pointer("/definitions/0/conditions"),
            Some(&serde_json::json!([]))
        );
        assert_eq!(
            helper.pointer("/attempts/0/conditions"),
            Some(&serde_json::json!([{
                "site_id":0,
                "owner":{"rule":"data.test.identity","call_instance":call_instance,"attempt":call_instance},
                "outcome":"success","binding":"x",
                "left":{"concrete_path":{"status":"no_path"},"value":false,
                    "origins":{"paths":[{"status":"captured","root":"input","segments":[{"key":key}]}],"complete":true}}
            }]))
        );
        assert_eq!(
            json.pointer(&format!(
                "/rules/0/results/0/proofs/0/conditions/{}",
                index - 1
            )),
            helper.pointer("/attempts/0/conditions/0"),
        );
    }
    assert_eq!(
        json.pointer("/rules/0/calls"),
        Some(&serde_json::json!([
            {"use_id":1,"call_instance":2,"attempt":1},
            {"use_id":2,"call_instance":3,"attempt":1}
        ]))
    );
    Ok(())
}

#[test]
fn uncaptured_bindings_are_not_an_empty_contributor_set() -> Result<(), serde_json::Error> {
    let mut proof = Derivation {
        call_uses: None,
        definition: 0,
        body: 0,
        attempt: None,
        conditionality: None,
        conditions: Vec::new(),
        bindings: None,
    };
    assert_eq!(
        serde_json::to_value(&proof)?,
        serde_json::json!({"definition":0,"body":0,"conditions":[]})
    );
    proof.bindings = Some(Vec::new());
    assert_eq!(
        serde_json::to_value(&proof)?,
        serde_json::json!({"definition":0,"body":0,"conditions":[],"bindings":[]})
    );
    Ok(())
}

#[test]
fn computed_origins_preserve_identity_without_claiming_source_values(
) -> Result<(), serde_json::Error> {
    let mut operand = known(Value::from(true), None);
    operand.concrete_path = ConcretePath::NoPath;
    operand.origins = Some(CausalOrigins {
        paths: alloc::vec![ConcretePath::Captured {
            root: PathRoot::Context,
            segments: alloc::vec![
                PathSegment::Key(String::from("resourceGroup")),
                PathSegment::Key(String::from("location"))
            ],
        }],
        complete: true,
    });
    assert_eq!(
        serde_json::to_value(&operand)?,
        serde_json::json!({
            "concrete_path":{"status":"no_path"},"value":true,
            "origins":{"paths":[{"status":"captured","root":"context",
                "segments":[{"key":"resourceGroup"},{"key":"location"}]}],"complete":true}
        })
    );
    operand.origins = Some(CausalOrigins {
        paths: alloc::vec![ConcretePath::Redacted],
        complete: false,
    });
    assert_eq!(
        serde_json::to_value(&operand)?.get("origins"),
        Some(&serde_json::json!({"paths":[{"status":"redacted"}],"complete":false}))
    );
    operand.origins = Some(CausalOrigins {
        paths: Vec::new(),
        complete: false,
    });
    let incomplete = serde_json::to_value(&operand)?;
    operand.origins = Some(CausalOrigins {
        paths: Vec::new(),
        complete: true,
    });
    let no_inputs = serde_json::to_value(&operand)?;
    operand.origins = None;
    let uncaptured = serde_json::to_value(&operand)?;
    assert_ne!(incomplete, no_inputs);
    assert_ne!(uncaptured, no_inputs);
    assert!(uncaptured.get("origins").is_none());
    Ok(())
}

#[test]
fn partial_object_conflict_keys_keep_redaction_and_elision() -> Result<(), serde_json::Error> {
    for (key, expected) in [
        (None, serde_json::json!({})),
        (
            Some(ReportedValue::Known(Value::from("env"))),
            serde_json::json!({"key":"env"}),
        ),
        (
            Some(ReportedValue::Redacted),
            serde_json::json!({"key_redacted":true}),
        ),
        (
            Some(ReportedValue::Elided),
            serde_json::json!({"key_elided":true}),
        ),
    ] {
        let conflict = RuleOutcome::Conflict {
            values: alloc::vec![
                ReportedValue::Known(Value::from("a")),
                ReportedValue::Known(Value::from("b"))
            ],
            key,
        };
        let mut wanted =
            serde_json::json!({"status":"conflict","values":[{"value":"a"},{"value":"b"}]});
        if let (Some(wanted), Some(expected)) = (wanted.as_object_mut(), expected.as_object()) {
            wanted.extend(expected.clone());
        }
        assert_eq!(serde_json::to_value(&conflict)?, wanted);
    }
    Ok(())
}
