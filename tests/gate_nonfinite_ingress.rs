// The value domain contains no non-finite number, and a host-supplied non-finite float fails closed.
//
// Every text path (YAML, JSON, numeric strings, `units.*`, the lexer) must reject NaN/Inf instead of
// admitting it, and `From<f64>` - which cannot return an error - must map NaN/+/-Inf to `Value::Null`
// rather than `Undefined`. The distinction is the whole point: an `Undefined` is a skipped rule body,
// so `not input.x` succeeds and a policy fails *open*; `Null` denies, and is JSON-representable, so
// `json.marshal` emits `null` instead of a sentinel string that a consumer may read as real data.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::print_stdout)]

use regorus::*;

fn is_number(v: &Value) -> bool {
    v.as_number().is_ok()
}

/// YAML 1.1 float spellings currently land in the value domain as non-finite Numbers.
#[test]
#[cfg(feature = "yaml")]
fn yaml_data_cannot_introduce_non_finite_numbers() {
    for text in [
        "a: .nan",
        "a: .NaN",
        "a: .INF",
        "a: .inf",
        "a: -.inf",
        "a: {b: .nan}",
        "a:\n  - .inf\n  - 1",
    ] {
        let res = Value::from_yaml_str(text);
        match res {
            Ok(v) => panic!("non-finite YAML input was accepted: {text:?} -> {v:?}"),
            Err(err) => {
                let msg = err.to_string();
                assert!(
                    msg.contains("nan")
                        || msg.contains("inf")
                        || msg.contains("number")
                        || msg.contains("float"),
                    "rejection message does not name the problem: {text:?} -> {msg}"
                );
            }
        }
    }
}

/// `1e400` in YAML never becomes a number: the only way to make it an error would be to reject
/// numeric-looking *strings*, which yaml_serde cannot distinguish. regorus yields `String("1e400")`
/// and OPA (v1.20.2) yields `{"a":"1e400"}` for the same data file, so it is pinned as a string.
#[test]
#[cfg(feature = "yaml")]
fn out_of_range_yaml_floats_stay_strings_like_opa() {
    for text in ["a: 1e400", "a: -1e400"] {
        let v = Value::from_yaml_str(text).unwrap_or_else(|err| panic!("{text:?} rejected: {err}"));
        match &v {
            Value::Object(o) => match o.get(&Value::String("a".into())) {
                Some(Value::String(s)) => assert!(
                    s.starts_with("1e400") || s.starts_with("-1e400"),
                    "{text:?} -> {s}"
                ),
                other => panic!("{text:?} should stay a string, got {other:?}"),
            },
            other => panic!("expected an object, got {other:?}"),
        }
    }
}

/// The infallible public conversion must not smuggle a non-finite Number into the domain.
#[test]
fn public_f64_conversion_keeps_the_domain_finite() {
    for f in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        let v = Value::from(f);
        assert!(
            !is_number(&v),
            "Value::from({f}) produced a Number in the domain: {v:?}"
        );
        assert!(
            matches!(v, Value::Null),
            "Value::from({f}) should be Null, got {v:?}"
        );
    }
}

/// The point of routing to `Null` rather than `Undefined`: a guard that tests for the presence of a
/// value must fail closed when the host supplied something unrepresentable.
#[test]
fn host_supplied_non_finite_fails_closed_in_a_guard() {
    let mut e = Engine::new();
    e.add_policy(
        "t.rego".to_string(),
        "package t\ndefault allow := false\nallow if not input.blocked\n".to_string(),
    )
    .expect("policy");

    for f in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        let mut input = Value::from_json_str(r#"{"blocked":1}"#).expect("input");
        {
            let o = input.as_object_mut().expect("object");
            *o.get_mut(&Value::String("blocked".into())).expect("key") = Value::from(f);
        }
        e.set_input(input);

        let r = e
            .eval_query("data.t.allow".to_string(), false)
            .expect("eval failed");
        let v = &r.result.first().expect("no solution").expressions[0].value;
        assert_eq!(
            *v,
            Value::Bool(false),
            "host-supplied {f} must not grant access, got {v:?}"
        );

        let m = e
            .eval_query("json.marshal(input)".to_string(), false)
            .expect("marshal failed");
        let j = &m.result.first().expect("no solution").expressions[0].value;
        assert_eq!(
            j.as_string().map(|s| s.to_string()).ok().as_deref(),
            Some("{\"blocked\":null}"),
            "non-finite must marshal as null, got {j:?}"
        );
    }
}

/// End-to-end: with the ingress closed, the set-collapse symptom is unreachable, and finite data
/// still behaves exactly as before.
#[test]
fn set_semantics_stay_coherent_for_reachable_data() {
    let mut e = Engine::new();
    // finite control: equal values dedup, distinct values do not
    e.set_input(Value::from_json_str(r#"{"a":1.0,"b":1,"c":7}"#).expect("finite JSON rejected"));
    let r = e
        .eval_query("count({input.a, input.b, input.c})".to_string(), false)
        .expect("errored");
    let v = &r.result.first().expect("no solution").expressions[0].value;
    assert_eq!(
        v.as_number().ok().and_then(|n| n.as_u64()),
        Some(2),
        "finite set semantics changed"
    );

    // The YAML ingress path that previously constructed the collapse case must reject it.
    #[cfg(feature = "yaml")]
    assert!(
        Value::from_yaml_str("a: .nan\nb: .nan\nc: 7\n").is_err(),
        "input that produced count==1 is still constructible"
    );
}

/// Finite YAML/JSON float spellings that are legal must be unaffected.
#[test]
#[cfg(feature = "yaml")]
fn finite_data_is_unchanged() {
    let v = Value::from_yaml_str("a: 1.5\nb: 1e3\nc: -.5\nd: 0.0\ne: -0.0\n")
        .expect("finite yaml rejected");
    for key in ["a", "b", "c", "d", "e"] {
        let got = match &v {
            Value::Object(o) => o.get(&Value::String(key.into())),
            other => panic!("expected an object, got {other:?}"),
        };
        assert!(
            matches!(got, Some(Value::Number(_))),
            "{key} lost its numeric value: {got:?}"
        );
    }

    // JSON text never carried non-finite literals — must stay that way.
    for text in ["{\"a\": NaN}", "{\"a\": Infinity}"] {
        assert!(
            Value::from_json_str(text).is_err(),
            "json accepted {text:?}"
        );
    }

    // With serde_json/arbitrary_precision, an out-of-f64-range exponent remains an exact,
    // finite integer. Without that feature serde_json may reject it; either outcome is valid.
    for text in ["1e400", "-1e400"] {
        if let Ok(value) = Value::from_json_str(text) {
            assert_eq!(
                value,
                Value::from_numeric_string(text).expect("exact numeric string rejected"),
                "json did not preserve {text} exactly"
            );
        }
    }

    let mut e = Engine::new();
    e.set_input(Value::from_yaml_str("a: 2.5\n").expect("finite yaml rejected"));
    let r = e
        .eval_query("input.a * 2".to_string(), false)
        .expect("errored");
    let v = &r.result.first().expect("no solution").expressions[0].value;
    assert_eq!(
        v.as_number().ok().and_then(|n| n.as_f64()),
        Some(5.0),
        "float arithmetic changed"
    );
}
