// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(any(feature = "jsonschema", feature = "rvm"))]

#[cfg(feature = "jsonschema")]
use regorus::{Engine, Value};

#[cfg(feature = "jsonschema")]
fn schema_engine(strict: bool) -> Engine {
    let mut engine = Engine::new();
    engine.set_strict_builtin_errors(strict);
    engine
        .add_policy(
            "structural-json.rego".into(),
            "package structural_json\nverified := json.verify_schema(input)[0]\nmatched := json.match_schema(123, input)[0]".into(),
        )
        .unwrap();
    engine
}

#[cfg(feature = "jsonschema")]
#[test]
fn schema_strings_preserve_number_named_keywords() {
    for strict in [false, true] {
        let mut engine = schema_engine(strict);
        for schema in [
            r#"{"$serde_json::private::Number":"123"}"#,
            r#"{"$serde_json::private::Number":"123","type":"number"}"#,
            r#"{"properties":{"payload":{"$serde_json::private::Number":"123"}}}"#,
            r#"{"allOf":[{"$serde_json::private::Number":"123"}]}"#,
            r#"{"$serde_json::private::Number":{"nested":[{},{"key":"value"}]}}"#,
        ] {
            engine.set_input(Value::from(schema));
            for rule in ["verified", "matched"] {
                assert_eq!(
                    engine
                        .eval_rule(format!("data.structural_json.{rule}"))
                        .unwrap(),
                    Value::Bool(true),
                    "{schema}, strict={strict}, rule={rule}"
                );
            }
        }
    }
}

#[cfg(feature = "jsonschema")]
#[test]
fn schema_const_with_number_named_object_rejects_numeric_document() {
    for strict in [false, true] {
        let mut engine = Engine::new();
        engine.set_strict_builtin_errors(strict);
        engine
            .add_policy(
                "structural-json-const.rego".into(),
                r#"
package structural_json_const
string_schema_matches := json.match_schema(1, input)[0]
object_schema_matches := json.match_schema(1, {"const": {"$serde_json::private::Number": "1"}})[0]
numeric_const_matches := json.match_schema(1, "{\"const\":1}")[0]
"#
                .into(),
            )
            .unwrap();
        engine.set_input(Value::from(
            r#"{"const":{"$serde_json::private::Number":"1"}}"#,
        ));

        for (rule, expected) in [
            ("string_schema_matches", false),
            ("object_schema_matches", false),
            ("numeric_const_matches", true),
        ] {
            assert_eq!(
                engine
                    .eval_rule(format!("data.structural_json_const.{rule}"))
                    .unwrap(),
                Value::Bool(expected),
                "strict={strict}, rule={rule}"
            );
        }
    }
}

#[cfg(feature = "jsonschema")]
#[test]
fn schema_strings_keep_container_limit_and_json_escaping() {
    for strict in [false, true] {
        let mut engine = schema_engine(strict);
        for depth in [32, 33] {
            // Count the empty innermost object, not just its nonempty parents.
            let schema = format!(
                "{}{}{}",
                r#"{"extension":"#.repeat(depth - 1),
                "{}",
                "}".repeat(depth - 1)
            );
            engine.set_input(Value::from(schema));
            let result = engine.eval_rule("data.structural_json.verified".into());
            if depth == 32 {
                assert_eq!(result.unwrap(), Value::Bool(true));
            } else {
                assert!(format!("{:#}", result.unwrap_err()).contains("nesting limit 32"));
            }
        }
        for schema in [
            r#"{"description":"[{}] \"quoted\" \\","type":"number"}"#,
            r#"{"description":"\u005b\u007b\u0022","minimum":-1.25,"maximum":1e30}"#,
        ] {
            engine.set_input(Value::from(schema));
            assert_eq!(
                engine
                    .eval_rule("data.structural_json.matched".into())
                    .unwrap(),
                Value::Bool(true)
            );
        }
    }
}

#[cfg(feature = "rvm")]
#[test]
fn program_annotations_preserve_number_named_keys() {
    use regorus::rvm::program::Program;
    use regorus::Value;
    use std::collections::BTreeMap;

    for value in [
        Value::from("123"),
        Value::from(vec![Value::from("123")]),
        Value::from(BTreeMap::from([(
            Value::from("nested"),
            Value::from(vec![Value::new_object()]),
        )])),
    ] {
        for sibling in [false, true] {
            let mut program = Program::new();
            program
                .metadata
                .annotations
                .insert("$serde_json::private::Number".into(), value.clone());
            if sibling {
                program
                    .metadata
                    .annotations
                    .insert("sibling".into(), Value::from("retained"));
            }
            let json = program.serialize_json().unwrap();
            let decoded = Program::deserialize_json(&json).unwrap();
            assert_eq!(
                decoded.metadata.annotations, program.metadata.annotations,
                "{json}"
            );
        }
    }
}

#[cfg(feature = "rvm")]
#[test]
fn program_envelope_and_value_limits_remain_independent() {
    use regorus::rvm::program::Program;

    let base = Program::new().serialize_json().unwrap();
    for depth in [39, 40] {
        // The root envelope consumes one of the forty containers.
        let extension = format!("{}{}", "[".repeat(depth), "]".repeat(depth));
        let text = format!(
            r#"{{"extension":{extension},{}"#,
            base.strip_prefix('{').unwrap()
        );
        let result = Program::deserialize_json(&text);
        assert_eq!(result.is_ok(), depth == 39);
        if depth == 40 {
            assert!(result.unwrap_err().contains("nesting limit 40"));
        }
    }
    for depth in [32, 33] {
        let literals = format!("[{}null{}]", "[".repeat(depth), "]".repeat(depth));
        let mut envelope: serde_json::Value = serde_json::from_str(&base).unwrap();
        envelope["literals"] = serde_json::from_str(&literals).unwrap();
        assert_eq!(
            Program::deserialize_json(&envelope.to_string()).is_ok(),
            depth == 32
        );
    }
}
