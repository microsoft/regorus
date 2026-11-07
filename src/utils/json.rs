// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Bounded JSON syntax decoding, without Rego Value's private-number convention.

use alloc::string::String;
use alloc::vec::Vec;
use core::fmt;

use serde::de::{self, MapAccess, SeqAccess, Visitor};
use serde::Deserializer as _;
use serde_json::value::RawValue;
use serde_json::{Map, Value};

use super::depth::DepthExceeded;
use super::limits::{check_memory_limit_if_needed, enforce_memory_limit, LimitError};

#[derive(Debug, thiserror::Error)]
pub enum JsonError {
    #[error(transparent)]
    Depth(#[from] DepthExceeded),
    #[error(transparent)]
    Limit(#[from] LimitError),
    #[error(transparent)]
    Syntax(#[from] serde_json::Error),
}

impl JsonError {
    // Keep builtin error classification's downcasts to the original limit types.
    #[cfg(feature = "jsonschema")]
    pub fn into_anyhow(self) -> anyhow::Error {
        match self {
            Self::Depth(error) => error.into(),
            Self::Limit(error) => error.into(),
            Self::Syntax(error) => error.into(),
        }
    }
}

/// Count actual containers before using RawValue's grammar scanner. This scan
/// allocates nothing and does not validate JSON; serde still owns the grammar,
/// string escapes, Unicode and number handling. Empty containers count too.
fn check_depth(source: &str, limit: usize) -> Result<(), DepthExceeded> {
    let mut depth = 0_usize;
    let mut in_string = false;
    let mut escaped = false;
    for byte in source.bytes() {
        if in_string {
            if escaped {
                escaped = false;
            } else {
                match byte {
                    b'\\' => escaped = true,
                    b'"' => in_string = false,
                    _ => {}
                }
            }
        } else {
            match byte {
                b'"' => in_string = true,
                b'[' | b'{' => {
                    if depth >= limit {
                        return Err(DepthExceeded(limit));
                    }
                    depth = depth.saturating_add(1);
                }
                b']' | b'}' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(())
}

/// Decode a schema or program envelope with a small caller-supplied container
/// budget (32 or 40). Never route structural objects through a Value visitor:
/// even serde_json::Value can mistake a literal private Number key for a numeric
/// token under arbitrary_precision.
pub fn from_str(source: &str, limit: usize) -> Result<Value, JsonError> {
    enforce_memory_limit()?;
    // This must precede all serde parsing, including borrowed RawValue scanning.
    check_depth(source, limit)?;
    let decoded = decode(source);
    enforce_memory_limit()?;
    decoded
}

// Each child is borrowed as raw JSON so its opening token unambiguously
// distinguishes real objects from serde's synthetic arbitrary-precision map.
// Re-scanning is bounded by the preflight depth budget, not the input width.
fn decode(source: &str) -> Result<Value, JsonError> {
    check_memory_limit_if_needed()?;
    let token = source
        .trim_start_matches([' ', '\t', '\n', '\r'])
        .as_bytes()
        .first()
        .copied();
    let mut failure = None;
    let mut deserializer = serde_json::Deserializer::from_str(source);
    let visitor = ContainerVisitor {
        failure: &mut failure,
    };
    let result = match token {
        Some(b'{') => deserializer.deserialize_map(visitor),
        Some(b'[') => deserializer.deserialize_seq(visitor),
        // A scalar cannot contain the ambiguous private-number object syntax.
        // This preserves the active serde_json feature set's numeric precision.
        _ => return serde_json::from_str(source).map_err(JsonError::from),
    };
    match result {
        Ok(value) => {
            deserializer.end()?;
            Ok(value)
        }
        Err(error) => Err(failure.unwrap_or(JsonError::Syntax(error))),
    }
}

struct ContainerVisitor<'a> {
    failure: &'a mut Option<JsonError>,
}

impl ContainerVisitor<'_> {
    fn capture<E: de::Error>(&mut self, error: JsonError) -> E {
        let reported = E::custom(&error);
        *self.failure = Some(error);
        reported
    }

    fn checkpoint<E: de::Error>(&mut self) -> Result<(), E> {
        check_memory_limit_if_needed().map_err(|error| self.capture(JsonError::Limit(error)))
    }

    fn child<E: de::Error>(&mut self, raw: &RawValue) -> Result<Value, E> {
        decode(raw.get()).map_err(|error| self.capture(error))
    }
}

impl<'de> Visitor<'de> for ContainerVisitor<'_> {
    type Value = Value;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("a JSON object or array")
    }

    fn visit_map<A: MapAccess<'de>>(mut self, mut access: A) -> Result<Value, A::Error> {
        let mut values = Map::new();
        while let Some(key) = access.next_key::<String>()? {
            self.checkpoint()?;
            let raw = access.next_value::<&RawValue>()?;
            let value = self.child(raw)?;
            values.insert(key, value);
            self.checkpoint()?;
        }
        Ok(Value::Object(values))
    }

    fn visit_seq<A: SeqAccess<'de>>(mut self, mut access: A) -> Result<Value, A::Error> {
        let mut values = Vec::new();
        while let Some(raw) = access.next_element::<&RawValue>()? {
            values.push(self.child(raw)?);
            self.checkpoint()?;
        }
        Ok(Value::Array(values))
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::expect_used)]

    use super::*;
    use alloc::format;
    use alloc::string::ToString as _;

    #[test]
    fn literal_objects_are_never_number_tokens() {
        for source in [
            r#"{"$serde_json::private::Number":"123"}"#,
            r#"{"$serde_json::private::Number":"not a number","sibling":true}"#,
            r#"{"\u0024serde_json::private::Number":{"nested":[]}}"#,
        ] {
            let decoded = from_str(source, 32).unwrap();
            assert!(decoded.is_object());
            assert!(decoded.get("$serde_json::private::Number").is_some());
            // Reparse with the structural helper, not serde_json::Value's visitor.
            assert_eq!(from_str(&decoded.to_string(), 32).unwrap(), decoded);
            let array = format!("[{source}]");
            let decoded_array = from_str(&array, 32).unwrap();
            assert_eq!(decoded_array.get(0), Some(&decoded));
        }
    }

    #[test]
    fn numeric_tokens_keep_serde_json_precision() {
        for number in [
            "0",
            "-0",
            "-123",
            "-1.234567890123456789",
            "18446744073709551615",
            "1234567890123456789012345678901234567890",
            "1e300",
            "-9.876543210987654321e1000",
            "1e-1000",
        ] {
            // Without arbitrary_precision, out-of-range floats are rejected;
            // with it, even large exponents must keep the original Number.
            let expected = serde_json::from_str::<Value>(number);
            let decoded = from_str(&format!(r#"{{"number":{number}}}"#), 32);
            match expected {
                Ok(expected) => {
                    assert!(expected.is_number());
                    assert_eq!(decoded.unwrap().get("number"), Some(&expected), "{number}");
                    assert_eq!(from_str(number, 0).unwrap(), expected, "{number}");
                }
                Err(_) => assert!(matches!(decoded, Err(JsonError::Syntax(_)))),
            }
        }
    }

    #[test]
    fn counts_empty_containers_and_ignores_quoted_delimiters() {
        for limit in [0_usize, 1, 32, 40] {
            for object in [false, true] {
                for depth in [limit, limit.saturating_add(1)] {
                    let source = if depth == 0 {
                        String::from("null")
                    } else if object {
                        format!(
                            "{}{}{}",
                            r#"{"key":"#.repeat(depth.saturating_sub(1)),
                            "{}",
                            "}".repeat(depth.saturating_sub(1))
                        )
                    } else {
                        format!("{}{}", "[".repeat(depth), "]".repeat(depth))
                    };
                    let decoded = from_str(&source, limit);
                    if depth == limit {
                        assert!(decoded.is_ok(), "{source}");
                    } else {
                        assert!(matches!(
                            decoded,
                            Err(JsonError::Depth(DepthExceeded(actual))) if actual == limit
                        ));
                    }
                }
            }
        }
        for text in [
            r#""[{}] \" quote \\ [""#,
            r#""\u005b\u007b\u0022""#,
            r#""\\\\\"[{}]""#,
        ] {
            assert_eq!(
                from_str(text, 0).unwrap(),
                serde_json::from_str::<Value>(text).unwrap()
            );
        }
        // Reject before serde's raw scanner can allocate scratch for an
        // arbitrarily deep malformed prefix.
        assert!(matches!(
            from_str(&"[".repeat(100_000), 40),
            Err(JsonError::Depth(DepthExceeded(40)))
        ));
    }

    #[test]
    fn serde_still_validates_the_complete_json_grammar() {
        for malformed in [
            "",
            "[",
            "{",
            "[1,]",
            r#"{"key":}"#,
            r#"{"key":"\uD800"}"#,
            r#"{"key":"\x00"}"#,
            "01",
            "true false",
            "{}[]",
            "[}",
        ] {
            assert!(matches!(from_str(malformed, 32), Err(JsonError::Syntax(_))));
        }
        assert_eq!(
            from_str(r#"{"key":1,"key":2}"#, 32).unwrap().get("key"),
            Some(&Value::from(2))
        );
    }

    #[cfg(feature = "jsonschema")]
    #[test]
    fn anyhow_mapping_preserves_limit_types() {
        let depth = from_str("[]", 0).unwrap_err().into_anyhow();
        assert_eq!(
            depth.downcast_ref::<DepthExceeded>(),
            Some(&DepthExceeded(0))
        );

        let limit = LimitError::MemoryLimitExceeded { usage: 2, limit: 1 };
        let mut failure = None;
        let mut visitor = ContainerVisitor {
            failure: &mut failure,
        };
        let _: serde_json::Error = visitor.capture(JsonError::Limit(limit));
        assert_eq!(
            failure.unwrap().into_anyhow().downcast_ref::<LimitError>(),
            Some(&limit)
        );
    }
}
