// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::pattern_type_mismatch)]

//! Free helper functions used by the Azure Policy compiler.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;

use anyhow::{anyhow, bail, Result};

use crate::languages::azure_policy::ast::{Expr, ExprLiteral, JsonValue, ObjectEntry};
use crate::Value;

/// Extract a string literal from an expression, or bail.
pub(super) fn extract_string_literal(expr: &Expr) -> Result<String> {
    match expr {
        Expr::Literal {
            value: ExprLiteral::String(value),
            ..
        } => Ok(value.clone()),
        other => bail!("expected string literal argument, found {:?}", other),
    }
}

/// Split a count field path at the `[*]` wildcard into `(prefix, optional_suffix)`.
pub(super) fn split_count_wildcard_path(path: &str) -> Result<(String, Option<String>)> {
    let wildcard_index = path
        .find("[*]")
        .ok_or_else(|| anyhow!("wildcard path must contain [*]: {}", path))?;

    let (prefix_str, rest) = path.split_at(wildcard_index);
    let prefix = prefix_str.trim_end_matches('.');
    if prefix.is_empty() {
        bail!(
            "wildcard path must have a non-empty prefix before [*]: {}",
            path
        );
    }
    let after_wildcard = rest.strip_prefix("[*]").ok_or_else(|| {
        anyhow!(
            "wildcard path could not be parsed after [*] split: {}",
            path
        )
    })?;
    let suffix_str = after_wildcard.trim_start_matches('.');
    let suffix = if suffix_str.is_empty() {
        None
    } else {
        Some(suffix_str.to_string())
    };

    Ok((prefix.to_string(), suffix))
}

/// Split a dotted path (without `[*]` wildcards) into its component segments.
///
/// Handles bracket notation:
///   - `tags['key']` → `["tags", "key"]`
///   - `properties['network-acls']` → `["properties", "network-acls"]`
///   - `properties.ipRules[0].value` → `["properties", "ipRules", "0", "value"]`
pub(super) fn split_path_without_wildcards(path: &str) -> Result<Vec<String>> {
    if path.trim().is_empty() {
        bail!("empty path");
    }
    if path.contains("[*]") {
        bail!(
            "wildcard field paths are not supported in this context: {}",
            path
        );
    }
    if path.ends_with('.') {
        bail!("path must not end with '.': {}", path);
    }

    let mut parts = Vec::new();
    let mut token = String::new();
    let mut bracket = String::new();
    let mut in_bracket = false;
    let mut after_bracket = false;

    for ch in path.chars() {
        match ch {
            '.' if !in_bracket => {
                let t = token.trim();
                if t.is_empty() && !after_bracket {
                    bail!("empty segment in path: {}", path);
                }
                if !t.is_empty() {
                    parts.push(t.to_string());
                }
                token.clear();
                after_bracket = false;
            }
            '[' => {
                if in_bracket {
                    bail!("nested brackets in path: {}", path);
                }
                in_bracket = true;
                after_bracket = false;
                let t = token.trim();
                if !t.is_empty() {
                    parts.push(t.to_string());
                }
                token.clear();
            }
            ']' => {
                if !in_bracket {
                    bail!("unexpected closing bracket in path: {}", path);
                }
                in_bracket = false;
                after_bracket = true;
                let cleaned = bracket
                    .trim()
                    .trim_matches('"')
                    .trim_matches('\'')
                    .to_string();
                if cleaned.is_empty() {
                    bail!("empty bracket in path: {}", path);
                }
                parts.push(cleaned);
                bracket.clear();
            }
            _ => {
                if in_bracket {
                    bracket.push(ch);
                } else {
                    if after_bracket {
                        bail!("expected '.' or '[' after bracket in path: {}", path);
                    }
                    token.push(ch);
                }
            }
        }
    }

    if in_bracket {
        bail!("unclosed bracket in path: {}", path);
    }

    let t = token.trim();
    if !t.is_empty() {
        parts.push(t.to_string());
    }

    Ok(parts)
}

/// Convert a parsed JSON value from the Azure Policy AST into a runtime [`Value`].
pub(super) fn json_value_to_runtime(value: &JsonValue) -> Result<Value> {
    match value {
        JsonValue::Null(_) => Ok(Value::Null),
        JsonValue::Bool(_, b) => Ok(Value::Bool(*b)),
        JsonValue::Number(_, raw) => {
            Value::from_numeric_string(raw).map_err(|_| anyhow!("invalid number literal: {}", raw))
        }
        JsonValue::Str(_, s) => {
            // Handle ARM template escape: `[[...` → `[...`
            s.strip_prefix("[[").map_or_else(
                || Ok(Value::from(s.clone())),
                |unescaped| Ok(Value::from(alloc::format!("[{unescaped}"))),
            )
        }
        JsonValue::Array(_, items) => {
            let mut out = Vec::with_capacity(items.len());
            for item in items {
                out.push(json_value_to_runtime(item)?);
            }
            Ok(Value::from(out))
        }
        JsonValue::Object(_, entries) => {
            let mut obj = Value::new_object();
            let map = obj.as_object_mut()?;
            for ObjectEntry {
                key,
                value: entry_value,
                ..
            } in entries
            {
                map.insert(
                    Value::from(key.clone()),
                    json_value_to_runtime(entry_value)?,
                );
            }
            Ok(obj)
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use alloc::vec;

    use crate::lexer::Source;

    use super::*;

    fn dummy_span() -> crate::lexer::Span {
        let source = Source::from_contents("test".into(), " ".into()).unwrap();
        crate::lexer::Span {
            source,
            line: 1,
            col: 1,
            start: 0,
            end: 0,
        }
    }

    // -----------------------------------------------------------------------
    // extract_string_literal
    // -----------------------------------------------------------------------

    #[test]
    fn extract_string_literal_ok() {
        let expr = Expr::Literal {
            span: dummy_span(),
            value: ExprLiteral::String("hello".into()),
        };
        assert_eq!(extract_string_literal(&expr).unwrap(), "hello");
    }

    #[test]
    fn extract_string_literal_number_err() {
        let expr = Expr::Literal {
            span: dummy_span(),
            value: ExprLiteral::Number("42".into()),
        };
        extract_string_literal(&expr).unwrap_err();
    }

    #[test]
    fn extract_string_literal_ident_err() {
        let expr = Expr::Ident {
            span: dummy_span(),
            name: "x".into(),
        };
        extract_string_literal(&expr).unwrap_err();
    }

    // -----------------------------------------------------------------------
    // json_value_to_runtime
    // -----------------------------------------------------------------------

    #[test]
    fn json_null() {
        let v = json_value_to_runtime(&JsonValue::Null(dummy_span())).unwrap();
        assert_eq!(v, Value::Null);
    }

    #[test]
    fn json_bool() {
        let v = json_value_to_runtime(&JsonValue::Bool(dummy_span(), true)).unwrap();
        assert_eq!(v, Value::Bool(true));
    }

    #[test]
    fn json_number_int() {
        let v = json_value_to_runtime(&JsonValue::Number(dummy_span(), "42".into())).unwrap();
        assert_eq!(v, Value::from(42_i64));
    }

    #[test]
    fn json_number_float() {
        let v = json_value_to_runtime(&JsonValue::Number(dummy_span(), "1.5".into())).unwrap();
        assert_eq!(v, Value::from(1.5_f64));
    }

    #[test]
    fn json_number_invalid() {
        json_value_to_runtime(&JsonValue::Number(dummy_span(), "abc".into())).unwrap_err();
    }

    #[test]
    fn json_string() {
        let v = json_value_to_runtime(&JsonValue::Str(dummy_span(), "hello".into())).unwrap();
        assert_eq!(v, Value::from("hello".to_string()));
    }

    #[test]
    fn json_string_double_bracket_escape() {
        let v = json_value_to_runtime(&JsonValue::Str(dummy_span(), "[[escaped]".into())).unwrap();
        assert_eq!(v, Value::from("[escaped]".to_string()));
    }

    #[test]
    fn json_array() {
        let arr = JsonValue::Array(
            dummy_span(),
            vec![
                JsonValue::Bool(dummy_span(), true),
                JsonValue::Null(dummy_span()),
            ],
        );
        let v = json_value_to_runtime(&arr).unwrap();
        let items = v.as_array().unwrap();
        assert_eq!(items.len(), 2);
    }

    #[test]
    fn json_object() {
        let obj = JsonValue::Object(
            dummy_span(),
            vec![ObjectEntry {
                key_span: dummy_span(),
                key: "k".into(),
                value: JsonValue::Bool(dummy_span(), false),
            }],
        );
        let v = json_value_to_runtime(&obj).unwrap();
        let map = v.as_object().unwrap();
        assert_eq!(map.len(), 1);
    }

    // -----------------------------------------------------------------------
    // split_count_wildcard_path
    // -----------------------------------------------------------------------

    #[test]
    fn wildcard_simple() {
        let (prefix, suffix) = split_count_wildcard_path("a.b[*].c").unwrap();
        assert_eq!(prefix, "a.b");
        assert_eq!(suffix.as_deref(), Some("c"));
    }

    #[test]
    fn wildcard_no_suffix() {
        let (prefix, suffix) = split_count_wildcard_path("a[*]").unwrap();
        assert_eq!(prefix, "a");
        assert_eq!(suffix, None);
    }

    #[test]
    fn wildcard_trailing_dot_prefix() {
        let (prefix, _) = split_count_wildcard_path("a.[*].c").unwrap();
        assert_eq!(prefix, "a");
    }

    #[test]
    fn wildcard_missing() {
        split_count_wildcard_path("a.b.c").unwrap_err();
    }

    #[test]
    fn wildcard_empty_prefix() {
        split_count_wildcard_path("[*].c").unwrap_err();
    }

    #[test]
    fn wildcard_nested() {
        let (prefix, suffix) = split_count_wildcard_path("a[*].b[*].c").unwrap();
        assert_eq!(prefix, "a");
        assert_eq!(suffix.as_deref(), Some("b[*].c"));
    }

    // -----------------------------------------------------------------------
    // split_path_without_wildcards
    // -----------------------------------------------------------------------

    #[test]
    fn path_simple_dotted() {
        assert_eq!(
            split_path_without_wildcards("a.b.c").unwrap(),
            vec!["a", "b", "c"]
        );
    }

    #[test]
    fn path_bracket_quoted() {
        assert_eq!(
            split_path_without_wildcards("tags['key']").unwrap(),
            vec!["tags", "key"]
        );
    }

    #[test]
    fn path_bracket_numeric() {
        assert_eq!(
            split_path_without_wildcards("a[0].b").unwrap(),
            vec!["a", "0", "b"]
        );
    }

    #[test]
    fn path_single_segment() {
        assert_eq!(split_path_without_wildcards("name").unwrap(), vec!["name"]);
    }

    #[test]
    fn path_empty() {
        split_path_without_wildcards("").unwrap_err();
    }

    #[test]
    fn path_whitespace_only() {
        split_path_without_wildcards("   ").unwrap_err();
    }

    #[test]
    fn path_trailing_dot() {
        split_path_without_wildcards("a.").unwrap_err();
    }

    #[test]
    fn path_leading_dot() {
        split_path_without_wildcards(".a").unwrap_err();
    }

    #[test]
    fn path_consecutive_dots() {
        split_path_without_wildcards("a..b").unwrap_err();
    }

    #[test]
    fn path_wildcard_rejected() {
        split_path_without_wildcards("a[*].b").unwrap_err();
    }

    #[test]
    fn path_nested_brackets() {
        split_path_without_wildcards("a[[0]]").unwrap_err();
    }

    #[test]
    fn path_stray_close_bracket() {
        split_path_without_wildcards("a]b").unwrap_err();
    }

    #[test]
    fn path_unclosed_bracket() {
        split_path_without_wildcards("a[0").unwrap_err();
    }

    #[test]
    fn path_empty_bracket() {
        split_path_without_wildcards("a[]").unwrap_err();
    }

    #[test]
    fn path_char_after_bracket_without_separator() {
        split_path_without_wildcards("a[0]b").unwrap_err();
    }
}
