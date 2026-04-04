// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Recursive-descent JSON parser for Azure Policy rule constraints.
//!
//! Parses Azure Policy JSON directly from [`Lexer`] tokens, building span-annotated
//! AST nodes in a single pass. No intermediate `serde_json::Value` is created.
//!
//! The parser is policy-aware: when parsing JSON objects, it dispatches on key names
//! (`allOf`, `anyOf`, `not`, `field`, `value`, `count`, operator names) to build
//! the appropriate AST nodes.

mod constraint;
mod core;
mod error;

pub(super) use self::core::json_unescape;
pub use error::ParseError;

use alloc::string::ToString as _;

use crate::lexer::{Source, TokenKind};

use super::ast::{Constraint, FieldKind, OperatorKind};
use super::expr::ExprParser;

use self::core::Parser;

// ============================================================================
// Public API
// ============================================================================

/// Parse a standalone constraint from a JSON source.
///
/// A constraint is one of:
/// - Logical combinator: `{ "allOf": [...] }`, `{ "anyOf": [...] }`, `{ "not": {...} }`
/// - Leaf condition: `{ "field": "...", "equals": "..." }`
/// - Count condition: `{ "count": { "field": "..." }, "greater": 0 }`
pub fn parse_constraint(source: &Source) -> Result<Constraint, ParseError> {
    let mut parser = Parser::new(source)?;
    let constraint = parser.parse_constraint()?;

    if parser.tok.0 != TokenKind::Eof {
        return Err(ParseError::UnexpectedToken {
            span: parser.tok.1.clone(),
            expected: "end of input",
        });
    }

    Ok(constraint)
}

// ============================================================================
// Helper functions (used across submodules)
// ============================================================================

/// Check if a string is an ARM template expression (`[...]` but not `[[...`).
pub(super) fn is_template_expr(s: &str) -> bool {
    s.starts_with('[') && s.ends_with(']') && !s.starts_with("[[")
}

/// Checked `s[prefix_len..]`.
///
/// Callers guarantee bounds via a prior `starts_with` check on an ASCII
/// prefix whose byte-length equals `prefix_len`.
fn tail(s: &str, prefix_len: usize) -> &str {
    s.get(prefix_len..).unwrap_or_default()
}

/// Checked `s[prefix_len .. s.len() - suffix_len]`.
///
/// Callers guarantee bounds via prior `starts_with` / `ends_with` checks.
fn unwrap(s: &str, prefix_len: usize, suffix_len: usize) -> &str {
    let end = s.len().saturating_sub(suffix_len);
    s.get(prefix_len..end).unwrap_or_default()
}

/// Classify a field string into a [`FieldKind`].
pub(super) fn classify_field(
    text: &str,
    span: &crate::lexer::Span,
) -> Result<FieldKind, ParseError> {
    let lower = text.to_lowercase();
    match lower.as_str() {
        "type" => Ok(FieldKind::Type),
        "id" => Ok(FieldKind::Id),
        "kind" => Ok(FieldKind::Kind),
        "name" => Ok(FieldKind::Name),
        "location" => Ok(FieldKind::Location),
        "fullname" => Ok(FieldKind::FullName),
        "tags" => Ok(FieldKind::Tags),
        "identity.type" => Ok(FieldKind::IdentityType),
        _ if lower.starts_with("identity.") => Ok(FieldKind::IdentityField(
            tail(text, "identity.".len()).into(),
        )),
        "apiversion" => Ok(FieldKind::ApiVersion),
        _ if lower.starts_with("tags.") => Ok(FieldKind::Tag(tail(text, "tags.".len()).into())),
        _ if lower.starts_with("tags['") && text.ends_with("']") => Ok(FieldKind::Tag(
            unwrap(text, "tags['".len(), "']".len()).into(),
        )),
        // Tags[tagName] — bracket notation without quotes.
        // Tag name is everything between the first '[' and the LAST ']'.
        // e.g. Tags[Dept.Name]] → tag name "Dept.Name]"
        // Exclude tags[*] which is a wildcard iteration, not a tag name.
        _ if lower.starts_with("tags[") && text.ends_with(']') && !text.contains("[*]") => Ok(
            FieldKind::Tag(unwrap(text, "tags[".len(), "]".len()).into()),
        ),
        _ if is_template_expr(text) => {
            let inner = unwrap(text, 1, 1);
            let expr = ExprParser::parse_from_brackets(inner, span).map_err(|e| {
                ParseError::ExprParse {
                    span: span.clone(),
                    message: e.to_string(),
                }
            })?;
            Ok(FieldKind::Expr(expr))
        }
        _ => Ok(FieldKind::Alias(text.into())),
    }
}

/// Try to parse a lowercase key as an operator kind.
pub(super) fn parse_operator_kind(key: &str) -> Option<OperatorKind> {
    match key {
        "contains" => Some(OperatorKind::Contains),
        "containskey" => Some(OperatorKind::ContainsKey),
        "equals" => Some(OperatorKind::Equals),
        "greater" => Some(OperatorKind::Greater),
        "greaterorequals" => Some(OperatorKind::GreaterOrEquals),
        "exists" => Some(OperatorKind::Exists),
        "in" => Some(OperatorKind::In),
        "less" => Some(OperatorKind::Less),
        "lessorequals" => Some(OperatorKind::LessOrEquals),
        "like" => Some(OperatorKind::Like),
        "match" => Some(OperatorKind::Match),
        "matchinsensitively" => Some(OperatorKind::MatchInsensitively),
        "notcontains" => Some(OperatorKind::NotContains),
        "notcontainskey" => Some(OperatorKind::NotContainsKey),
        "notequals" => Some(OperatorKind::NotEquals),
        "notin" => Some(OperatorKind::NotIn),
        "notlike" => Some(OperatorKind::NotLike),
        "notmatch" => Some(OperatorKind::NotMatch),
        "notmatchinsensitively" => Some(OperatorKind::NotMatchInsensitively),
        _ => None,
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]
mod tests {
    use super::*;

    fn dummy_span() -> crate::lexer::Span {
        let source =
            crate::lexer::Source::from_contents("<test>".into(), alloc::string::String::new())
                .unwrap();
        crate::lexer::Span {
            source,
            line: 1,
            col: 1,
            start: 0,
            end: 0,
        }
    }

    #[test]
    fn test_is_template_expr() {
        assert!(is_template_expr("[field('type')]"));
        assert!(is_template_expr("[concat('a', 'b')]"));
        assert!(!is_template_expr("[[escaped]"));
        assert!(!is_template_expr("not-an-expr"));
        assert!(!is_template_expr("[no-end-bracket"));
    }

    #[test]
    fn test_classify_field_builtin_names() {
        let span = dummy_span();
        assert!(matches!(classify_field("type", &span), Ok(FieldKind::Type)));
        assert!(matches!(classify_field("Type", &span), Ok(FieldKind::Type)));
        assert!(matches!(classify_field("name", &span), Ok(FieldKind::Name)));
        assert!(matches!(
            classify_field("location", &span),
            Ok(FieldKind::Location)
        ));
    }

    #[test]
    fn test_classify_field_alias() {
        let span = dummy_span();
        match classify_field("Microsoft.Compute/virtualMachines/storageProfile", &span) {
            Ok(FieldKind::Alias(a)) => {
                assert_eq!(a, "Microsoft.Compute/virtualMachines/storageProfile");
            }
            other => panic!("expected Alias, got {:?}", other),
        }
    }

    #[test]
    fn test_classify_field_expression() {
        let span = dummy_span();
        match classify_field("[field('type')]", &span) {
            Ok(FieldKind::Expr(_)) => {}
            other => panic!("expected Expr, got {:?}", other),
        }
    }

    #[test]
    fn test_classify_field_double_bracket_not_expr() {
        // [[escaped] should NOT be parsed as an expression.
        let span = dummy_span();
        match classify_field("[[escaped]", &span) {
            Ok(FieldKind::Alias(a)) => assert_eq!(a, "[[escaped]"),
            other => panic!("expected Alias, got {:?}", other),
        }
    }
}
