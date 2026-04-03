// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Constraint parsing: logical combinators, leaf conditions, and count blocks.

use alloc::boxed::Box;
use alloc::string::String;
use alloc::vec::Vec;

use crate::lexer::Span;

use crate::languages::azure_policy::ast::{
    Condition, Constraint, CountNode, FieldNode, JsonValue, Lhs, NameNode, OperatorNode,
};

use super::classify_field;
use super::core::{CountInner, EntryValue, Parser};
use super::error::ParseError;
use super::parse_operator_kind;

/// Set `slot` to `val`, returning a [`ParseError::DuplicateKey`] if it was already set.
fn set_once<T>(slot: &mut Option<T>, val: T, key: &str, span: &Span) -> Result<(), ParseError> {
    if slot.is_some() {
        return Err(ParseError::DuplicateKey {
            span: span.clone(),
            key: String::from(key),
        });
    }
    *slot = Some(val);
    Ok(())
}

impl<'source> Parser<'source> {
    /// Parse a constraint (a JSON object: logical combinator or leaf condition).
    pub fn parse_constraint(&mut self) -> Result<Constraint, ParseError> {
        let open = self.expect_symbol("{")?;
        let mut entries: Vec<(Span, String, EntryValue)> = Vec::new();

        if self.token_text() != "}" {
            loop {
                let (key_span, key) = self.expect_string()?;
                self.expect_symbol(":")?;
                let key_lower = key.to_lowercase();

                let value = match key_lower.as_str() {
                    "allof" | "anyof" => {
                        if self.token_text() != "[" {
                            return Err(ParseError::LogicalOperatorNotArray {
                                span: key_span,
                                operator: key,
                            });
                        }
                        EntryValue::ConstraintArray(self.parse_constraint_array()?)
                    }
                    "not" => EntryValue::SingleConstraint(self.parse_constraint()?),
                    "count" => EntryValue::CountInner(Box::new(self.parse_count_inner()?)),
                    _ => EntryValue::Json(self.parse_json_value()?),
                };

                // Detect duplicate keys during collection (case-insensitive).
                if entries
                    .iter()
                    .any(|entry| entry.1.eq_ignore_ascii_case(&key))
                {
                    return Err(ParseError::DuplicateKey {
                        span: key_span,
                        key,
                    });
                }

                entries.push((key_span, key, value));

                if self.token_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        let close = self.expect_symbol("}")?;
        let span = Span {
            source: open.source.clone(),
            line: open.line,
            col: open.col,
            start: open.start,
            end: close.end,
        };

        Self::build_constraint(span, entries)
    }

    /// Parse a `[constraint, constraint, ...]` array for `allOf`/`anyOf`.
    fn parse_constraint_array(&mut self) -> Result<Vec<Constraint>, ParseError> {
        self.expect_symbol("[")?;
        let mut constraints = Vec::new();
        if self.token_text() != "]" {
            constraints.push(self.parse_constraint()?);
            while self.token_text() == "," {
                self.advance()?;
                constraints.push(self.parse_constraint()?);
            }
        }
        self.expect_symbol("]")?;
        Ok(constraints)
    }

    /// Dispatch on collected entries to build the appropriate constraint.
    fn build_constraint(
        span: Span,
        entries: Vec<(Span, String, EntryValue)>,
    ) -> Result<Constraint, ParseError> {
        // Check for logical operators with extra keys.
        for entry in entries.iter() {
            let lower = entry.1.to_lowercase();
            if matches!(lower.as_str(), "allof" | "anyof" | "not") && entries.len() > 1 {
                return Err(ParseError::ExtraKeysInLogical {
                    span: entry.0.clone(),
                    operator: entry.1.clone(),
                });
            }
        }

        // Single-entry logical operators.
        if entries.len() == 1 {
            // Safe: we just checked len() == 1.
            let mut entries = entries;
            let (key_span, key, value) = entries
                .pop()
                .ok_or_else(|| ParseError::MissingLhsOperand { span: span.clone() })?;
            match key.to_lowercase().as_str() {
                "allof" => {
                    // Non-array values are caught during parsing (LogicalOperatorNotArray).
                    let EntryValue::ConstraintArray(constraints) = value else {
                        return Err(ParseError::LogicalOperatorNotArray {
                            span: key_span,
                            operator: key,
                        });
                    };
                    return Ok(Constraint::AllOf { span, constraints });
                }
                "anyof" => {
                    let EntryValue::ConstraintArray(constraints) = value else {
                        return Err(ParseError::LogicalOperatorNotArray {
                            span: key_span,
                            operator: key,
                        });
                    };
                    return Ok(Constraint::AnyOf { span, constraints });
                }
                "not" => {
                    let EntryValue::SingleConstraint(constraint) = value else {
                        // `not` is always parsed as SingleConstraint in parse_constraint,
                        // so this branch is structurally unreachable.
                        return Err(ParseError::UnexpectedToken {
                            span: key_span,
                            expected: "constraint for 'not'",
                        });
                    };
                    return Ok(Constraint::Not {
                        span,
                        constraint: Box::new(constraint),
                    });
                }
                _ => {
                    return Self::build_condition(span, alloc::vec![(key_span, key, value)]);
                }
            }
        }

        Self::build_condition(span, entries)
    }

    /// Build a leaf condition from collected object entries.
    fn build_condition(
        span: Span,
        entries: Vec<(Span, String, EntryValue)>,
    ) -> Result<Constraint, ParseError> {
        let mut field: Option<(Span, JsonValue)> = None;
        let mut value: Option<(Span, JsonValue)> = None;
        let mut count: Option<(Span, Box<CountInner>)> = None;
        let mut operator: Option<OperatorNode> = None;
        let mut rhs: Option<JsonValue> = None;

        for (key_span, key, entry_value) in entries {
            match key.to_lowercase().as_str() {
                "field" => {
                    let EntryValue::Json(jv) = entry_value else {
                        return Err(ParseError::UnexpectedToken {
                            span: key_span,
                            expected: "JSON value for 'field'",
                        });
                    };
                    set_once(&mut field, (key_span.clone(), jv), &key, &key_span)?;
                }
                "value" => {
                    let EntryValue::Json(jv) = entry_value else {
                        return Err(ParseError::UnexpectedToken {
                            span: key_span,
                            expected: "JSON value for 'value'",
                        });
                    };
                    set_once(&mut value, (key_span.clone(), jv), &key, &key_span)?;
                }
                "count" => {
                    let EntryValue::CountInner(ci) = entry_value else {
                        return Err(ParseError::UnexpectedToken {
                            span: key_span,
                            expected: "object for 'count'",
                        });
                    };
                    set_once(&mut count, (key_span.clone(), ci), &key, &key_span)?;
                }
                _ => {
                    if let Some(op_kind) = parse_operator_kind(&key.to_lowercase()) {
                        let EntryValue::Json(jv) = entry_value else {
                            return Err(ParseError::UnexpectedToken {
                                span: key_span,
                                expected: "JSON value for operator",
                            });
                        };
                        if operator.is_some() {
                            return Err(ParseError::MultipleOperators { span: key_span });
                        }
                        operator = Some(OperatorNode {
                            span: key_span,
                            kind: op_kind,
                        });
                        rhs = Some(jv);
                    } else {
                        return Err(ParseError::UnrecognizedKey {
                            span: key_span,
                            key,
                        });
                    }
                }
            }
        }

        let operator =
            operator.ok_or_else(|| ParseError::MissingOperator { span: span.clone() })?;
        let rhs_json = rhs.ok_or_else(|| ParseError::MissingOperator { span: span.clone() })?;
        let rhs_value = Self::json_to_value_or_expr(rhs_json)?;

        let lhs = match (field, value, count) {
            (Some((_, fv)), None, None) => Lhs::Field(Self::json_to_field(fv)?),
            (None, Some((key_span, vv)), None) => Lhs::Value {
                key_span,
                value: Self::json_to_value_or_expr(vv)?,
            },
            (None, None, Some((_, ci))) => Lhs::Count(Self::finalize_count(*ci)?),

            (None, None, None) => {
                return Err(ParseError::MissingLhsOperand { span: span.clone() });
            }
            _ => {
                return Err(ParseError::MultipleLhsOperands { span: span.clone() });
            }
        };

        Ok(Constraint::Condition(Box::new(Condition {
            span,
            lhs,
            operator,
            rhs: rhs_value,
        })))
    }

    // ========================================================================
    // Count parsing
    // ========================================================================

    /// Parse the inner object of a `"count": { ... }` block.
    pub fn parse_count_inner(&mut self) -> Result<CountInner, ParseError> {
        let open = self.expect_symbol("{")?;

        let mut field: Option<(Span, JsonValue)> = None;
        let mut value: Option<(Span, JsonValue)> = None;
        let mut name: Option<(Span, JsonValue)> = None;
        let mut where_: Option<Constraint> = None;

        if self.token_text() != "}" {
            loop {
                let (key_span, key) = self.expect_string()?;
                self.expect_symbol(":")?;
                let key_lower = key.to_lowercase();

                match key_lower.as_str() {
                    "field" => {
                        let jv = self.parse_json_value()?;
                        set_once(&mut field, (key_span.clone(), jv), &key_lower, &key_span)?;
                    }
                    "value" => {
                        let jv = self.parse_json_value()?;
                        set_once(&mut value, (key_span.clone(), jv), &key_lower, &key_span)?;
                    }
                    "name" => {
                        let jv = self.parse_json_value()?;
                        set_once(&mut name, (key_span.clone(), jv), &key_lower, &key_span)?;
                    }
                    "where" => {
                        let c = self.parse_constraint()?;
                        set_once(&mut where_, c, &key_lower, &key_span)?;
                    }
                    _ => {
                        return Err(ParseError::UnrecognizedKey {
                            span: key_span,
                            key: key_lower,
                        });
                    }
                }

                if self.token_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        let close = self.expect_symbol("}")?;
        let span = Span {
            source: open.source.clone(),
            line: open.line,
            col: open.col,
            start: open.start,
            end: close.end,
        };

        Ok(CountInner {
            span,
            field,
            value,
            name,
            where_,
        })
    }

    // ========================================================================
    // Helpers
    // ========================================================================

    /// Convert a JSON value (expected to be a string) into a [`FieldNode`].
    pub fn json_to_field(jv: JsonValue) -> Result<FieldNode, ParseError> {
        let (span, text) = match jv {
            JsonValue::Str(span, text) => (span, text),
            other => {
                return Err(ParseError::UnexpectedToken {
                    span: other.span().clone(),
                    expected: "string for 'field' value",
                });
            }
        };
        let kind = classify_field(&text, &span)?;
        Ok(FieldNode { span, kind })
    }

    /// Finalize a [`CountInner`] into a [`CountNode`].
    pub fn finalize_count(ci: CountInner) -> Result<CountNode, ParseError> {
        let CountInner {
            span,
            field,
            value,
            name,
            where_,
        } = ci;
        let where_box = where_.map(Box::new);

        let name_node = match name {
            Some((key_span, jv)) => {
                if value.is_none() {
                    return Err(ParseError::MisplacedCountName { span: key_span });
                }
                match jv {
                    JsonValue::Str(name_span, text) => Some(NameNode {
                        span: name_span,
                        name: text,
                    }),
                    _ => {
                        return Err(ParseError::InvalidCountName {
                            span: jv.span().clone(),
                        });
                    }
                }
            }
            None => None,
        };

        match (field, value) {
            (None, None) => Err(ParseError::MissingCountCollection { span }),
            (Some((_, fv)), None) => {
                let field_node = Self::json_to_field(fv)?;
                Ok(CountNode::Field {
                    span,
                    field: field_node,
                    where_: where_box,
                })
            }
            (None, Some((_, vv))) => {
                let val = Self::json_to_value_or_expr(vv)?;
                Ok(CountNode::Value {
                    span,
                    value: val,
                    name: name_node,
                    where_: where_box,
                })
            }
            (Some(_), Some(_)) => Err(ParseError::MultipleCountCollections { span }),
        }
    }
}
