// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Top-level policy rule parsing: `parse_policy_rule` and `parse_then_block`.

use crate::lexer::Span;

use crate::languages::azure_policy::ast::{
    Constraint, EffectKind, EffectNode, JsonValue, ObjectEntry, PolicyRule, ThenBlock,
};

use super::core::Parser;
use super::error::ParseError;

impl<'source> Parser<'source> {
    /// Parse the top-level `policyRule` object.
    pub fn parse_policy_rule(&mut self) -> Result<PolicyRule, ParseError> {
        let open = self.expect_symbol("{")?;

        let mut condition: Option<Constraint> = None;
        let mut then_block: Option<ThenBlock> = None;

        if self.token_text() != "}" {
            loop {
                let (key_span, key) = self.expect_string()?;
                self.expect_symbol(":")?;

                match key.to_lowercase().as_str() {
                    "if" => {
                        let c = self.parse_constraint()?;
                        Self::set_once(&mut condition, c, "if", &key_span)?;
                    }
                    "then" => {
                        let tb = self.parse_then_block()?;
                        Self::set_once(&mut then_block, tb, "then", &key_span)?;
                    }
                    _ => {
                        let _ = self.parse_json_value()?;
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

        let condition = condition.ok_or_else(|| ParseError::MissingKey {
            span: span.clone(),
            key: "if",
        })?;
        let then_block = then_block.ok_or_else(|| ParseError::MissingKey {
            span: span.clone(),
            key: "then",
        })?;

        Ok(PolicyRule {
            span,
            condition,
            then_block,
        })
    }

    /// Parse the `"then"` block.
    fn parse_then_block(&mut self) -> Result<ThenBlock, ParseError> {
        let open = self.expect_symbol("{")?;

        let mut effect: Option<EffectNode> = None;
        let mut details: Option<JsonValue> = None;
        let mut existence_condition: Option<Constraint> = None;

        if self.token_text() != "}" {
            loop {
                let (key_span, key) = self.expect_string()?;
                self.expect_symbol(":")?;

                match key.to_lowercase().as_str() {
                    "effect" => {
                        let (val_span, val_text) = self.expect_string()?;
                        let kind = match val_text.to_lowercase().as_str() {
                            "deny" => EffectKind::Deny,
                            "audit" => EffectKind::Audit,
                            "append" => EffectKind::Append,
                            "auditifnotexists" => EffectKind::AuditIfNotExists,
                            "deployifnotexists" => EffectKind::DeployIfNotExists,
                            "disabled" => EffectKind::Disabled,
                            "modify" => EffectKind::Modify,
                            "denyaction" => EffectKind::DenyAction,
                            "manual" => EffectKind::Manual,
                            _ => EffectKind::Other,
                        };
                        let node = EffectNode {
                            span: val_span,
                            kind,
                            raw: val_text,
                        };
                        Self::set_once(&mut effect, node, "effect", &key_span)?;
                    }
                    "details" => {
                        // If details is an object, parse structurally to
                        // recognize existenceCondition inline.  Otherwise
                        // (e.g., append's array form), parse as opaque JSON.
                        if self.token_text() == "{" {
                            let (det, ec) = self.parse_then_details()?;
                            Self::set_once(&mut details, det, "details", &key_span)?;
                            existence_condition = ec;
                        } else {
                            let det = self.parse_json_value()?;
                            Self::set_once(&mut details, det, "details", &key_span)?;
                        }
                    }
                    _ => {
                        let _ = self.parse_json_value()?;
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

        let effect = effect.ok_or_else(|| ParseError::MissingKey {
            span: span.clone(),
            key: "effect",
        })?;

        Ok(ThenBlock {
            span,
            effect,
            details,
            existence_condition,
        })
    }

    /// Parse the `"details"` object, extracting `existenceCondition` as a
    /// structured [`Constraint`] directly from the token stream.
    ///
    /// All other entries are collected into a generic `JsonValue::Object`.
    fn parse_then_details(&mut self) -> Result<(JsonValue, Option<Constraint>), ParseError> {
        let open = self.expect_symbol("{")?;

        let mut entries = alloc::vec::Vec::new();
        let mut existence_condition: Option<Constraint> = None;

        if self.token_text() != "}" {
            loop {
                let (key_span, key) = self.expect_string()?;
                self.expect_symbol(":")?;

                if key.eq_ignore_ascii_case("existenceCondition") {
                    // Parse the constraint directly from the token stream and
                    // expose it separately via `ThenBlock::existence_condition`.
                    // Intentionally omit the `existenceCondition` entry from
                    // the `details` JsonValue since that field is returned
                    // separately on the AST node.
                    Self::set_once(
                        &mut existence_condition,
                        self.parse_constraint()?,
                        "existenceCondition",
                        &key_span,
                    )?;
                } else {
                    let value = self.parse_json_value()?;
                    entries.push(ObjectEntry {
                        key_span,
                        key,
                        value,
                    });
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

        Ok((JsonValue::Object(span, entries), existence_condition))
    }
}
