// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::arithmetic_side_effects, clippy::unused_trait_names)]

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::languages::azure_rbac::ast::{
    AttributeReference, AttributeSource, BooleanLiteral, ConditionExpr, ConditionOperator,
    EmptySpan, FunctionCallExpression, IdentifierExpression, ListLiteral, NullLiteral,
    NumberLiteral, SetLiteral, StringLiteral,
};
use crate::lexer::{AzureRbacTokenKind, TokenKind};

use super::condition_parser::ConditionParser;
use super::ConditionParseError;

impl<'source> ConditionParser<'source> {
    /// Parse primary expression (literals, attribute refs, function calls, parentheses)
    pub(super) fn parse_primary_expression(
        &mut self,
    ) -> Result<ConditionExpr, ConditionParseError> {
        match self.current.0 {
            // Parenthesized expression
            TokenKind::Symbol if self.current_text() == "(" => {
                self.advance()?;
                let expr = self.parse_or_expression()?;
                self.expect_symbol(")")?;
                Ok(expr)
            }

            // Attribute reference (@Source[...])
            TokenKind::AzureRbac(AzureRbacTokenKind::At) => self.parse_attribute_reference(),

            // String literal
            TokenKind::String => {
                let value = self.current_text().to_string();
                self.advance()?;
                Ok(ConditionExpr::StringLiteral(StringLiteral {
                    span: EmptySpan,
                    value,
                }))
            }

            // Raw string literal
            TokenKind::RawString => {
                let value = self.current_text().to_string();
                self.advance()?;
                Ok(ConditionExpr::StringLiteral(StringLiteral {
                    span: EmptySpan,
                    value,
                }))
            }

            // Number literal
            TokenKind::Number => {
                let raw = self.current_text().to_string();
                self.advance()?;
                Ok(ConditionExpr::NumberLiteral(NumberLiteral {
                    span: EmptySpan,
                    raw,
                }))
            }

            // Set literal {'a', 'b', 'c'}
            TokenKind::Symbol if self.current_text() == "{" => self.parse_set_literal(),

            // List literal ['a', 'b']
            TokenKind::Symbol if self.current_text() == "[" => self.parse_list_literal(),

            // Identifier (function call, boolean, identifier)
            TokenKind::Ident => {
                let text = self.current_text();
                match text {
                    "true" => {
                        self.advance()?;
                        Ok(ConditionExpr::BooleanLiteral(BooleanLiteral {
                            span: EmptySpan,
                            value: true,
                        }))
                    }
                    "false" => {
                        self.advance()?;
                        Ok(ConditionExpr::BooleanLiteral(BooleanLiteral {
                            span: EmptySpan,
                            value: false,
                        }))
                    }
                    "null" => {
                        self.advance()?;
                        Ok(ConditionExpr::NullLiteral(NullLiteral { span: EmptySpan }))
                    }
                    _ => {
                        let name = text.to_string();
                        self.advance()?;

                        // Check for function call
                        if self.current.0 == TokenKind::Symbol && self.current_text() == "(" {
                            self.parse_function_call(name)
                        } else {
                            if ConditionOperator::from_name(&name).is_some() {
                                return Err(ConditionParseError::UnsupportedCondition(format!(
                                    "Operator '{}' missing operands",
                                    name
                                )));
                            }

                            // Just an identifier
                            Ok(ConditionExpr::Identifier(IdentifierExpression {
                                span: EmptySpan,
                                name,
                            }))
                        }
                    }
                }
            }

            _ => Err(ConditionParseError::UnsupportedCondition(format!(
                "Unexpected token: {:?} '{}'",
                self.current.0,
                self.current_text()
            ))),
        }
    }

    /// Parse attribute reference @Source[namespace:attribute]
    pub(super) fn parse_attribute_reference(
        &mut self,
    ) -> Result<ConditionExpr, ConditionParseError> {
        self.expect(TokenKind::AzureRbac(AzureRbacTokenKind::At))?;

        // Parse source (Request, Resource, Principal, Environment, Context)
        if self.current.0 != TokenKind::Ident {
            return Err(ConditionParseError::UnsupportedCondition(
                "Expected attribute source after @".to_string(),
            ));
        }

        let source_text = self.current_text();
        let source = match source_text {
            "Request" => AttributeSource::Request,
            "Resource" => AttributeSource::Resource,
            "Principal" => AttributeSource::Principal,
            "Environment" => AttributeSource::Environment,
            "Context" => AttributeSource::Context,
            _ => {
                return Err(ConditionParseError::UnsupportedCondition(format!(
                    "Unknown attribute source: {}",
                    source_text
                )))
            }
        };
        self.advance()?;

        // Expect [
        self.expect_symbol("[")?;

        // Parse namespace:attribute or just attribute
        let mut namespace = None;

        // Read until ] - this handles namespace:attribute and complex paths
        let mut parts = Vec::new();
        loop {
            match self.current.0 {
                TokenKind::Symbol if self.current_text() == "]" => break,
                TokenKind::Symbol if self.current_text() == ":" => {
                    // Colon separator
                    parts.push(":".to_string());
                    self.advance()?;
                }
                TokenKind::Ident | TokenKind::String | TokenKind::Symbol => {
                    parts.push(self.current_text().to_string());
                    self.advance()?;
                }
                _ => {
                    return Err(ConditionParseError::UnsupportedCondition(format!(
                        "Unexpected token in attribute reference: {:?}",
                        self.current.0
                    )))
                }
            }
        }

        // Join parts and split on last colon
        let full_path = parts.join("");
        let attribute = if let Some(colon_pos) = full_path.rfind(':') {
            namespace = Some(full_path[..colon_pos].to_string());
            full_path[colon_pos + 1..].to_string()
        } else {
            full_path
        };

        self.expect_symbol("]")?;

        Ok(ConditionExpr::AttributeReference(AttributeReference {
            span: EmptySpan,
            source,
            namespace,
            attribute,
            path: Vec::new(), // Path parsing can be added later if needed
        }))
    }

    /// Parse function call
    pub(super) fn parse_function_call(
        &mut self,
        function: String,
    ) -> Result<ConditionExpr, ConditionParseError> {
        self.expect_symbol("(")?;

        let mut arguments = Vec::new();

        // Parse arguments
        if self.current.0 != TokenKind::Symbol || self.current_text() != ")" {
            loop {
                let arg = self.parse_or_expression()?;
                arguments.push(arg);

                if self.current.0 == TokenKind::Symbol && self.current_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        self.expect_symbol(")")?;

        Ok(ConditionExpr::FunctionCall(FunctionCallExpression {
            span: EmptySpan,
            function,
            arguments,
        }))
    }

    /// Parse set literal {'a', 'b', 'c'}
    pub(super) fn parse_set_literal(&mut self) -> Result<ConditionExpr, ConditionParseError> {
        self.expect_symbol("{")?;

        let mut elements = Vec::new();

        if self.current.0 != TokenKind::Symbol || self.current_text() != "}" {
            loop {
                let elem = self.parse_or_expression()?;
                elements.push(elem);

                if self.current.0 == TokenKind::Symbol && self.current_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        self.expect_symbol("}")?;

        Ok(ConditionExpr::SetLiteral(SetLiteral {
            span: EmptySpan,
            elements,
        }))
    }

    /// Parse list literal ['a', 'b']
    pub(super) fn parse_list_literal(&mut self) -> Result<ConditionExpr, ConditionParseError> {
        self.expect_symbol("[")?;

        let mut elements = Vec::new();

        if self.current.0 != TokenKind::Symbol || self.current_text() != "]" {
            loop {
                let elem = self.parse_or_expression()?;
                elements.push(elem);

                if self.current.0 == TokenKind::Symbol && self.current_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        self.expect_symbol("]")?;

        Ok(ConditionExpr::ListLiteral(ListLiteral {
            span: EmptySpan,
            elements,
        }))
    }

    /// Expect a specific symbol
    pub(super) fn expect_symbol(&mut self, expected: &str) -> Result<(), ConditionParseError> {
        if self.current.0 != TokenKind::Symbol || self.current_text() != expected {
            return Err(ConditionParseError::UnsupportedCondition(format!(
                "Expected '{}', found '{}'",
                expected,
                self.current_text()
            )));
        }
        self.advance()?;
        Ok(())
    }
}
