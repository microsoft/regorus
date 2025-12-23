// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::unused_trait_names)]
#![allow(missing_debug_implementations)] // parser structs are internal; Debug not required

use alloc::boxed::Box;
use alloc::format;
use alloc::string::ToString;

use crate::languages::azure_rbac::ast::{
    BinaryExpression, ConditionExpr, ConditionExpression, ConditionOperator, EmptySpan,
    LogicalExpression, LogicalOperator, UnaryExpression, UnaryOperator,
};
use crate::lexer::{AzureRbacTokenKind, Lexer, Source, Token, TokenKind};

use super::error::ConditionParseError;

/// Parse a condition expression string into AST
pub fn parse_condition_expression(
    condition_str: &str,
) -> Result<ConditionExpression, ConditionParseError> {
    if condition_str.trim().is_empty() {
        return Err(ConditionParseError::UnsupportedCondition(
            "Empty condition expression".to_string(),
        ));
    }

    let source = Source::from_contents("condition".to_string(), condition_str.to_string())
        .map_err(|e| ConditionParseError::InvalidExpression(e.to_string()))?;
    let parsed_expr = ConditionParser::parse(&source)?;

    Ok(ConditionExpression::with_parsed(
        EmptySpan,
        condition_str.to_string(),
        parsed_expr,
    ))
}

/// Condition expression parser
pub struct ConditionParser<'source> {
    pub(super) lexer: Lexer<'source>,
    pub(super) current: Token,
}

impl<'source> ConditionParser<'source> {
    /// Parse a condition expression from source
    pub fn parse(source: &'source Source) -> Result<ConditionExpr, ConditionParseError> {
        let mut lexer = Lexer::new(source);
        lexer.set_enable_rbac_tokens(true);
        lexer.set_allow_single_quoted_strings(true);

        let current = lexer
            .next_token()
            .map_err(|e| ConditionParseError::InvalidExpression(e.to_string()))?;

        let mut parser = Self { lexer, current };
        let expression = parser.parse_or_expression()?;

        if parser.current.0 != TokenKind::Eof {
            return Err(ConditionParseError::UnsupportedCondition(format!(
                "Unexpected token after expression: {:?} '{}'",
                parser.current.0,
                parser.current_text()
            )));
        }

        Ok(expression)
    }

    /// Get current token text
    pub(super) fn current_text(&self) -> &str {
        self.current.1.text()
    }

    /// Advance to next token
    pub(super) fn advance(&mut self) -> Result<(), ConditionParseError> {
        self.current = self
            .lexer
            .next_token()
            .map_err(|e| ConditionParseError::InvalidExpression(e.to_string()))?;
        Ok(())
    }

    /// Check if current token matches expected
    pub(super) fn expect(&mut self, expected: TokenKind) -> Result<(), ConditionParseError> {
        if self.current.0 != expected {
            return Err(ConditionParseError::UnsupportedCondition(format!(
                "Expected {:?}, found {:?} at {}",
                expected,
                self.current.0,
                self.current_text()
            )));
        }
        self.advance()?;
        Ok(())
    }

    /// Parse OR expression (lowest precedence)
    pub(super) fn parse_or_expression(&mut self) -> Result<ConditionExpr, ConditionParseError> {
        let mut left = self.parse_and_expression()?;

        while self.current.0 == TokenKind::AzureRbac(AzureRbacTokenKind::LogicalOr)
            || (self.current.0 == TokenKind::Ident && self.current_text() == "OR")
        {
            self.advance()?;
            let right = self.parse_and_expression()?;
            left = ConditionExpr::Logical(LogicalExpression {
                span: EmptySpan,
                operator: LogicalOperator::Or,
                left: Box::new(left),
                right: Box::new(right),
            });
        }

        Ok(left)
    }

    /// Parse AND expression (higher precedence than OR)
    pub(super) fn parse_and_expression(&mut self) -> Result<ConditionExpr, ConditionParseError> {
        let mut left = self.parse_unary_expression()?;

        while self.current.0 == TokenKind::AzureRbac(AzureRbacTokenKind::LogicalAnd)
            || (self.current.0 == TokenKind::Ident && self.current_text() == "AND")
        {
            self.advance()?;
            let right = self.parse_unary_expression()?;
            left = ConditionExpr::Logical(LogicalExpression {
                span: EmptySpan,
                operator: LogicalOperator::And,
                left: Box::new(left),
                right: Box::new(right),
            });
        }

        Ok(left)
    }

    /// Parse unary expression (NOT, Exists)
    pub(super) fn parse_unary_expression(&mut self) -> Result<ConditionExpr, ConditionParseError> {
        if self.current.0 == TokenKind::Ident {
            let text = self.current_text();
            match text {
                "NOT" | "!" => {
                    self.advance()?;
                    let operand = self.parse_unary_expression()?;
                    return Ok(ConditionExpr::Unary(UnaryExpression {
                        span: EmptySpan,
                        operator: UnaryOperator::Not,
                        operand: Box::new(operand),
                    }));
                }
                "Exists" => {
                    self.advance()?;
                    let operand = self.parse_primary_expression()?;
                    return Ok(ConditionExpr::Unary(UnaryExpression {
                        span: EmptySpan,
                        operator: UnaryOperator::Exists,
                        operand: Box::new(operand),
                    }));
                }
                "NotExists" => {
                    self.advance()?;
                    let operand = self.parse_primary_expression()?;
                    return Ok(ConditionExpr::Unary(UnaryExpression {
                        span: EmptySpan,
                        operator: UnaryOperator::NotExists,
                        operand: Box::new(operand),
                    }));
                }
                _ => {}
            }
        }

        self.parse_comparison_expression()
    }

    /// Parse comparison/binary expression
    pub(super) fn parse_comparison_expression(
        &mut self,
    ) -> Result<ConditionExpr, ConditionParseError> {
        let left = self.parse_primary_expression()?;

        // Check for binary operator
        if self.current.0 == TokenKind::Ident {
            let op_text = self.current_text().to_string();

            // Check if this is a known operator
            if let Some(operator) = ConditionOperator::from_name(&op_text) {
                self.advance()?;
                let right = self.parse_primary_expression()?;
                return Ok(ConditionExpr::Binary(BinaryExpression {
                    span: EmptySpan,
                    operator,
                    left: Box::new(left),
                    right: Box::new(right),
                }));
            }
        }

        Ok(left)
    }
}
