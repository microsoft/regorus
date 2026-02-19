// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)]

use alloc::boxed::Box;
use alloc::string::ToString as _;
use alloc::vec;
use alloc::vec::Vec;

use super::ConditionInterpreter;
use crate::languages::azure_rbac::ast::{
    ArrayExpression, ArrayOperator, AttributeReference, AttributeSource, BinaryExpression,
    ConditionExpr, EmptySpan, EnvironmentContext, EvaluationContext, ListLiteral, Principal,
    PrincipalType, PropertyAccessExpression, RequestContext, Resource, StringLiteral,
    VariableReference,
};
use crate::languages::azure_rbac::builtins::RbacBuiltin;
use crate::value::Value;

fn basic_context() -> EvaluationContext {
    EvaluationContext {
        principal: Principal {
            id: "user-1".to_string(),
            principal_type: PrincipalType::User,
            custom_security_attributes: Value::new_object(),
        },
        resource: Resource {
            id: "/subscriptions/s1".to_string(),
            resource_type: "Microsoft.Storage/storageAccounts".to_string(),
            scope: "/subscriptions/s1".to_string(),
            attributes: Value::from_json_str(
                r#"{"owner":"alice","tags":["a","b"],"confidential":true}"#,
            )
            .unwrap(),
        },
        request: RequestContext {
            action: Some("Microsoft.Storage/storageAccounts/read".to_string()),
            data_action: None,
            attributes: Value::from_json_str(r#"{"clientIP":"10.0.0.1"}"#).unwrap(),
        },
        environment: EnvironmentContext {
            is_private_link: None,
            private_endpoint: None,
            subnet: None,
            utc_now: Some("2023-05-01T12:00:00Z".to_string()),
        },
        action: Some("Microsoft.Storage/storageAccounts/read".to_string()),
        suboperation: None,
    }
}

#[test]
fn evaluates_basic_condition() {
    let ctx = basic_context();
    let interpreter = ConditionInterpreter::new(&ctx);
    let result = interpreter
        .evaluate_str("@Resource[owner] StringEquals 'alice'")
        .unwrap();
    assert!(result);
}

#[test]
fn evaluates_logical_condition() {
    let ctx = basic_context();
    let interpreter = ConditionInterpreter::new(&ctx);
    let result = interpreter
        .evaluate_str(
            "@Resource[owner] StringEquals 'alice' AND @Resource[confidential] BoolEquals true",
        )
        .unwrap();
    assert!(result);
}

#[test]
fn evaluates_property_access() {
    let mut ctx = basic_context();
    ctx.request.attributes = Value::from_json_str(r#"{"obj":{"key":"value"}}"#).unwrap();

    let expr = ConditionExpr::Binary(BinaryExpression {
        span: EmptySpan,
        operator: RbacBuiltin::StringEquals,
        left: Box::new(ConditionExpr::PropertyAccess(PropertyAccessExpression {
            span: EmptySpan,
            object: Box::new(ConditionExpr::AttributeReference(AttributeReference {
                span: EmptySpan,
                source: AttributeSource::Request,
                namespace: None,
                attribute: "obj".to_string(),
                path: Vec::new(),
            })),
            property: "key".to_string(),
        })),
        right: Box::new(ConditionExpr::StringLiteral(StringLiteral {
            span: EmptySpan,
            value: "value".to_string(),
        })),
    });

    let interpreter = ConditionInterpreter::new(&ctx);
    let result = interpreter.evaluate_bool(&expr).unwrap();
    assert!(result);
}

#[test]
fn evaluates_any_quantifier_with_variable() {
    let ctx = basic_context();
    let expr = ConditionExpr::ArrayExpression(ArrayExpression {
        span: EmptySpan,
        operator: ArrayOperator {
            name: "ANY".to_string(),
            modifier: None,
        },
        array: Box::new(ConditionExpr::ListLiteral(ListLiteral {
            span: EmptySpan,
            elements: vec![
                ConditionExpr::StringLiteral(StringLiteral {
                    span: EmptySpan,
                    value: "a".to_string(),
                }),
                ConditionExpr::StringLiteral(StringLiteral {
                    span: EmptySpan,
                    value: "b".to_string(),
                }),
            ],
        })),
        variable: Some("item".to_string()),
        condition: Box::new(ConditionExpr::Binary(BinaryExpression {
            span: EmptySpan,
            operator: RbacBuiltin::StringEquals,
            left: Box::new(ConditionExpr::VariableReference(VariableReference {
                span: EmptySpan,
                name: "item".to_string(),
            })),
            right: Box::new(ConditionExpr::StringLiteral(StringLiteral {
                span: EmptySpan,
                value: "b".to_string(),
            })),
        })),
    });

    let interpreter = ConditionInterpreter::new(&ctx);
    let result = interpreter.evaluate_bool(&expr).unwrap();
    assert!(result);
}

#[test]
fn evaluates_all_quantifier_with_variable() {
    let ctx = basic_context();
    let expr = ConditionExpr::ArrayExpression(ArrayExpression {
        span: EmptySpan,
        operator: ArrayOperator {
            name: "ALL".to_string(),
            modifier: None,
        },
        array: Box::new(ConditionExpr::ListLiteral(ListLiteral {
            span: EmptySpan,
            elements: vec![
                ConditionExpr::StringLiteral(StringLiteral {
                    span: EmptySpan,
                    value: "a".to_string(),
                }),
                ConditionExpr::StringLiteral(StringLiteral {
                    span: EmptySpan,
                    value: "a".to_string(),
                }),
            ],
        })),
        variable: Some("item".to_string()),
        condition: Box::new(ConditionExpr::Binary(BinaryExpression {
            span: EmptySpan,
            operator: RbacBuiltin::StringEquals,
            left: Box::new(ConditionExpr::VariableReference(VariableReference {
                span: EmptySpan,
                name: "item".to_string(),
            })),
            right: Box::new(ConditionExpr::StringLiteral(StringLiteral {
                span: EmptySpan,
                value: "a".to_string(),
            })),
        })),
    });

    let interpreter = ConditionInterpreter::new(&ctx);
    let result = interpreter.evaluate_bool(&expr).unwrap();
    assert!(result);
}
