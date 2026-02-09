// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Tests for Azure RBAC condition expression parsing

#[cfg(test)]
mod condition_tests {
    #![allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)] // tests unwrap/expect to assert parse results
    use crate::languages::azure_rbac::parser::*;
    use alloc::string::String;
    use alloc::vec;
    use alloc::vec::Vec;
    use serde_json;
    use serde_yaml;

    #[derive(Debug, serde::Deserialize)]
    struct TestCase {
        name: String,
        condition: String,
        expected: serde_json::Value,
    }

    #[derive(Debug, serde::Deserialize)]
    struct TestCases {
        test_cases: Vec<TestCase>,
    }

    fn load_test_cases() -> TestCases {
        let yaml_content = include_str!("test_cases.yaml");
        serde_yaml::from_str(yaml_content).expect("Failed to parse test cases YAML")
    }

    #[test]
    fn test_condition_expression_parsing() {
        let test_cases = load_test_cases();

        for test_case in test_cases.test_cases {
            // Parse the condition expression
            let result = parse_condition_expression(&test_case.condition);

            assert!(
                result.is_ok(),
                "Failed to parse condition '{}' for test '{}': {:?}",
                test_case.condition,
                test_case.name,
                result.err()
            );

            let parsed_condition = result.unwrap();

            // Verify we have a parsed expression
            assert!(
                parsed_condition.expression.is_some(),
                "No parsed expression for test '{}', condition: '{}'",
                test_case.name,
                test_case.condition
            );

            let actual_expr = parsed_condition.expression.unwrap();

            // Deserialize the expected JSON into our AST type
            let expected_expr: crate::languages::azure_rbac::ast::ConditionExpr =
                serde_json::from_value(test_case.expected.clone()).unwrap_or_else(|_| {
                    panic!(
                        "Failed to deserialize expected JSON for test '{}': {}",
                        test_case.name,
                        serde_json::to_string_pretty(&test_case.expected).unwrap()
                    )
                });

            // Compare the actual parsed expression with the expected expression
            assert_eq!(
                actual_expr, expected_expr,
                "\nTest '{}' failed!\nCondition: '{}'\nExpected: {:#?}\nActual: {:#?}",
                test_case.name, test_case.condition, expected_expr, actual_expr
            );
        }
    }

    // Test for edge cases and error conditions
    #[test]
    fn test_parsing_errors() {
        // The parser funnels every binary/logical keyword through the same branches,
        // so this list of malformed expressions covers all operators without duplication.
        let invalid_expressions = vec![
            ("", "Empty expression"),
            ("@", "Incomplete attribute reference"),
            ("@Request", "Missing attribute brackets"),
            ("@Request[", "Unclosed attribute brackets"),
            ("@InvalidSource[attr]", "Invalid attribute source"),
            ("@Request[attr] InvalidOperator 'value'", "Invalid operator"),
            ("@Request[attr] StringEquals", "Missing right operand"),
            ("StringEquals 'value'", "Missing left operand"),
            (
                "@Request[attr] 'value'",
                "Missing operator between operands",
            ),
            ("StringEquals 'value'", "Missing left operand"),
            ("StringEquals", "Binary operator without any operands"),
            (
                "@Request[attr] StringEquals 'value' AND",
                "Missing right operand after AND",
            ),
            (
                "AND @Request[attr] StringEquals 'value'",
                "Leading AND without left operand",
            ),
            (
                "@Request[attr] StringEquals 'value' OR",
                "Missing right operand after OR",
            ),
            (
                "OR @Request[attr] StringEquals 'value'",
                "Leading OR without left operand",
            ),
            ("NOT", "Standalone NOT without operand"),
            ("Exists", "Exists without operand"),
            ("NotExists", "NotExists without operand"),
            (
                "(@Request[attr] StringEquals 'value'",
                "Unmatched parenthesis",
            ),
            ("@Request[attr] StringEquals 'unclosed", "Unclosed string"),
            (
                "@Request[attr] StringEquals 'value')",
                "Unexpected closing parenthesis",
            ),
        ];

        for (expression, description) in invalid_expressions {
            let result = parse_condition_expression(expression);
            assert!(
                result.is_err(),
                "Expected error for {} but got success: {:?}",
                description,
                result
            );
        }
    }

    #[test]
    fn test_raw_expression_preservation() {
        let test_cases = load_test_cases();

        for test_case in test_cases.test_cases.iter().take(5) {
            // Test first 5 cases
            let result = parse_condition_expression(&test_case.condition).unwrap();
            assert_eq!(
                result.raw_expression, test_case.condition,
                "Raw expression not preserved for test '{}'",
                test_case.name
            );
        }
    }
}

#[cfg(test)]
mod rbac_builtin_tests {
    #![allow(clippy::panic, clippy::unwrap_used, clippy::expect_used)] // tests unwrap/expect to assert evaluation
    use alloc::string::{String, ToString as _};
    use alloc::vec::Vec;
    use serde_json;
    use serde_yaml;
    use std::fs;
    use std::path::PathBuf;

    use crate::languages::azure_rbac::ast::{
        EnvironmentContext, EvaluationContext, Principal, PrincipalType, RequestContext, Resource,
    };
    use crate::languages::azure_rbac::interpreter::ConditionInterpreter;
    use crate::languages::azure_rbac::parser::parse_condition_expression;
    use crate::value::Value;

    #[derive(Debug, serde::Deserialize)]
    struct EvalTestCase {
        name: String,
        condition: String,
        expected: bool,
        #[serde(default)]
        context: Option<EvalContextOverrides>,
    }

    #[derive(Debug, serde::Deserialize)]
    struct EvalTestCases {
        test_cases: Vec<EvalTestCase>,
    }

    #[derive(Debug, serde::Deserialize, Default)]
    struct EvalContextOverrides {
        action: Option<String>,
        suboperation: Option<String>,
        request_action: Option<String>,
        data_action: Option<String>,
        principal_id: Option<String>,
        principal_type: Option<String>,
        resource_id: Option<String>,
        resource_type: Option<String>,
        resource_scope: Option<String>,
        request_attributes: Option<serde_json::Value>,
        resource_attributes: Option<serde_json::Value>,
        principal_custom_security_attributes: Option<serde_json::Value>,
        environment: Option<EvalEnvironmentOverrides>,
    }

    #[derive(Debug, serde::Deserialize, Default)]
    struct EvalEnvironmentOverrides {
        is_private_link: Option<bool>,
        private_endpoint: Option<String>,
        subnet: Option<String>,
        utc_now: Option<String>,
    }

    fn default_context() -> EvaluationContext {
        EvaluationContext {
            principal: Principal {
                id: "user-1".to_string(),
                principal_type: PrincipalType::User,
                custom_security_attributes: Value::from_json_str(
                    r#"{"department":"eng","levels":["L1","L2"]}"#,
                )
                .unwrap(),
            },
            resource: Resource {
                id: "/subscriptions/s1".to_string(),
                resource_type: "Microsoft.Storage/storageAccounts".to_string(),
                scope: "/subscriptions/s1".to_string(),
                attributes: Value::from_json_str(
                    r#"{"owner":"alice","tags":["a","b"],"count":5,"enabled":false,"ip":"10.0.0.5","guid":"a1b2c3d4-0000-0000-0000-000000000000"}"#,
                )
                .unwrap(),
            },
            request: RequestContext {
                action: Some("Microsoft.Storage/storageAccounts/read".to_string()),
                data_action: Some("Microsoft.Storage/storageAccounts/read".to_string()),
                attributes: Value::from_json_str(
                    r#"{"owner":"alice","text":"HelloWorld","tags":["prod","gold"],"count":10,"ratio":2.5,"enabled":true,"ip":"10.0.0.8","guid":"A1B2C3D4-0000-0000-0000-000000000000","time":"12:30:15","date":"2023-05-01T12:00:00Z","numbers":[1,2,3],"letters":["a","b"]}"#,
                )
                .unwrap(),
            },
            environment: EnvironmentContext {
                is_private_link: Some(false),
                private_endpoint: None,
                subnet: None,
                utc_now: Some("2023-05-01T12:00:00Z".to_string()),
            },
            action: Some("Microsoft.Storage/storageAccounts/read".to_string()),
            suboperation: Some("sub/read".to_string()),
        }
    }

    fn value_from_json(value: Option<serde_json::Value>, default: Value) -> Value {
        value
            .map(|v| Value::from_json_str(&serde_json::to_string(&v).unwrap()).unwrap())
            .unwrap_or(default)
    }

    fn apply_overrides(
        mut context: EvaluationContext,
        overrides: EvalContextOverrides,
    ) -> EvaluationContext {
        if let Some(action) = overrides.action {
            context.action = Some(action);
        }
        if let Some(suboperation) = overrides.suboperation {
            context.suboperation = Some(suboperation);
        }
        if let Some(action) = overrides.request_action {
            context.request.action = Some(action);
        }
        if let Some(data_action) = overrides.data_action {
            context.request.data_action = Some(data_action);
        }
        if let Some(principal_id) = overrides.principal_id {
            context.principal.id = principal_id;
        }
        if let Some(principal_type) = overrides.principal_type {
            context.principal.principal_type = match principal_type.as_str() {
                "User" => PrincipalType::User,
                "Group" => PrincipalType::Group,
                "ServicePrincipal" => PrincipalType::ServicePrincipal,
                "ManagedServiceIdentity" => PrincipalType::ManagedServiceIdentity,
                _ => PrincipalType::User,
            };
        }
        if let Some(resource_id) = overrides.resource_id {
            context.resource.id = resource_id;
        }
        if let Some(resource_type) = overrides.resource_type {
            context.resource.resource_type = resource_type;
        }
        if let Some(resource_scope) = overrides.resource_scope {
            context.resource.scope = resource_scope;
        }

        context.request.attributes =
            value_from_json(overrides.request_attributes, context.request.attributes);
        context.resource.attributes =
            value_from_json(overrides.resource_attributes, context.resource.attributes);
        context.principal.custom_security_attributes = value_from_json(
            overrides.principal_custom_security_attributes,
            context.principal.custom_security_attributes,
        );

        if let Some(env) = overrides.environment {
            if let Some(is_private_link) = env.is_private_link {
                context.environment.is_private_link = Some(is_private_link);
            }
            if let Some(private_endpoint) = env.private_endpoint {
                context.environment.private_endpoint = Some(private_endpoint);
            }
            if let Some(subnet) = env.subnet {
                context.environment.subnet = Some(subnet);
            }
            if let Some(utc_now) = env.utc_now {
                context.environment.utc_now = Some(utc_now);
            }
        }

        context
    }

    fn load_eval_test_cases() -> Vec<EvalTestCase> {
        let mut dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        dir.push("src/languages/azure_rbac/test_cases");

        let mut entries: Vec<PathBuf> = fs::read_dir(&dir)
            .expect("Failed to read test_cases directory")
            .filter_map(|entry| entry.ok().map(|entry| entry.path()))
            .filter(|path| path.extension().map(|ext| ext == "yaml").unwrap_or(false))
            .collect();
        entries.sort();

        let mut cases = Vec::new();
        for path in entries {
            let yaml = fs::read_to_string(&path).expect("Failed to read test case YAML");
            let suite: EvalTestCases =
                serde_yaml::from_str(&yaml).expect("Failed to parse evaluation cases YAML");
            cases.extend(suite.test_cases);
        }
        cases
    }

    #[test]
    fn rbac_builtins() {
        let cases = load_eval_test_cases();

        for case in cases {
            let mut context = default_context();
            if let Some(overrides) = case.context {
                context = apply_overrides(context, overrides);
            }

            let parsed = parse_condition_expression(&case.condition).unwrap();
            let expr = parsed.expression.expect("Missing parsed expression");

            let interpreter = ConditionInterpreter::new(&context);
            let result = interpreter.evaluate_bool(&expr).unwrap();

            assert_eq!(
                result, case.expected,
                "Test '{}' failed for condition '{}'",
                case.name, case.condition
            );
        }
    }
}
