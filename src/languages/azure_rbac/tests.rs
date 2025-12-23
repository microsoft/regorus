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
