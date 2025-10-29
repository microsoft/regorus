// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Path manipulation utilities shared between analyzer and compiler

use alloc::string::{String, ToString};
use alloc::vec::Vec;

/// Component of a reference chain
#[derive(Debug, Clone)]
pub enum AccessComponent {
    /// Static field access (e.g., .field_name)
    Field(String),
    /// Dynamic access (e.g., [expr])
    Dynamic,
}

/// Represents a chained reference like data.a.b[expr].c
#[derive(Debug, Clone)]
pub struct ReferenceChain {
    /// Root variable (e.g., "data", "input", "local_var")
    pub root: String,
    /// Chain of field accesses
    pub components: Vec<AccessComponent>,
}

impl ReferenceChain {
    /// Get the static prefix path (all literal components from the start)
    pub fn static_prefix(&self) -> Vec<&str> {
        let mut prefix = alloc::vec![self.root.as_str()];
        for component in &self.components {
            match component {
                AccessComponent::Field(field) => prefix.push(field.as_str()),
                AccessComponent::Dynamic => break,
            }
        }
        prefix
    }

    /// Check if the chain is fully static (no dynamic components)
    #[allow(dead_code)]
    pub fn is_fully_static(&self) -> bool {
        self.components
            .iter()
            .all(|c| matches!(c, AccessComponent::Field(_)))
    }

    /// Get full path as string (for static chains)
    #[allow(dead_code)]
    pub fn to_path_string(&self) -> Option<String> {
        if !self.is_fully_static() {
            return None;
        }
        let mut parts = alloc::vec![self.root.as_str()];
        for component in &self.components {
            if let AccessComponent::Field(field) = component {
                parts.push(field.as_str());
            }
        }
        Some(parts.join("."))
    }
}

/// Parse a rule path string into components
#[allow(dead_code)]
pub fn parse_rule_path(path: &str) -> Vec<String> {
    path.split('.').map(|s| s.to_string()).collect()
}

/// Check if a rule path matches a pattern with wildcards
/// e.g., "data.test.users.alice" matches "data.test.users.*"
pub fn matches_path_pattern(rule_path: &str, pattern: &str) -> bool {
    if !pattern.contains('*') {
        // Exact match or prefix
        return rule_path == pattern || rule_path.starts_with(&alloc::format!("{}.", pattern));
    }

    let rule_parts: Vec<&str> = rule_path.split('.').collect();
    let pattern_parts: Vec<&str> = pattern.split('.').collect();

    let match_length = rule_parts.len().min(pattern_parts.len());

    for i in 0..match_length {
        let rule_part = rule_parts[i];
        let pattern_part = pattern_parts[i];

        if pattern_part == "*" {
            if rule_part.is_empty() {
                return false;
            }
        } else if rule_part != pattern_part {
            return false;
        }
    }

    rule_parts.len() >= pattern_parts.len()
        || pattern_parts[match_length..].iter().all(|&p| p == "*")
}

/// Normalize a rule path (remove redundant "data." prefix if present twice)
pub fn normalize_rule_path(path: &str) -> String {
    // Handle cases like "data.data.package.rule"
    if path.starts_with("data.data.") {
        path.strip_prefix("data.").unwrap().to_string()
    } else {
        path.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matches_path_pattern() {
        assert!(matches_path_pattern(
            "data.test.users.alice",
            "data.test.users.*"
        ));
        assert!(matches_path_pattern(
            "data.test.users.alice",
            "data.*.*.alice"
        ));
        assert!(!matches_path_pattern(
            "data.test.admin",
            "data.test.users.*"
        ));
        assert!(matches_path_pattern("data.pkg.rule", "data.pkg.rule"));
    }

    #[test]
    fn test_static_prefix() {
        let chain = ReferenceChain {
            root: "data".to_string(),
            components: alloc::vec![
                AccessComponent::Field("a".to_string()),
                AccessComponent::Field("b".to_string()),
                AccessComponent::Dynamic,
                AccessComponent::Field("c".to_string()),
            ],
        };
        assert_eq!(chain.static_prefix(), alloc::vec!["data", "a", "b"]);
        assert!(!chain.is_fully_static());
    }

    #[test]
    fn test_fully_static_chain() {
        let chain = ReferenceChain {
            root: "input".to_string(),
            components: alloc::vec![
                AccessComponent::Field("user".to_string()),
                AccessComponent::Field("name".to_string()),
            ],
        };
        assert!(chain.is_fully_static());
        assert_eq!(chain.to_path_string(), Some("input.user.name".to_string()));
    }

    #[test]
    fn test_normalize_rule_path() {
        assert_eq!(
            normalize_rule_path("data.data.package.rule"),
            "data.package.rule"
        );
        assert_eq!(
            normalize_rule_path("data.package.rule"),
            "data.package.rule"
        );
    }
}
