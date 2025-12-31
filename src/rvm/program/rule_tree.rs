// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use anyhow::Result as AnyResult;

use crate::value::Value;

use super::Program;

impl Program {
    /// Add a rule to the rule tree
    /// path: Package path components (e.g., ["p1", "p2"] for data.p1.p2.rule)
    /// rule_name: Rule name (e.g., "rule")
    /// rule_index: Index of the rule in rule_infos
    pub fn add_rule_to_tree(
        &mut self,
        path: &[String],
        rule_name: &str,
        rule_index: usize,
    ) -> AnyResult<()> {
        if path.len() >= Program::MAX_PATH_DEPTH {
            return Err(anyhow::anyhow!(
                "Rule path depth exceeds maximum ({} >= {})",
                path.len(),
                Program::MAX_PATH_DEPTH
            ));
        }

        let capacity = path.len().checked_add(1).unwrap_or(path.len());
        let mut full_path = Vec::with_capacity(capacity);
        full_path.extend(path.iter().map(|s| s.as_str()));
        full_path.push(rule_name);

        let target = self.rule_tree.make_or_get_value_mut(&full_path)?;
        *target = Value::Number(rule_index.into());

        Ok(())
    }

    /// Check for conflicts between rule tree and data
    /// Returns an error if any rule path conflicts with data paths
    pub fn check_rule_data_conflicts(&self, data: &Value) -> Result<(), crate::rvm::vm::VmError> {
        let actual_rule_tree = &self.rule_tree["data"];

        match *actual_rule_tree {
            Value::Undefined => return Ok(()),
            Value::Object(ref rule_obj) if rule_obj.is_empty() => return Ok(()),
            _ => {}
        }

        Self::check_conflicts_recursive(actual_rule_tree, data, &mut Vec::new())
    }

    fn check_conflicts_recursive(
        rule_tree: &Value,
        data: &Value,
        current_path: &mut Vec<String>,
    ) -> Result<(), crate::rvm::vm::VmError> {
        match *rule_tree {
            Value::Object(ref rule_obj) => {
                for (key, rule_value) in rule_obj.iter() {
                    if let Value::String(ref key_str) = *key {
                        current_path.push(key_str.to_string());

                        let data_value = &data[key];

                        match *rule_value {
                            Value::Number(_) => {
                                if data_value != &Value::Undefined {
                                    return Err(crate::rvm::vm::VmError::RuleDataConflict {
                                        message: format!(
                                            "Conflict: rule defines path '{}' but data also provides this path",
                                            current_path.join("."),
                                        ),
                                        pc: 0,
                                    });
                                }
                            }
                            Value::Object(_) => {
                                if let Value::Object(_) = *data_value {
                                    Self::check_conflicts_recursive(
                                        rule_value,
                                        data_value,
                                        current_path,
                                    )?;
                                } else if data_value != &Value::Undefined {
                                    return Err(crate::rvm::vm::VmError::RuleDataConflict {
                                        message: format!(
                                            "Conflict: rule defines subpaths under '{}' but data provides a non-object value at this path",
                                            current_path.join("."),
                                        ),
                                        pc: 0,
                                    });
                                }
                            }
                            _ => {
                                return Err(crate::rvm::vm::VmError::RuleDataConflict {
                                    message: format!(
                                        "Invalid rule tree structure at path '{}'",
                                        current_path.join("."),
                                    ),
                                    pc: 0,
                                });
                            }
                        }

                        current_path.pop();
                    }
                }
            }
            _ => {
                return Err(crate::rvm::vm::VmError::RuleDataConflict {
                    message: "Rule tree root must be an object".to_string(),
                    pc: 0,
                });
            }
        }

        Ok(())
    }
}
