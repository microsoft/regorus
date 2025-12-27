// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(clippy::indexing_slicing)]

use super::super::error::TargetCompileError;
#[cfg(feature = "azure_policy")]
use super::super::TargetInfo;
use super::super::*;

fn format_effect_names(names: &[String]) -> String {
    match names.len() {
        0 => String::new(),
        1 => names[0].clone(),
        2 => format!("{} or {}", names[0], names[1]),
        _ => {
            if let Some((last, rest)) = names.split_last() {
                format!("{} or {}", rest.join(", "), last)
            } else {
                String::new()
            }
        }
    }
}

pub fn resolve_target(interpreter: &mut Interpreter) -> Result<(), TargetCompileError> {
    use crate::registry::targets;

    let mut target_name: Option<String> = None;
    let mut target_package: Option<String> = None;

    // Check all modules for target specifications
    for module in interpreter.compiled_policy.modules.iter() {
        if let Some(ref module_target) = module.target {
            // Get the package path for this module
            let module_package = Interpreter::get_path_string(&module.package.refr, None)
                .map_err(|_| TargetCompileError::TargetNotFound(module_target.clone().into()))?;

            match &target_name {
                None => {
                    // First target found
                    target_name = Some(module_target.clone());
                    target_package = Some(module_package);
                }
                Some(existing_target) => {
                    // Ensure all modules specify the same target
                    if existing_target != module_target {
                        return Err(TargetCompileError::ConflictingTargets {
                            existing: existing_target.as_str().into(),
                            conflicting: module_target.as_str().into(),
                        });
                    }

                    // Ensure all modules with targets have the same package
                    if let Some(ref existing_package) = target_package {
                        if existing_package != &module_package {
                            return Err(TargetCompileError::ConflictingPackages {
                                target: module_target.as_str().into(),
                                existing_package: existing_package.as_str().into(),
                                conflicting_package: module_package.as_str().into(),
                            });
                        }
                    }
                }
            }
        }
    }

    // If a target is specified, retrieve it from the registry
    if let Some(target_name) = target_name {
        match targets::get(&target_name) {
            Some(target) => {
                // Target found in registry - store it in the compiled policy
                // We'll set a default effect schema here, but it will be updated in resolve_effect
                // once we determine which effect actually has rules defined
                let default_effect_schema = match target.effects.values().next() {
                    Some(schema) => schema.clone(),
                    None => {
                        return Err(TargetCompileError::TargetNotFound(
                            format!("Target '{}' has no effects defined", target_name)
                                .as_str()
                                .into(),
                        ));
                    }
                };
                let target_info = TargetInfo {
                    target,
                    package: match target_package {
                        Some(pkg) => pkg.as_str().into(),
                        None => {
                            return Err(TargetCompileError::TargetNotFound(
                                format!("No package found for target '{}'", target_name)
                                    .as_str()
                                    .into(),
                            ));
                        }
                    },
                    effect_schema: default_effect_schema,
                    effect_name: "".into(), // Will be updated in resolve_effect
                    effect_path: "".into(), // Will be updated in resolve_effect
                };
                interpreter.compiled_policy_mut().target_info = Some(target_info);
            }
            None => {
                return Err(TargetCompileError::TargetNotFound(
                    target_name.as_str().into(),
                ));
            }
        }
    } else {
        // No target specified - this is an error when using compile_for_target
        return Err(TargetCompileError::NoTargetSpecified);
    }

    Ok(())
}

pub fn resolve_effect(interpreter: &mut Interpreter) -> Result<(), TargetCompileError> {
    // Check if we have target info from resolve_target
    if let Some(ref target_info) = interpreter.compiled_policy.target_info {
        let target = &target_info.target;
        let package = &target_info.package;

        let mut effects_with_rules = Vec::new();

        // For each effect defined in the target, check if rules exist
        for effect_name in target.effects.keys() {
            // Rule keys are stored with "data." prefix in CompiledPolicy
            let expected_path = format!("data.{}.{}", package, effect_name);

            // Disallow sub-paths for effects in rules.
            for rule_path in interpreter.compiled_policy.rules.keys() {
                if rule_path.starts_with(&expected_path) && rule_path.len() > expected_path.len() {
                    // Sub-paths are not allowed for effects - they must be exact matches only
                    // This prevents effect rules from being defined at deeper nested paths
                    let all_effect_names: Vec<String> =
                        target.effects.keys().map(|k| k.to_string()).collect();
                    let formatted_names = format_effect_names(&all_effect_names);
                    return Err(TargetCompileError::NoEffectRules {
                        target_name: target.name.to_string().into(),
                        package: package.to_string().into(),
                        effect_names: formatted_names.as_str().into(),
                    });
                }
            }

            // Disallow sub-paths for effects in default_rules.
            for rule_path in interpreter.compiled_policy.default_rules.keys() {
                if rule_path.starts_with(&expected_path) && rule_path.len() > expected_path.len() {
                    // Sub-paths are not allowed for effects - they must be exact matches only
                    let all_effect_names: Vec<String> =
                        target.effects.keys().map(|k| k.to_string()).collect();
                    let formatted_names = format_effect_names(&all_effect_names);
                    return Err(TargetCompileError::NoEffectRules {
                        target_name: target.name.to_string().into(),
                        package: package.to_string().into(),
                        effect_names: formatted_names.as_str().into(),
                    });
                }
            }

            // Check if rules exist at the expected path or any sub-path
            let mut has_rules = false;

            // Check for exact match in rules
            if let Some(rules) = interpreter.compiled_policy.rules.get(&expected_path) {
                if !rules.is_empty() {
                    has_rules = true;
                }
            }

            // Check for exact match in default_rules
            if !has_rules {
                if let Some(default_rules) = interpreter
                    .compiled_policy
                    .default_rules
                    .get(&expected_path)
                {
                    if !default_rules.is_empty() {
                        has_rules = true;
                    }
                }
            }

            if has_rules {
                effects_with_rules.push(effect_name.clone());
            }
        }

        // Ensure exactly one effect has rules defined
        match effects_with_rules.len() {
            0 => {
                let all_effect_names: Vec<String> =
                    target.effects.keys().map(|k| k.to_string()).collect();
                let formatted_names = format_effect_names(&all_effect_names);
                return Err(TargetCompileError::NoEffectRules {
                    target_name: target.name.to_string().into(),
                    package: package.to_string().into(),
                    effect_names: formatted_names.as_str().into(),
                });
            }
            1 => {
                // Exactly one effect has rules - this is correct
                // Update the target info with the correct effect schema
                let effect_name = &effects_with_rules[0];
                let effect_schema = match target.effects.get(effect_name) {
                    Some(schema) => schema.clone(),
                    None => {
                        // This should not happen since we got the effect_name from target.effects.keys()
                        return Err(TargetCompileError::TargetNotFound(
                            format!(
                                "Effect '{}' not found in target '{}'",
                                effect_name, target.name
                            )
                            .as_str()
                            .into(),
                        ));
                    }
                };

                // Update the target info with the correct effect schema, name, and path
                let expected_path = format!("data.{}.{}", package, effect_name);
                if let Some(ref mut target_info_mut) = interpreter.compiled_policy_mut().target_info
                {
                    target_info_mut.effect_schema = effect_schema;
                    target_info_mut.effect_name = effect_name.as_ref().into();
                    target_info_mut.effect_path = expected_path.as_str().into();
                }
            }
            _ => {
                return Err(TargetCompileError::MultipleEffectRules {
                    target_name: target.name.to_string().into(),
                    effect_names: effects_with_rules.join(", ").as_str().into(),
                    path: package.to_string().into(),
                });
            }
        }
    }

    Ok(())
}

pub fn resolve_and_apply_target(interpreter: &mut Interpreter) -> Result<(), TargetCompileError> {
    // Resolve the target first
    resolve_target(interpreter)?;

    // Then resolve the effect
    resolve_effect(interpreter)?;

    Ok(())
}
