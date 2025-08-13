// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::compiled_policy::CompiledPolicy;
use crate::engine::Engine;
use crate::value::Value;
use crate::*;

use anyhow::Result;

/// Represents a Rego policy module with an identifier and content.
#[derive(Debug, Clone)]
pub struct PolicyModule {
    pub id: Rc<str>,
    pub content: Rc<str>,
}

/// Compiles a target-aware policy from data and modules.
///
/// This is a convenience function that sets up an [`Engine`] and calls
/// [`Engine::compile_for_target`]. For more control over the compilation process
/// or to reuse an engine, use the engine method directly.
///
/// # Arguments
///
/// * `data` - Static data to be available during policy evaluation
/// * `modules` - Array of Rego policy modules to compile together
///
/// # Returns
///
/// Returns a [`CompiledPolicy`] for target-aware evaluation.
///
/// # Note
///
/// This function is only available when the `azure_policy` feature is enabled.
///
/// # See Also
///
/// - [`Engine::compile_for_target`] for detailed documentation and examples
/// - [`compile_policy_with_entrypoint`] for explicit rule-based compilation
#[cfg(feature = "azure_policy")]
#[cfg_attr(docsrs, doc(cfg(feature = "azure_policy")))]
pub fn compile_policy_for_target(data: Value, modules: &[PolicyModule]) -> Result<CompiledPolicy> {
    let mut engine = setup_engine_with_modules(data, modules)?;
    engine.compile_for_target()
}

/// Compiles a policy from data and modules with a specific entry point rule.
///
/// This is a convenience function that sets up an [`Engine`] and calls
/// [`Engine::compile_with_entrypoint`]. For more control over the compilation process
/// or to reuse an engine, use the engine method directly.
///
/// # Arguments
///
/// * `data` - Static data to be available during policy evaluation
/// * `modules` - Array of Rego policy modules to compile together
/// * `entry_point_rule` - The specific rule path to evaluate (e.g., "data.policy.allow")
///
/// # Returns
///
/// Returns a [`CompiledPolicy`] focused on the specified entry point rule.
///
/// # See Also
///
/// - [`Engine::compile_with_entrypoint`] for detailed documentation and examples
/// - [`compile_policy_for_target`] for target-aware compilation
pub fn compile_policy_with_entrypoint(
    data: Value,
    modules: &[PolicyModule],
    entry_point_rule: Rc<str>,
) -> Result<CompiledPolicy> {
    let mut engine = setup_engine_with_modules(data, modules)?;
    engine.compile_with_entrypoint(&entry_point_rule)
}

/// Helper function to set up an engine with data and modules.
fn setup_engine_with_modules(data: Value, modules: &[PolicyModule]) -> Result<Engine> {
    let mut engine = Engine::new();

    // Add data to the engine
    engine.add_data(data)?;
    engine.set_gather_prints(true);

    // Add all modules to the engine
    for module in modules {
        engine.add_policy(module.id.to_string(), module.content.to_string())?;
    }

    Ok(engine)
}
