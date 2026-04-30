// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Azure Policy evaluation subcommand for the regorus example binary.
//!
//! Demonstrates parsing an Azure Policy definition JSON, compiling it to
//! RVM bytecode, normalizing an ARM resource through the alias registry,
//! and evaluating the compiled policy against the normalized input.
//!
//! Usage:
//!   cargo run --example regorus --features azure_policy -- \
//!     azure-policy-eval \
//!       --policy-definition policy.json \
//!       --resource resource.json \
//!       --aliases aliases.json \
//!       [--parameters '{"sku": "Standard_D2s_v3"}'] \
//!       [--api-version 2023-01-01]

use anyhow::{bail, Result};

use regorus::languages::azure_policy::aliases::normalizer;
use regorus::languages::azure_policy::aliases::AliasRegistry;
use regorus::languages::azure_policy::compiler;
use regorus::languages::azure_policy::parser;
use regorus::rvm::RegoVM;
use regorus::Source;
use regorus::Value;

/// Evaluate an Azure Policy definition against a resource.
///
/// This mirrors the pipeline used in production:
/// 1. Load aliases and build the alias registry
/// 2. Parse the policy definition JSON
/// 3. Compile to RVM bytecode (with alias-aware field resolution)
/// 4. Normalize the ARM resource through the alias registry
/// 5. Run the compiled program in the Rego VM
pub fn azure_policy_eval(
    policy_definition: String,
    resource: String,
    aliases: String,
    parameters_json: Option<String>,
    api_version: Option<String>,
) -> Result<()> {
    // 1. Load alias registry.
    let aliases_json = std::fs::read_to_string(&aliases)
        .map_err(|e| anyhow::anyhow!("failed to read aliases file {aliases}: {e}"))?;
    let mut registry = AliasRegistry::new();
    registry.load_from_json(&aliases_json)?;
    println!(
        "Loaded {} resource type(s) from alias registry",
        registry.len()
    );

    // 2. Parse the policy definition.
    let defn_json = std::fs::read_to_string(&policy_definition)
        .map_err(|e| anyhow::anyhow!("failed to read policy file {policy_definition}: {e}"))?;
    let source = Source::from_contents(policy_definition.clone(), defn_json)?;
    let defn = parser::parse_policy_definition(&source)
        .map_err(|e| anyhow::anyhow!("parse error: {e}"))?;
    println!("Parsed policy definition from {policy_definition}");

    // 3. Compile to RVM bytecode.
    let program = compiler::compile_policy_definition_with_aliases(
        &defn,
        registry.alias_map(),
        registry.alias_modifiable_map(),
    )?;
    println!("Compiled policy to RVM bytecode");

    // 4. Build normalized input.
    let resource_json = std::fs::read_to_string(&resource)
        .map_err(|e| anyhow::anyhow!("failed to read resource file {resource}: {e}"))?;
    let raw_resource = Value::from_json_str(&resource_json)?;
    let normalized = normalizer::normalize(&raw_resource, Some(&registry), api_version.as_deref());
    println!("Normalized resource ({} top-level fields)", {
        normalized.as_object().map(|m| m.len()).unwrap_or(0)
    });

    // Inject api_version into the normalized resource (lowercased key to match
    // the host contract — policies reference `field('apiVersion')` which the
    // compiler lowercases to `apiversion`).
    let mut resource = normalized;
    if let Some(ref api_ver) = api_version {
        let map = resource.as_object_mut()?;
        map.insert(Value::from("apiversion"), Value::from(api_ver.clone()));
    }

    // Build the input envelope: { resource, parameters }
    let parameters = if let Some(ref params) = parameters_json {
        Value::from_json_str(params)?
    } else {
        Value::new_object()
    };
    let mut input = Value::new_object();
    {
        let map = input.as_object_mut()?;
        map.insert(Value::from("resource"), resource);
        map.insert(Value::from("parameters"), parameters);
    }

    // Build a default context with requestContext if api_version is provided.
    let mut context = Value::from_json_str(
        r#"{
            "resourceGroup": { "name": "exampleRG", "location": "eastus" },
            "subscription": { "subscriptionId": "00000000-0000-0000-0000-000000000000" }
        }"#,
    )?;
    if let Some(ref api_ver) = api_version {
        let mut req_ctx = Value::new_object();
        let rc_map = req_ctx.as_object_mut()?;
        rc_map.insert(Value::from("apiVersion"), Value::from(api_ver.clone()));
        let ctx_map = context.as_object_mut()?;
        ctx_map.insert(Value::from("requestContext"), req_ctx);
    }

    // 5. Execute in the Rego VM.
    let mut vm = RegoVM::new();
    vm.load_program(program);
    vm.set_input(input);
    vm.set_context(context);

    let result = vm.execute_entry_point_by_name("main")?;
    println!("\nPolicy evaluation result:");
    println!("{}", serde_json::to_string_pretty(&result)?);

    Ok(())
}

/// List available aliases for a resource type.
pub fn azure_policy_aliases(aliases: String, resource_type: Option<String>) -> Result<()> {
    let aliases_json = std::fs::read_to_string(&aliases)
        .map_err(|e| anyhow::anyhow!("failed to read aliases file {aliases}: {e}"))?;
    let mut registry = AliasRegistry::new();
    registry.load_from_json(&aliases_json)?;

    println!("Alias registry: {} resource type(s)", registry.len());

    if let Some(ref rt) = resource_type {
        let rt_lower = rt.to_lowercase();
        let mut found = false;
        for (alias_name, _) in registry.alias_map() {
            if alias_name.to_lowercase().starts_with(&rt_lower) {
                println!("  {alias_name}");
                found = true;
            }
        }
        if !found {
            bail!("no aliases found for resource type '{rt}'");
        }
    } else {
        for (alias_name, _) in registry.alias_map() {
            println!("  {alias_name}");
        }
    }
    Ok(())
}
