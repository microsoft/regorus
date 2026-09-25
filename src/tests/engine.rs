// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::Engine;
use alloc::string::ToString as _;
use anyhow::Result;

#[test]
fn has_policy_params_inspects_authored_rule_heads_in_the_exact_module() -> Result<()> {
    let policies = [
        ("conditional.rego", "package customer\nparams if { false }"),
        ("complete.rego", "package customer\nparams := false"),
        (
            "descendant.rego",
            "package customer\nparams.child.nested := null",
        ),
        ("default.rego", "package customer\ndefault params = false"),
        (
            "default_child.rego",
            "package customer\ndefault params.child = null",
        ),
        (
            "function.rego",
            "package customer\nparams.lookup(value) := value",
        ),
        ("set.rego", "package customer\nparams contains \"item\""),
    ];

    for (path, policy) in policies {
        let mut engine = Engine::new();
        engine.add_policy(path.to_string(), policy.to_string())?;

        anyhow::ensure!(
            engine.has_policy_params(path)?,
            "expected a params rule in {path}"
        );
    }

    let mut engine = Engine::new();
    engine.add_policy(
        "references.rego".to_string(),
        r#"package customer
           import data.shared as params
           # params.comment := true
           note := "params.string"
           config := {"params": true}
           use := params.value
        "#
        .to_string(),
    )?;
    anyhow::ensure!(
        !engine.has_policy_params("references.rego")?,
        "expected a reference-only module to have no params rule"
    );

    engine.add_policy(
        "same_package.rego".to_string(),
        "package customer\nparams.child := true".to_string(),
    )?;
    anyhow::ensure!(
        !engine.has_policy_params("references.rego")?,
        "expected same-package rules not to change another module's result"
    );
    anyhow::ensure!(
        engine.has_policy_params("same_package.rego")?,
        "expected same_package.rego to declare a params rule"
    );

    Ok(())
}

#[test]
fn has_policy_params_errors_for_missing_or_ambiguous_sources_and_bad_policies() -> Result<()> {
    let mut engine = Engine::new();
    engine.add_policy(
        "duplicate.rego".to_string(),
        "package customer\nx := true".to_string(),
    )?;
    anyhow::ensure!(
        engine.has_policy_params("missing.rego").is_err(),
        "expected a missing source path to return an error"
    );

    engine.add_policy(
        "duplicate.rego".to_string(),
        "package customer\nparams := true".to_string(),
    )?;
    anyhow::ensure!(
        engine.has_policy_params("duplicate.rego").is_err(),
        "expected an ambiguous source path to return an error"
    );

    anyhow::ensure!(
        Engine::new()
            .add_policy("malformed.rego".to_string(), "package".to_string())
            .is_err(),
        "expected malformed policy to fail to load"
    );

    let mut unclassifiable_engine = Engine::new();
    unclassifiable_engine.add_policy(
        "unclassifiable.rego".to_string(),
        "package customer\nparams[lookup()] := true".to_string(),
    )?;
    anyhow::ensure!(
        unclassifiable_engine
            .has_policy_params("unclassifiable.rego")
            .is_err(),
        "expected an unclassifiable rule head to return an error"
    );

    Ok(())
}
