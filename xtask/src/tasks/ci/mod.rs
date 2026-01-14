// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::ffi::OsString;
use std::path::Path;

use anyhow::Result;
use clap::Args;

use crate::tasks::util::{
    opa_passing_arguments, run_cargo_step as util_run_cargo_step, workspace_root,
};

pub mod musl;

pub use musl::TestMuslCommand;

const DEFAULT_OPA_FEATURES: &str = "opa-testutil,serde_json/arbitrary_precision";

/// Mirrors the release-focused GitHub workflow locally.
#[derive(Args, Default)]
pub struct CiReleaseCommand {
    /// Propagate --frozen to cargo invocations (match CI by passing --frozen).
    #[arg(long)]
    pub frozen: bool,

    /// Enable the supplied feature list across build and test steps (comma separated).
    #[arg(long, value_delimiter = ',', value_name = "FEATURE")]
    pub features: Vec<String>,

    /// Override the feature set passed to the OPA tests.
    #[arg(long, value_name = "FEATURES")]
    pub opa_features: Option<String>,

    /// Skip the `cargo build --all-features` phase.
    #[arg(long)]
    pub skip_all_features_build: bool,

    /// Skip the `cargo test --no-default-features` phase.
    #[arg(long)]
    pub skip_no_default_features_tests: bool,

    /// Skip the Azure Policy feature tests.
    #[arg(long)]
    pub skip_azure_policy: bool,

    /// Skip the Azure RBAC feature tests.
    #[arg(long)]
    pub skip_azure_rbac: bool,
}

/// Mirrors the debug-focused GitHub workflow locally.
#[derive(Args, Default)]
pub struct CiDebugCommand {
    /// Propagate --frozen to cargo invocations (match CI by passing --frozen).
    #[arg(long)]
    pub frozen: bool,
}

impl CiReleaseCommand {
    pub fn run(&self) -> Result<()> {
        let opa_features = self
            .opa_features
            .clone()
            .unwrap_or_else(|| DEFAULT_OPA_FEATURES.to_string());

        run_ci_suite(CiSuiteConfig {
            release: true,
            frozen: self.frozen,
            include_fmt: true,
            include_run_example: true,
            include_azure_policy: !self.skip_azure_policy,
            include_azure_rbac: !self.skip_azure_rbac,
            include_all_features_build: !self.skip_all_features_build,
            include_no_default_features_tests: !self.skip_no_default_features_tests,
            base_features: self.features.clone(),
            opa_features,
        })
    }
}

impl CiDebugCommand {
    pub fn run(&self) -> Result<()> {
        run_ci_suite(CiSuiteConfig {
            release: false,
            frozen: self.frozen,
            include_fmt: false,
            include_run_example: false,
            include_azure_policy: false,
            include_azure_rbac: true,
            include_all_features_build: true,
            include_no_default_features_tests: true,
            base_features: Vec::new(),
            opa_features: DEFAULT_OPA_FEATURES.to_string(),
        })
    }
}

struct CiSuiteConfig {
    release: bool,
    frozen: bool,
    include_fmt: bool,
    include_run_example: bool,
    include_azure_policy: bool,
    include_azure_rbac: bool,
    include_all_features_build: bool,
    include_no_default_features_tests: bool,
    base_features: Vec<String>,
    opa_features: String,
}

fn run_ci_suite(config: CiSuiteConfig) -> Result<()> {
    let workspace = workspace_root();
    let joined_features = join_features(&config.base_features);

    if config.include_fmt {
        run_fmt(&workspace)?;
    }

    if config.include_all_features_build {
        run_ci_cargo_step(
            &workspace,
            "build",
            config.release,
            config.frozen,
            None,
            &["--all-features"],
            "cargo build --all-features (ci)",
        )?;
    }

    run_ci_cargo_step(
        &workspace,
        "build",
        config.release,
        config.frozen,
        joined_features.as_deref(),
        &[],
        "cargo build (ci)",
    )?;

    if config.include_no_default_features_tests {
        run_ci_cargo_step(
            &workspace,
            "test",
            config.release,
            config.frozen,
            None,
            &["--no-default-features"],
            "cargo test --no-default-features (ci)",
        )?;
    }

    let example_features = example_features(&config.base_features);
    let example_label = format!(
        "cargo build --example regorus --no-default-features --features {} (ci)",
        example_features
    );
    run_ci_cargo_step(
        &workspace,
        "build",
        config.release,
        config.frozen,
        Some(&example_features),
        &["--example", "regorus", "--no-default-features"],
        &example_label,
    )?;

    run_ci_cargo_step(
        &workspace,
        "test",
        config.release,
        config.frozen,
        joined_features.as_deref(),
        &["--doc"],
        "cargo test --doc (ci)",
    )?;

    run_ci_cargo_step(
        &workspace,
        "test",
        config.release,
        config.frozen,
        joined_features.as_deref(),
        &[],
        "cargo test (ci)",
    )?;

    if config.include_run_example {
        run_example(
            &workspace,
            config.release,
            config.frozen,
            joined_features.as_deref(),
        )?;
    }

    run_named_test(
        &workspace,
        config.release,
        config.frozen,
        joined_features.as_deref(),
        "aci",
    )?;

    run_named_test(
        &workspace,
        config.release,
        config.frozen,
        joined_features.as_deref(),
        "kata",
    )?;

    run_opa_tests(
        &workspace,
        config.release,
        config.frozen,
        &config.opa_features,
    )?;

    if config.include_azure_policy {
        run_ci_cargo_step(
            &workspace,
            "test",
            config.release,
            config.frozen,
            None,
            &["--features", "azure_policy"],
            "cargo test --features azure_policy (ci)",
        )?;
    }

    if config.include_azure_rbac {
        run_ci_cargo_step(
            &workspace,
            "test",
            config.release,
            config.frozen,
            None,
            &["--features", "azure-rbac"],
            "cargo test --features azure-rbac (ci)",
        )?;
    }

    Ok(())
}

fn join_features(features: &[String]) -> Option<String> {
    if features.is_empty() {
        None
    } else {
        Some(features.join(","))
    }
}

fn example_features(base: &[String]) -> String {
    let mut features = Vec::with_capacity(base.len() + 1);
    features.push(String::from("std"));
    features.extend(base.iter().cloned());
    features.join(",")
}

fn run_fmt(workspace: &Path) -> Result<()> {
    util_run_cargo_step(
        workspace,
        "cargo xtask fmt --check",
        ["xtask", "fmt", "--check"],
    )
}

fn run_ci_cargo_step(
    workspace: &Path,
    subcommand: &str,
    release: bool,
    frozen: bool,
    features: Option<&str>,
    extra: &[&str],
    label: &str,
) -> Result<()> {
    let mut args = base_cargo_args(subcommand, release, frozen, features);
    for arg in extra {
        args.push(OsString::from(*arg));
    }
    util_run_cargo_step(workspace, label, args)
}

fn run_named_test(
    workspace: &Path,
    release: bool,
    frozen: bool,
    features: Option<&str>,
    name: &str,
) -> Result<()> {
    let label = format!("cargo test --test {} (ci)", name);
    run_ci_cargo_step(
        workspace,
        "test",
        release,
        frozen,
        features,
        &["--test", name],
        &label,
    )
}

fn run_example(
    workspace: &Path,
    release: bool,
    frozen: bool,
    features: Option<&str>,
) -> Result<()> {
    let mut args = base_cargo_args("run", release, frozen, features);
    args.extend(
        [
            "--example",
            "regorus",
            "--",
            "eval",
            "-d",
            "examples/server/allowed_server.rego",
            "-i",
            "examples/server/input.json",
            "data.example",
        ]
        .into_iter()
        .map(OsString::from),
    );

    util_run_cargo_step(workspace, "cargo run --example regorus (ci)", args)
}

fn run_opa_tests(workspace: &Path, release: bool, frozen: bool, features: &str) -> Result<()> {
    let tests = opa_passing_arguments(workspace)?;
    let mut args = base_cargo_args("test", release, frozen, Some(features));
    args.push(OsString::from("--test"));
    args.push(OsString::from("opa"));
    args.push(OsString::from("--"));
    for entry in tests {
        args.push(OsString::from(entry));
    }

    let label = format!("cargo test --test opa --features {} (ci)", features);
    util_run_cargo_step(workspace, &label, args)
}

fn base_cargo_args(
    subcommand: &str,
    release: bool,
    frozen: bool,
    features: Option<&str>,
) -> Vec<OsString> {
    let mut args = vec![OsString::from(subcommand)];
    if release {
        args.push(OsString::from("--release"));
    }
    if frozen {
        args.push(OsString::from("--frozen"));
    }
    if let Some(features) = features {
        if !features.is_empty() {
            args.push(OsString::from("--features"));
            args.push(OsString::from(features));
        }
    }
    args
}
