// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::path::Path;
use std::process::{Command, Stdio};

use anyhow::{Context, Result};
use clap::Args;

use super::precommit::PrecommitCommand;
use crate::tasks::util::{
    log_step, opa_passing_arguments, run_cargo_step, run_command, workspace_root,
};

/// Runs the repository's pre-push validation sequence.
#[derive(Args, Default)]
pub struct PrepushCommand;

impl PrepushCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();

        log_step("pre-commit checks");
        PrecommitCommand::default()
            .run()
            .with_context(|| "pre-push: pre-commit sequence failed".to_string())?;

        run_cargo_step(&workspace, "cargo test --doc", ["test", "--doc"])
            .with_context(|| "pre-push: cargo test --doc failed".to_string())?;

        if rustup_available() {
            log_step("rustup target add thumbv7m-none-eabi");
            let mut rustup = Command::new("rustup");
            rustup.arg("target");
            rustup.arg("add");
            rustup.arg("thumbv7m-none-eabi");
            run_command(rustup, "rustup target add thumbv7m-none-eabi")
                .with_context(|| "pre-push: rustup target add failed".to_string())?;

            run_cargo_step(
                &workspace,
                "cargo xtask test-no-std",
                ["xtask", "test-no-std"],
            )
            .with_context(|| "pre-push: cargo xtask test-no-std failed".to_string())?;
        }

        run_cargo_step(
            &workspace,
            "cargo build --example regorus --no-default-features --features std",
            [
                "build",
                "--example",
                "regorus",
                "--no-default-features",
                "--features",
                "std",
            ],
        )
        .with_context(|| {
            "pre-push: cargo build --example regorus --no-default-features --features std failed"
                .to_string()
        })?;

        run_cargo_step(
            &workspace,
            "cargo build --all-features",
            ["build", "--all-features"],
        )
        .with_context(|| "pre-push: cargo build --all-features failed".to_string())?;

        run_cargo_step(&workspace, "cargo test", ["test"])
            .with_context(|| "pre-push: cargo test failed".to_string())?;
        run_cargo_step(
            &workspace,
            "cargo test --test aci",
            ["test", "--test", "aci"],
        )
        .with_context(|| "pre-push: cargo test --test aci failed".to_string())?;
        run_cargo_step(
            &workspace,
            "cargo test --test kata",
            ["test", "--test", "kata"],
        )
        .with_context(|| "pre-push: cargo test --test kata failed".to_string())?;

        run_cargo_step(
            &workspace,
            "cargo test --features rego-extensions",
            ["test", "--features", "rego-extensions"],
        )
        .with_context(|| "pre-push: cargo test --features rego-extensions failed".to_string())?;
        run_cargo_step(
            &workspace,
            "cargo test --test aci --features rego-extensions",
            ["test", "--test", "aci", "--features", "rego-extensions"],
        )
        .with_context(|| {
            "pre-push: cargo test --test aci --features rego-extensions failed".to_string()
        })?;
        run_cargo_step(
            &workspace,
            "cargo test --test kata --features rego-extensions",
            ["test", "--test", "kata", "--features", "rego-extensions"],
        )
        .with_context(|| {
            "pre-push: cargo test --test kata --features rego-extensions failed".to_string()
        })?;

        log_step("cargo test --features opa-testutil,serde_json/arbitrary_precision,rego-extensions --test opa");
        run_opa_conformance(&workspace).with_context(|| {
            "pre-push: cargo test --features opa-testutil,serde_json/arbitrary_precision,rego-extensions --test opa failed"
                .to_string()
        })?;

        Ok(())
    }
}

fn run_opa_conformance(root: &Path) -> Result<()> {
    let tests = opa_passing_arguments(root)?;
    let mut cmd = Command::new("cargo");
    cmd.current_dir(root);
    cmd.arg("test");
    cmd.arg("--features");
    cmd.arg("opa-testutil,serde_json/arbitrary_precision,rego-extensions");
    cmd.arg("--test");
    cmd.arg("opa");
    cmd.arg("--");
    for entry in tests {
        cmd.arg(entry);
    }

    run_command(
        cmd,
        "cargo test --features opa-testutil,serde_json/arbitrary_precision,rego-extensions --test opa",
    )
}

fn rustup_available() -> bool {
    let mut probe = Command::new("rustup");
    probe.arg("--version");
    probe.stdout(Stdio::null());
    probe.stderr(Stdio::null());
    probe
        .status()
        .map(|status| status.success())
        .unwrap_or(false)
}
