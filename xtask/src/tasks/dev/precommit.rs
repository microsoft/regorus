// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use std::collections::HashSet;
use std::io::Write;
use std::process::{Command, Stdio};

use anyhow::{anyhow, Context, Result};
use clap::Args;

use crate::tasks::util::{log_step, run_cargo_step, workspace_root};

/// Runs the repository's pre-commit validation sequence.
#[derive(Args, Default)]
pub struct PrecommitCommand;

impl PrecommitCommand {
    pub fn run(&self) -> Result<()> {
        let workspace = workspace_root();

        log_step("cargo build --all-targets");
        run_cargo_step(
            &workspace,
            "cargo build --all-targets",
            ["build", "--all-targets"],
        )
        .with_context(|| "pre-commit: cargo build --all-targets failed".to_string())?;

        run_cargo_step(
            &workspace,
            "cargo xtask fmt --check",
            ["xtask", "fmt", "--check"],
        )
        .with_context(|| "pre-commit: cargo xtask fmt --check failed".to_string())?;

        run_cargo_step(&workspace, "cargo xtask clippy", ["xtask", "clippy"])
            .with_context(|| "pre-commit: cargo xtask clippy failed".to_string())?;

        log_step("git status --short");
        verify_clean_status(&workspace)?;

        Ok(())
    }
}

fn verify_clean_status(root: &std::path::Path) -> Result<()> {
    let mut git = Command::new("git");
    git.current_dir(root);
    git.arg("status");
    git.arg("-s");
    git.stdout(Stdio::piped());

    let output = git
        .output()
        .with_context(|| format!("failed to inspect git status in {}", root.display()))?;

    if !output.status.success() {
        return Err(anyhow!(
            "git status -s exited with status {}",
            output.status
        ));
    }

    let stdout = String::from_utf8(output.stdout)
        .with_context(|| "git status output was not UTF-8".to_string())?;

    let interesting: HashSet<&str> = ["MM", "??", "AM", " M"].into_iter().collect();
    let mut flagged = Vec::new();
    for line in stdout.lines() {
        if line.len() >= 2 {
            let status = &line[..2];
            if interesting.contains(status) {
                flagged.push(line.to_string());
            }
        }
    }

    if flagged.is_empty() {
        return Ok(());
    }

    let mut stderr = std::io::stderr();
    writeln!(stderr, "\nUnstaged changes found:").ok();
    for entry in &flagged {
        writeln!(stderr, "{}", entry).ok();
    }
    writeln!(stderr, "Stage them and try again").ok();

    Err(anyhow!("repository contains unstaged changes"))
}
