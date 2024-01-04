// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use std::path::Path;
use std::process::Command;

fn main() -> Result<()> {
    // Copy hooks to appropriate location so that git will run them.
    // In git worktrees, .git is a symlink and the following commands fail.
    if Path::new(".git").is_dir() {
        std::fs::copy("./scripts/pre-commit", "./.git/hooks/pre-commit")?;
        std::fs::copy("./scripts/pre-push", "./.git/hooks/pre-push")?;
    }

    // Supply information as compile-time environment variables.
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .unwrap();
    let git_hash = String::from_utf8(output.stdout).unwrap();
    println!("cargo:rustc-env=GIT_HASH={}", git_hash);

    Ok(())
}
