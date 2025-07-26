// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use std::path::Path;

fn main() -> Result<()> {
    // Copy hooks to appropriate location so that git will run them.
    // In git worktrees, .git is a symlink and the following commands fail.
    if Path::new(".git").is_dir() {
        if !Path::new("./.git/hooks").exists() {
            std::fs::create_dir_all("./.git/hooks")?;
        }
        std::fs::copy("./scripts/pre-commit", "./.git/hooks/pre-commit")?;
        std::fs::copy("./scripts/pre-push", "./.git/hooks/pre-push")?;
    }

    // Supply information as compile-time environment variables.
    #[cfg(feature = "opa-runtime")]
    {
        let git_hash = std::process::Command::new("git")
            .args(["rev-parse", "HEAD"])
            .output()
            .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
            .unwrap_or_else(|_| "unknown".to_string());
        println!("cargo:rustc-env=GIT_HASH={}", git_hash);
    }

    // Rerun only if build.rs changes.
    println!("cargo:rerun-if-changed=build.rs");
    Ok(())
}
