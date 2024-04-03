// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;
use std::path::Path;

fn main() -> Result<()> {
    // Copy hooks to appropriate location so that git will run them.
    // In git worktrees, .git is a symlink and the following commands fail.
    if Path::new(".git").is_dir() {
        std::fs::copy("./scripts/pre-commit", "./.git/hooks/pre-commit")?;
        std::fs::copy("./scripts/pre-push", "./.git/hooks/pre-push")?;
    }

    // Supply information as compile-time environment variables.
    #[cfg(feature = "opa-runtime")]
    {
        let output = std::process::Command::new("git")
            .args(["rev-parse", "HEAD"])
            .output()
            .expect("`git rev-parse HEAD` failed.");
        let git_hash = String::from_utf8(output.stdout).unwrap();
        println!("cargo:rustc-env=GIT_HASH={}", git_hash);
    }

    Ok(())
}
