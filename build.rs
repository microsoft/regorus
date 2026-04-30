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
        // Allow build systems (e.g. vcpkg, CI) to inject the commit hash directly
        // via a GIT_HASH environment variable. If not set, attempt to read it from
        // git. Fall back to "unknown" when git is unavailable or there is no .git
        // directory (e.g. builds from source tarballs).
        let git_hash = std::env::var("GIT_HASH").ok().unwrap_or_else(|| {
            std::process::Command::new("git")
                .args(["rev-parse", "HEAD"])
                .output()
                .ok()
                .and_then(|o| {
                    if o.status.success() {
                        Some(o.stdout)
                    } else {
                        None
                    }
                })
                .and_then(|bytes| String::from_utf8(bytes).ok())
                .map(|s| s.trim().to_string())
                .unwrap_or_else(|| "unknown".to_string())
        });
        println!("cargo:rustc-env=GIT_HASH={git_hash}");
    }

    // Rerun only if build.rs changes.
    println!("cargo:rerun-if-changed=build.rs");
    Ok(())
}
