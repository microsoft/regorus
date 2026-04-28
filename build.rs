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
        // Try to get the current git commit hash. This may fail when git is not
        // available (e.g. vcpkg builds) or when building from a source tarball
        // without a .git directory. In those cases we fall back to an empty string.
        let git_hash = std::process::Command::new("git")
            .args(["rev-parse", "HEAD"])
            .output()
            .ok()
            .and_then(|o| if o.status.success() { Some(o.stdout) } else { None })
            .and_then(|bytes| String::from_utf8(bytes).ok())
            .unwrap_or_default();
        println!("cargo:rustc-env=GIT_HASH={git_hash}");
    }

    // Rerun only if build.rs changes.
    println!("cargo:rerun-if-changed=build.rs");
    Ok(())
}
