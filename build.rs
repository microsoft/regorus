// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::Result;

fn main() -> Result<()> {
    // Copy hooks to appropriate location so that git will run them.
    std::fs::copy("./scripts/pre-commit", "./.git/hooks/pre-commit")?;
    std::fs::copy("./scripts/pre-push", "./.git/hooks/pre-push")?;
    Ok(())
}
