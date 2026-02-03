// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use anyhow::{anyhow, Result};

pub fn split_token(token: &str) -> Result<(&str, &str, &str)> {
    let mut parts = token.split('.');
    let header = parts.next().ok_or_else(|| anyhow!("Missing JWT header"))?;
    let payload = parts.next().ok_or_else(|| anyhow!("Missing JWT payload"))?;
    let signature = parts
        .next()
        .ok_or_else(|| anyhow!("Missing JWT signature"))?;

    if parts.next().is_some() {
        return Err(anyhow!("JWT has more than 3 parts"));
    }

    Ok((header, payload, signature))
}
