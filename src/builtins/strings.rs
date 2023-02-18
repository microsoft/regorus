// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::Value;

use anyhow::{bail, Result};

fn ensure_numeric(fcn: &str, arg: &Expr, v: &Value) -> Result<Float> {
    Ok(match &v {
        Value::Number(n) => n.0 .0,
        _ => {
            let span = arg.span();
            bail!(
                span.error(format!("`{fcn}` expects numeric argument. Got `{v}` instead").as_str())
            )
        }
    })
}

