// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::Expr;
use crate::builtins;
use crate::builtins::utils::ensure_args_count;
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("to_number", to_number);
}

fn to_number(span: &Span, params: &[Expr], args: &[Value]) -> Result<Value> {
    let name = "to_number";
    ensure_args_count(span, name, params, args, 1)?;

    let span = params[0].span();
    Ok(match &args[0] {
        Value::Bool(true) => Value::from_float(1.0),
        Value::Bool(false) => Value::from_float(0.0),
        Value::Number(_) => args[0].clone(),
        // Eventhough the doc says that strings are converted using strconv.Atoi golang method,
        // in practice strings seems to be read as json numbers. This means that floating point
        // numbers are read and the string representation is limited to what json allows.
        Value::String(s) => match Value::from_json_str(s) {
            Ok(Value::Number(n)) => Value::Number(n),
            _ => {
                bail!(span.error("could not parse string as number"));
            }
        },
        _ => {
            bail!(span.error(format!("`{name}` expects bool/number/string argument.").as_str()));
        }
    })
}
