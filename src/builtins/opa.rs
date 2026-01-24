// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{enforce_limit, ensure_args_count};
use crate::*;

use crate::lexer::Span;
use crate::value::Value;

use alloc::collections::BTreeMap;

use anyhow::Result;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("opa.runtime", (opa_runtime, 0));
}

fn opa_runtime(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "opa.runtime";
    ensure_args_count(span, name, params, args, 0)?;
    let mut obj = BTreeMap::new();

    obj.insert(
        Value::String("commit".into()),
        Value::String(env!("GIT_HASH").into()),
    );

    obj.insert(
        Value::String("regorus-version".into()),
        Value::String(env!("CARGO_PKG_VERSION").into()),
    );

    obj.insert(
        Value::String("version".into()),
        Value::String("0.60.0".into()),
    );

    // Emitting environment variables could lead to confidential data being leaked.
    #[cfg(feature = "std")]
    if false {
        obj.insert(
            Value::String("env".into()),
            Value::from_map(
                std::env::vars()
                    .map(|(k, v)| (Value::String(k.into()), Value::String(v.into())))
                    .collect(),
            ),
        );
    }

    let features = [
        #[cfg(feature = "base64")]
        "base64",
        #[cfg(feature = "base64url")]
        "base64url",
        #[cfg(feature = "glob")]
        "glob",
        #[cfg(feature = "graph")]
        "graph",
        #[cfg(feature = "hex")]
        "hex",
        #[cfg(feature = "http")]
        "http",
        #[cfg(feature = "jsonschema")]
        "jsonschema",
        #[cfg(feature = "opa-runtime")]
        "opa-runtime",
        #[cfg(feature = "regex")]
        "regex",
        #[cfg(feature = "semver")]
        "semver",
        #[cfg(feature = "time")]
        "time",
        #[cfg(feature = "uuid")]
        "uuid",
        #[cfg(feature = "urlquery")]
        "urlquery",
        #[cfg(feature = "yaml")]
        "yaml",
        "",
    ];

    let features = &features[..features.len() - 1];
    let mut feature_values = Vec::with_capacity(features.len());
    for feature in features.iter() {
        feature_values.push(Value::String((*feature).to_string().into()));
        // Guard feature list growth while reporting enabled capabilities.
        enforce_limit()?;
    }
    obj.insert(
        Value::String("features".into()),
        Value::from_array(feature_values),
    );

    let mut builtins: Vec<&&str> = builtins::BUILTINS.keys().collect();
    builtins.sort();

    let mut builtin_values = Vec::with_capacity(builtins.len());
    for builtin in builtins.iter() {
        builtin_values.push(Value::String((**builtin).to_string().into()));
        // Guard builtin list growth while reporting registered functions.
        enforce_limit()?;
    }
    obj.insert(
        Value::String("builtins".into()),
        Value::from_array(builtin_values),
    );

    Ok(Value::from_map(obj))
}
