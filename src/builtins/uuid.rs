// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_string};
use crate::lexer::Span;
use crate::value::Value;
use crate::*;

use alloc::collections::BTreeMap;

use anyhow::Result;
use uuid::{Timestamp, Uuid};

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("uuid.parse", (parse, 1));
    m.insert("uuid.rfc4122", (rfc4122, 1));
}

fn parse(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "uuid.parse";
    ensure_args_count(span, name, params, args, 1)?;

    let val = ensure_string(name, &params[0], &args[0])?;
    let Some(uuid) = Uuid::parse_str(&val).ok() else {
        return Ok(Value::Undefined);
    };
    let version = uuid.get_version_num();

    let mut result = BTreeMap::new();
    result.insert(
        Value::String("version".into()),
        Value::Number(version.into()),
    );
    result.insert(
        Value::String("variant".into()),
        Value::String(uuid.get_variant().to_string().into()),
    );

    if let Some(time) = timestamp(&uuid) {
        let (sec, nanosec) = time.to_unix();
        let time = sec.wrapping_mul(1_000_000_000).wrapping_add(nanosec as u64);
        result.insert(Value::String("time".into()), Value::Number(time.into()));
    }

    if version == 1 || version == 2 {
        let (f1, _, _, f4) = uuid.as_fields();

        result.insert(
            Value::String("nodeid".into()),
            Value::String(
                f4[2..]
                    .iter()
                    .map(|f| format!("{f:02x}"))
                    .collect::<Vec<_>>()
                    .join("-")
                    .into(),
            ),
        );
        result.insert(
            Value::String("macvariables".into()),
            Value::String(mac_vars(f4[2]).into()),
        );

        let clock_seq = u16::from_be_bytes([f4[0], f4[1]]) & 0x3fff;
        result.insert(
            Value::String("clocksequence".into()),
            Value::Number((clock_seq as u64).into()),
        );

        if version == 2 {
            result.insert(
                Value::String("id".into()),
                Value::Number((f1 as u64).into()),
            );
            result.insert(
                Value::String("domain".into()),
                Value::String(domain(f4[1]).into()),
            );
        }
    }

    Ok(Value::from(result))
}

fn rfc4122(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "uuid.rfc4122";
    ensure_args_count(span, name, params, args, 1)?;
    ensure_string(name, &params[0], &args[0])?;

    let uuid = Uuid::new_v4();
    Ok(Value::String(uuid.to_string().into()))
}

fn mac_vars(b: u8) -> &'static str {
    if b & 0b11 == 0b11 {
        return "local:multicast";
    } else if b & 0b01 == 0b01 {
        return "global:multicast";
    } else if b & 0b10 == 0b10 {
        return "local:unicast";
    }
    "global:unicast"
}

fn domain(b: u8) -> String {
    match b {
        0 => "Person".to_string(),
        1 => "Group".to_string(),
        2 => "Org".to_string(),
        n => format!("Domain{n}"),
    }
}

fn timestamp(uuid: &Uuid) -> Option<Timestamp> {
    // We need a special case for v2 UUIDs because `uuid` crate does not support
    // parsing timestamps for v2 UUIDs but OPA tests expects them and also
    // the original Go implementation parses timestamps for v2 UUIDs.
    // This is just a copy of parsing logic for v1 UUIDs:
    // https://github.com/uuid-rs/uuid/blob/94ecea893fadac93248f1bd6f47673c09cec5912/src/lib.rs#L900-L904
    if uuid.get_version_num() == 2 {
        let (ticks, counter) = decode_rfc4122_timestamp(uuid);
        #[allow(deprecated)]
        return Some(Timestamp::from_rfc4122(ticks, counter));
    }

    uuid.get_timestamp()
}

// Copied from https://github.com/uuid-rs/uuid/blob/94ecea893fadac93248f1bd6f47673c09cec5912/src/timestamp.rs#L190-L205
const fn decode_rfc4122_timestamp(uuid: &Uuid) -> (u64, u16) {
    let bytes = uuid.as_bytes();

    let ticks: u64 = ((bytes[6] & 0x0F) as u64) << 56
        | (bytes[7] as u64) << 48
        | (bytes[4] as u64) << 40
        | (bytes[5] as u64) << 32
        | (bytes[0] as u64) << 24
        | (bytes[1] as u64) << 16
        | (bytes[2] as u64) << 8
        | (bytes[3] as u64);

    let counter: u16 = ((bytes[8] & 0x3F) as u16) << 8 | (bytes[9] as u16);

    (ticks, counter)
}
