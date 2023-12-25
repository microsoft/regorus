// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;
use std::time::SystemTime;

use anyhow::{bail, Result};
use chrono::{Datelike, Days, Months, NaiveDateTime};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("time.add_date", (add_date, 4));
    m.insert("time.now_ns", (now_ns, 0));
}

fn add_date(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.add_date";
    ensure_args_count(span, name, params, args, 4)?;

    let ns = ensure_numeric(name, &params[0], &args[0])?
        .as_i64()
        .ok_or_else(|| span.error("could not convert `ns` to int64"))?;
    let years: i32 = ensure_numeric(name, &params[1], &args[1])?
        .as_i64()
        .and_then(|n| n.try_into().ok())
        .ok_or_else(|| span.error("could not convert `years` to int32"))?;
    let months: i32 = ensure_numeric(name, &params[2], &args[2])?
        .as_i64()
        .and_then(|n| n.try_into().ok())
        .ok_or_else(|| span.error("could not convert `months` to int32"))?;
    let days: i32 = ensure_numeric(name, &params[3], &args[3])?
        .as_i64()
        .and_then(|n| n.try_into().ok())
        .ok_or_else(|| span.error("could not convert `days` to int32"))?;

    let (sec, nsec) = nsec_to_sec_and_remainder(ns);

    let datetime = match NaiveDateTime::from_timestamp_opt(sec, nsec) {
        Some(datetime) => datetime,
        None => return Ok(Value::Undefined),
    };

    let Some(new_year) = datetime.year().checked_add(years) else {
        return Ok(Value::Undefined);
    };

    Ok(datetime
        .with_year(new_year)
        .and_then(|d| {
            let rhs = Months::new(months.unsigned_abs());
            if months >= 0 {
                d.checked_add_months(rhs)
            } else {
                d.checked_sub_months(rhs)
            }
        })
        .and_then(|d| {
            let rhs = Days::new(days.unsigned_abs() as u64);
            if days >= 0 {
                d.checked_add_days(rhs)
            } else {
                d.checked_sub_days(rhs)
            }
        })
        .and_then(|d| d.timestamp_nanos_opt())
        .map(Into::into)
        .unwrap_or(Value::Undefined))
}

fn now_ns(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.now_ns";
    ensure_args_count(span, name, params, args, 0)?;

    let now = SystemTime::now();
    let elapsed = match now.duration_since(SystemTime::UNIX_EPOCH) {
        Ok(e) => e,
        Err(e) => bail!(span.error(format!("could not fetch elapsed time. {e}").as_str())),
    };
    let nanos = elapsed.as_nanos();
    Ok(Value::from(nanos))
}

// Unlike Go's `time` package, `chrono` crate only supports nanoseconds
// up to 1_000_000_000 (a billion). But we receive the whole epochs as
// nanoseconds which is much more larger than a billion most of the time.
// In order to overcome this we devide nanoseconds into two,
// whole seconds and reminder nanoseconds.
// This is basically what Go's `time.Unix` does and we adapted our code from that function.
// https://cs.opensource.google/go/go/+/refs/tags/go1.21.5:src/time/time.go;l=1397-1405
fn nsec_to_sec_and_remainder(mut nsec: i64) -> (i64, u32) {
    const BILLION: i64 = 1_000_000_000;

    let mut sec: i64 = 0;
    #[allow(clippy::manual_range_contains)]
    if nsec < 0 || nsec >= BILLION {
        let n = nsec / BILLION;
        sec += n;
        nsec -= n * BILLION;
        if nsec < 0 {
            nsec += BILLION;
            sec -= 1;
        }
    }

    (sec, nsec as u32)
}
