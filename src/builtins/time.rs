// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;
use std::time::SystemTime;

use anyhow::{anyhow, bail, Result};
use chrono::{DateTime, Datelike, Days, FixedOffset, Local, Months, TimeZone, Timelike, Utc};
use chrono_tz::Tz;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("time.add_date", (add_date, 4));
    m.insert("time.clock", (clock, 1));
    m.insert("time.date", (date, 1));
    m.insert("time.now_ns", (now_ns, 0));
}

fn add_date(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.add_date";
    ensure_args_count(span, name, params, args, 4)?;

    let datetime = parse_epoch(name, &params[0], &args[0])?;
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

fn clock(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.clock";
    ensure_args_count(span, name, params, args, 1)?;

    let datetime = parse_epoch(name, &params[0], &args[0])?;

    Ok(Vec::from([
        (datetime.hour() as u64).into(),
        (datetime.minute() as u64).into(),
        (datetime.second() as u64).into(),
    ])
    .into())
}

fn date(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.date";
    ensure_args_count(span, name, params, args, 1)?;

    let datetime = parse_epoch(name, &params[0], &args[0])?;

    Ok(Vec::from([
        (datetime.year() as u64).into(),
        (datetime.month() as u64).into(),
        (datetime.day() as u64).into(),
    ])
    .into())
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

fn parse_epoch(fcn: &str, arg: &Expr, val: &Value) -> Result<DateTime<FixedOffset>> {
    match val {
        Value::Number(num) => {
            let ns = num.as_i64().ok_or_else(|| {
                arg.span()
                    .error("could not convert numeric value of `ns` to int64")
            })?;

            return Ok(Utc.timestamp_nanos(ns).fixed_offset());
        }

        Value::Array(arr) => match arr.as_slice() {
            [Value::Number(num)] => {
                let ns = num.as_i64().ok_or_else(|| {
                    arg.span()
                        .error("could not convert numeric value of `ns` to int64")
                })?;

                return Ok(Utc.timestamp_nanos(ns).fixed_offset());
            }
            [Value::Number(num), Value::String(tz)] => {
                let ns = num.as_i64().ok_or_else(|| {
                    arg.span()
                        .error("could not convert numeric value of `ns` to int64")
                })?;

                let datetime = match tz.as_ref() {
                    "UTC" | "" => Utc.timestamp_nanos(ns).fixed_offset(),
                    "Local" => Local.timestamp_nanos(ns).fixed_offset(),
                    _ => {
                        let tz: Tz = tz.parse().map_err(|err: String| anyhow!(err))?;
                        tz.timestamp_nanos(ns).fixed_offset()
                    }
                };
                return Ok(datetime);
            }
            _ => {}
        },

        _ => {}
    }

    bail!(arg.span().error(&format!(
        "`{fcn}` expects `ns` to be a `number` or `array[number, string]`. Got `{val}` instead"
    )))
}
