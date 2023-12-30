// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric};
use crate::lexer::Span;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{anyhow, bail, Result};
use chrono::{
    DateTime, Datelike, Days, FixedOffset, Local, Months, SecondsFormat, TimeZone, Timelike, Utc,
};
use chrono_tz::Tz;

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("time.add_date", (add_date, 4));
    m.insert("time.clock", (clock, 1));
    m.insert("time.date", (date, 1));
    m.insert("time.diff", (diff, 2));
    m.insert("time.format", (format, 1));
    m.insert("time.now_ns", (now_ns, 0));
}

fn add_date(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.add_date";
    ensure_args_count(span, name, params, args, 4)?;

    let (datetime, _) = parse_epoch(name, &params[0], &args[0])?;
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

    let (datetime, _) = parse_epoch(name, &params[0], &args[0])?;

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

    let (datetime, _) = parse_epoch(name, &params[0], &args[0])?;

    Ok(Vec::from([
        (datetime.year() as u64).into(),
        (datetime.month() as u64).into(),
        (datetime.day() as u64).into(),
    ])
    .into())
}

// Adapted from the official Go implementation:
// https://github.com/open-policy-agent/opa/blob/eb17a716b97720a27c6569395ba7c4b7409aae87/topdown/time.go#L179-L243
fn diff(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.diff";
    ensure_args_count(span, name, params, args, 2)?;

    let (datetime1, _) = parse_epoch(name, &params[0], &args[0])?;
    let (datetime2, _) = parse_epoch(name, &params[1], &args[1])?;

    // Make sure both datetimes in the same timezone
    let datetime2 = datetime2.with_timezone(&datetime1.timezone());

    // Make sure `datetime1` is always the smallest one
    let (datetime1, datetime2) = if datetime1 > datetime2 {
        (datetime2, datetime1)
    } else {
        (datetime1, datetime2)
    };

    let mut year = datetime2.year() - datetime1.year();
    let mut month = datetime2.month() as i32 - datetime1.month() as i32;
    let mut day = datetime2.day() as i32 - datetime1.day() as i32;
    let mut hour = datetime2.hour() as i32 - datetime1.hour() as i32;
    let mut min = datetime2.minute() as i32 - datetime1.minute() as i32;
    let mut sec = datetime2.second() as i32 - datetime1.second() as i32;

    // Normalize negative values
    if sec < 0 {
        sec += 60;
        min -= 1;
    }
    if min < 0 {
        min += 60;
        hour -= 1;
    }
    if hour < 0 {
        hour += 24;
        day -= 1;
    }
    if day < 0 {
        // Days in month:
        let t = Utc
            .with_ymd_and_hms(datetime1.year(), datetime1.month(), 32, 0, 0, 0)
            .single()
            .ok_or(anyhow!("Could not convert `ns1` to datetime"))?;
        day += 32 - t.day() as i32;
        month -= 1;
    }
    if month < 0 {
        month += 12;
        year -= 1;
    }

    Ok(Vec::from([
        (year as i64).into(),
        (month as i64).into(),
        (day as i64).into(),
        (hour as i64).into(),
        (min as i64).into(),
        (sec as i64).into(),
    ])
    .into())
}

fn format(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.format";
    ensure_args_count(span, name, params, args, 1)?;

    let (datetime, format) = parse_epoch(name, &params[0], &args[0])?;

    let result = match format {
        Some(format) => datetime.format(&format).to_string(),
        None => datetime.to_rfc3339_opts(SecondsFormat::AutoSi, true),
    };

    Ok(Value::String(result.into()))
}

fn now_ns(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.now_ns";
    ensure_args_count(span, name, params, args, 0)?;

    match Utc::now().timestamp_nanos_opt() {
        Some(val) => Ok(Value::from(val)),
        None => Ok(Value::Undefined),
    }
}

fn parse_epoch(
    fcn: &str,
    arg: &Expr,
    val: &Value,
) -> Result<(DateTime<FixedOffset>, Option<String>)> {
    match val {
        Value::Number(num) => {
            let ns = num.as_i64().ok_or_else(|| {
                arg.span()
                    .error("could not convert numeric value of `ns` to int64")
            })?;

            return Ok((Utc.timestamp_nanos(ns).fixed_offset(), None));
        }

        Value::Array(arr) => match arr.as_slice() {
            [Value::Number(num)] => {
                let ns = num.as_i64().ok_or_else(|| {
                    arg.span()
                        .error("could not convert numeric value of `ns` to int64")
                })?;

                return Ok((Utc.timestamp_nanos(ns).fixed_offset(), None));
            }
            [Value::Number(num), Value::String(tz), rest @ ..] => {
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

                let format = match rest.first() {
                    Some(Value::String(format)) => Some(format.to_string()),
                    Some(other) => {
                        bail!(arg.span().error(&format!(
                            "`{fcn}` expects 3rd element of `ns` to be a `string`. Got `{other}` instead"
                        )))
                    }
                    None => None,
                };

                return Ok((datetime, format));
            }
            _ => {}
        },

        _ => {}
    }

    bail!(arg.span().error(&format!(
        "`{fcn}` expects `ns` to be a `number` or `array[number, string]`. Got `{val}` instead"
    )))
}
