// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]
use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{ensure_args_count, ensure_numeric, ensure_string};
use crate::lexer::Span;
use crate::value::Value;
use crate::*;

use anyhow::{bail, Result};

use jiff::{civil::Weekday, tz::TimeZone, Span as TimeSpan, Timestamp, ZonedDateTime};

use super::datetime::{format_rfc3339, parse_rfc3339};

pub(in crate::builtins) mod compat;
mod diff;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("time.add_date", (add_date, 4));
    m.insert("time.clock", (clock, 1));
    m.insert("time.date", (date, 1));
    m.insert("time.diff", (diff, 2));
    m.insert("time.format", (format, 1));
    m.insert("time.now_ns", (now_ns, 0));
    m.insert("time.parse_duration_ns", (parse_duration_ns, 1));
    m.insert("time.parse_ns", (parse_ns, 2));
    m.insert("time.parse_rfc3339_ns", (parse_rfc3339_ns, 1));
    m.insert("time.weekday", (weekday, 1));
}

fn add_date(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "time.add_date";
    ensure_args_count(span, name, params, args, 4)?;

    let (datetime, _) = parse_epoch(name, &params[0], &args[0])?;
    let years = ensure_i32(name, &params[1], &args[1])?;
    let months = ensure_i32(name, &params[2], &args[2])?;
    let days = ensure_i32(name, &params[3], &args[3])?;

    let Some(new_year) = i32::from(datetime.year())
        .checked_add(years)
        .and_then(|year| i16::try_from(year).ok())
    else {
        return Ok(Value::Undefined);
    };

    // Replacing a year rejects February 29 in a non-leap year, whereas
    // adding months constrains the day to the end of the destination month.
    let result = datetime
        .with()
        .year(new_year)
        .build()
        .and_then(|dt| dt.checked_add(TimeSpan::new().try_months(months)?))
        .and_then(|dt| dt.checked_add(TimeSpan::new().try_days(days)?));
    match result {
        Ok(dt) => {
            safe_timestamp_nanos(span, strict, dt.timestamp().as_nanosecond().try_into().ok())
        }
        Err(_) => Ok(Value::Undefined),
    }
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

fn diff(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.diff";
    ensure_args_count(span, name, params, args, 2)?;

    let (datetime1, _) = parse_epoch(name, &params[0], &args[0])?;
    let (datetime2, _) = parse_epoch(name, &params[1], &args[1])?;

    let (year, month, day, hour, min, sec) = diff::diff_between_datetimes(datetime1, datetime2)?;

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
        Some(format) => compat::format(&datetime, layout_with_predefined_formats(&format))?,
        None => format_rfc3339(&datetime, true)?,
    };

    Ok(Value::String(result.into()))
}

fn now_ns(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "time.now_ns";
    ensure_args_count(span, name, params, args, 0)?;

    safe_timestamp_nanos(
        span,
        strict,
        Timestamp::now().as_nanosecond().try_into().ok(),
    )
}

fn parse_duration_ns(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    strict: bool,
) -> Result<Value> {
    let name = "time.parse_duration_ns";
    ensure_args_count(span, name, params, args, 1)?;

    let value = ensure_string(name, &params[0], &args[0])?;
    let dur = compat::parse_duration(value.as_ref()).map_err(anyhow::Error::msg)?;
    safe_timestamp_nanos(span, strict, dur.as_nanos().try_into().ok())
}

fn parse_ns(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "time.parse_ns";
    ensure_args_count(span, name, params, args, 2)?;

    let layout = ensure_string(name, &params[0], &args[0])?;
    let value = ensure_string(name, &params[1], &args[1])?;

    let datetime = compat::parse(layout_with_predefined_formats(&layout), &value)
        .map_err(|err| anyhow::anyhow!("Failed to parse datetime: {}", err))?;
    safe_timestamp_nanos(
        span,
        strict,
        datetime.timestamp().as_nanosecond().try_into().ok(),
    )
}

fn parse_rfc3339_ns(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    strict: bool,
) -> Result<Value> {
    let name = "time.parse_rfc3339_ns";
    ensure_args_count(span, name, params, args, 1)?;

    let value = ensure_string(name, &params[0], &args[0])?;

    let datetime = parse_rfc3339(&value)
        .map_err(|err| anyhow::anyhow!("Failed to parse datetime: {}", err))?;
    safe_timestamp_nanos(
        span,
        strict,
        datetime.timestamp().as_nanosecond().try_into().ok(),
    )
}

fn weekday(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "time.weekday";
    ensure_args_count(span, name, params, args, 1)?;

    let (datetime, _) = parse_epoch(name, &params[0], &args[0])?;

    let weekday = match datetime.weekday() {
        Weekday::Monday => "Monday",
        Weekday::Tuesday => "Tuesday",
        Weekday::Wednesday => "Wednesday",
        Weekday::Thursday => "Thursday",
        Weekday::Friday => "Friday",
        Weekday::Saturday => "Saturday",
        Weekday::Sunday => "Sunday",
    };

    Ok(Value::String(weekday.into()))
}

fn ensure_i32(name: &str, arg: &Expr, v: &Value) -> Result<i32> {
    ensure_numeric(name, arg, v)?
        .as_i64()
        .and_then(|n| n.try_into().ok())
        .ok_or_else(|| arg.span().error("could not convert to int32"))
}

fn safe_timestamp_nanos(span: &Span, strict: bool, nanos: Option<i64>) -> Result<Value> {
    match nanos {
        Some(ns) => Ok(Value::Number(ns.into())),
        None if strict => {
            bail!(span.error("time outside of valid range"))
        }
        None => Ok(Value::Undefined),
    }
}

fn parse_epoch(fcn: &str, arg: &Expr, val: &Value) -> Result<(ZonedDateTime, Option<String>)> {
    match val {
        Value::Number(num) => {
            let ns = num.as_i64().ok_or_else(|| {
                arg.span()
                    .error("could not convert numeric value of `ns` to int64")
            })?;

            return Ok((
                Timestamp::from_nanosecond(i128::from(ns))?.to_zoned_datetime(TimeZone::UTC),
                None,
            ));
        }

        Value::Array(arr) => match arr.as_slice() {
            [Value::Number(num)] => {
                let ns = num.as_i64().ok_or_else(|| {
                    arg.span()
                        .error("could not convert numeric value of `ns` to int64")
                })?;

                return Ok((
                    Timestamp::from_nanosecond(i128::from(ns))?.to_zoned_datetime(TimeZone::UTC),
                    None,
                ));
            }
            [Value::Number(num), Value::String(tz), rest @ ..] => {
                let ns = num.as_i64().ok_or_else(|| {
                    arg.span()
                        .error("could not convert numeric value of `ns` to int64")
                })?;

                let zone = match tz.as_ref() {
                    "UTC" | "" => TimeZone::UTC,
                    "Local" => TimeZone::try_system()?,
                    _ => TimeZone::get(tz)?,
                };
                let timestamp = Timestamp::from_nanosecond(i128::from(ns))?;
                let zoned = timestamp.to_zoned_datetime(zone);
                // Preserve the fixed-offset arithmetic used by these builtins.
                let datetime = zoned.with_time_zone(TimeZone::fixed(zoned.offset()));

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

fn layout_with_predefined_formats(format: &str) -> &str {
    match format {
        "ANSIC" => "Mon Jan _2 15:04:05 2006",
        "UnixDate" => "Mon Jan _2 15:04:05 MST 2006",
        "RubyDate" => "Mon Jan 02 15:04:05 -0700 2006",
        "RFC822" => "02 Jan 06 15:04 MST",
        // RFC822 with numeric zone
        "RFC822Z" => "02 Jan 06 15:04 -0700",
        "RFC850" => "Monday, 02-Jan-06 15:04:05 MST",
        "RFC1123" => "Mon, 02 Jan 2006 15:04:05 MST",
        // RFC1123 with numeric zone
        "RFC1123Z" => "Mon, 02 Jan 2006 15:04:05 -0700",
        "RFC3339" => "2006-01-02T15:04:05Z07:00",
        "RFC3339Nano" => "2006-01-02T15:04:05.999999999Z07:00",
        other => other,
    }
}
