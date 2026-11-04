// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::lexer::Span;
use crate::value::{Array, Value};

use alloc::format;
use anyhow::{anyhow, bail, Result};

use super::{FormatSpec, MAX_SPRINTF_WIDTH_OR_PRECISION};

fn parse_usize(bytes: &[u8], cursor: &mut usize) -> Result<Option<usize>> {
    let start = *cursor;
    let mut value = 0usize;
    while *cursor < bytes.len() && bytes[*cursor].is_ascii_digit() {
        value = value
            .checked_mul(10)
            .and_then(|value| value.checked_add((bytes[*cursor] - b'0') as usize))
            .filter(|value| *value <= MAX_SPRINTF_WIDTH_OR_PRECISION)
            .ok_or_else(|| anyhow!("sprintf width or precision is too large"))?;
        *cursor += 1;
    }
    Ok((*cursor != start).then_some(value))
}

fn parse_index(bytes: &[u8], cursor: &mut usize) -> Result<Option<usize>> {
    if bytes.get(*cursor) != Some(&b'[') {
        return Ok(None);
    }
    let mut end = *cursor + 1;
    let Some(index) = parse_usize(bytes, &mut end)? else {
        bail!("sprintf argument index must contain a decimal number");
    };
    if bytes.get(end) != Some(&b']') {
        bail!("invalid sprintf argument index");
    }
    *cursor = end + 1;
    Ok(Some(index.checked_sub(1).unwrap_or(usize::MAX)))
}

fn take_integer(args: &Array, args_idx: &mut usize, args_span: &Span) -> Result<Option<i64>> {
    let index = *args_idx;
    let Some(value) = args.get(index) else {
        bail!(args_span.error(format!("no argument specified for format verb {index}").as_str()));
    };
    *args_idx += 1;
    match value {
        Value::Number(number) if number.is_integer() => {
            number.as_i64().map(Some).ok_or_else(|| {
                args_span.error("sprintf width or precision is outside the supported range")
            })
        }
        _ => Ok(None),
    }
}

fn checked_dynamic_value(value: u64, args_span: &Span) -> Result<usize> {
    usize::try_from(value)
        .ok()
        .filter(|value| *value <= MAX_SPRINTF_WIDTH_OR_PRECISION)
        .ok_or_else(|| args_span.error("sprintf width or precision is outside the supported range"))
}

pub(super) fn parse(
    format: &str,
    start: usize,
    args: &Array,
    args_idx: &mut usize,
    reordered: &mut bool,
    args_span: &Span,
    format_span: &Span,
) -> Result<(FormatSpec, char, usize)> {
    let bytes = format.as_bytes();
    let mut cursor = start;
    let mut spec = FormatSpec::default();

    while cursor < bytes.len() {
        match bytes[cursor] {
            b'#' => spec.flags.alternate = true,
            b'0' => spec.flags.zero = true,
            b'+' => spec.flags.plus = true,
            b'-' => spec.flags.minus = true,
            b' ' => spec.flags.space = true,
            _ => break,
        }
        cursor += 1;
    }

    if let Some(index) = parse_index(bytes, &mut cursor)? {
        if index < args.len() {
            *args_idx = index;
        } else {
            spec.bad_index = true;
        }
        *reordered = true;
        if matches!(bytes.get(cursor), Some(b'0'..=b'9' | b'.')) {
            spec.bad_index = true;
            // A valid index remains selected even when the directive is invalid.
        }
    }

    if bytes.get(cursor) == Some(&b'*') {
        cursor += 1;
        let width = if spec.bad_index && *args_idx >= args.len() {
            None
        } else {
            take_integer(args, args_idx, args_span)?
        };
        if width.is_none() {
            spec.bad_width = true;
        }
        let width = width.unwrap_or(0);
        if width < 0 {
            spec.flags.minus = true;
            spec.flags.zero = false;
            spec.width = Some(checked_dynamic_value(width.unsigned_abs(), args_span)?);
        } else {
            spec.width = Some(checked_dynamic_value(width as u64, args_span)?);
        }
    } else {
        spec.width = parse_usize(bytes, &mut cursor)?;
    }

    if bytes.get(cursor) == Some(&b'.') {
        cursor += 1;
        if let Some(index) = parse_index(bytes, &mut cursor)? {
            if index < args.len() {
                *args_idx = index;
            } else {
                spec.bad_index = true;
            }
            *reordered = true;
        }
        if bytes.get(cursor) == Some(&b'*') {
            cursor += 1;
            let precision = if spec.bad_index && *args_idx >= args.len() {
                None
            } else {
                take_integer(args, args_idx, args_span)?
            };
            if let Some(precision) = precision.filter(|n| *n >= 0) {
                spec.precision = Some(checked_dynamic_value(precision as u64, args_span)?);
            } else {
                spec.bad_precision = true;
            }
        } else {
            spec.precision = Some(parse_usize(bytes, &mut cursor)?.unwrap_or_default());
        }
    }

    if let Some(index) = parse_index(bytes, &mut cursor)? {
        if index < args.len() {
            *args_idx = index;
        } else {
            spec.bad_index = true;
        }
        *reordered = true;
    }

    let Some(rest) = format.get(cursor..) else {
        bail!(format_span.error("invalid byte offset in sprintf format string"));
    };
    let Some(verb) = rest.chars().next() else {
        bail!(format_span.error("missing format verb at end of format string"));
    };
    Ok((spec, verb, cursor + verb.len_utf8()))
}
