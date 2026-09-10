// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(
    clippy::unseparated_literal_suffix,
    clippy::as_conversions,
    clippy::pattern_type_mismatch
)]

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{
    enforce_limit, ensure_args_count, ensure_array, ensure_numeric, ensure_object, ensure_string,
    ensure_string_collection,
};
use crate::lexer::Span;
use crate::number::Number;
use crate::value::Value;
use crate::*;

use anyhow::{bail, Result};

mod go_is_print;
mod sprintf_format;

pub fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("concat", (concat, 2));
    m.insert("contains", (contains, 2));
    m.insert("endswith", (endswith, 2));
    m.insert("format_int", (format_int, 2));
    m.insert("indexof", (indexof, 2));
    m.insert("indexof_n", (indexof_n, 2));
    m.insert("lower", (lower, 1));
    m.insert("replace", (replace, 3));
    m.insert("split", (split, 2));
    m.insert("sprintf", (sprintf, 2));
    m.insert("startswith", (startswith, 2));
    m.insert("strings.any_prefix_match", (any_prefix_match, 2));
    m.insert("strings.any_suffix_match", (any_suffix_match, 2));
    m.insert("strings.count", (strings_count, 2));
    m.insert("strings.replace_n", (replace_n, 2));
    m.insert("strings.reverse", (reverse, 1));
    m.insert("substring", (substring, 3));
    m.insert("trim", (trim, 2));
    m.insert("trim_left", (trim_left, 2));
    m.insert("trim_prefix", (trim_prefix, 2));
    m.insert("trim_right", (trim_right, 2));
    m.insert("trim_space", (trim_space, 1));
    m.insert("trim_suffix", (trim_suffix, 2));
    m.insert("upper", (upper, 1));
}

fn concat(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "concat";
    ensure_args_count(span, name, params, args, 2)?;
    let delimiter = ensure_string(name, &params[0], &args[0])?;
    let collection = ensure_string_collection(name, &params[1], &args[1])?;
    Ok(Value::String(collection.join(&delimiter).into()))
}

fn contains(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "contains";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.contains(s2.as_ref())))
}

fn endswith(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "endswith";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.ends_with(s2.as_ref())))
}

fn format_int(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "format_int";
    ensure_args_count(span, name, params, args, 2)?;
    let mut n = ensure_numeric(name, &params[0], &args[0])?;
    let mut sign = "";
    if n < Number::from(0u64) {
        n = n.abs();
        sign = "-";
    }
    let n = n.floor();

    let base = ensure_numeric(name, &params[1], &args[1])?;

    let num = match base.as_u64() {
        Some(2) => n.format_bin(),
        Some(8) => n.format_octal(),
        Some(10) => n.format_decimal(),
        Some(16) => n.format_hex(),
        _ => {
            if strict {
                let span = params[1].span();
                bail!(span.error(&format!("`{name}` expects base to be one of 2, 8, 10, 16")));
            }

            return Ok(Value::Undefined);
        }
    };

    Ok(Value::String((sign.to_owned() + &num).into()))
}

fn indexof(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "indexof";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    for (pos, (idx, _)) in s1.char_indices().enumerate() {
        if s1[idx..].starts_with(s2.as_ref()) {
            return Ok(Value::from(Number::from(pos)));
        }
    }
    Ok(Value::from(Number::from(-1i64)))
}

fn indexof_n(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "indexof_n";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;

    let mut positions = vec![];
    for (pos, (idx, _)) in s1.char_indices().enumerate() {
        if s1[idx..].starts_with(s2.as_ref()) {
            positions.push(Value::from(Number::from(pos)));
            // Guard position vector growth while tracking matches.
            enforce_limit()?;
        }
    }
    Ok(Value::from_array(positions))
}

fn lower(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "lower";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.to_lowercase().into()))
}

fn replace(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "replace";
    ensure_args_count(span, name, params, args, 3)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let old = ensure_string(name, &params[1], &args[1])?;
    let new = ensure_string(name, &params[2], &args[2])?;
    Ok(Value::String(s.replace(old.as_ref(), new.as_ref()).into()))
}

fn split(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "replace";
    ensure_args_count(span, name, params, args, 2)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let delimiter = ensure_string(name, &params[1], &args[1])?;

    // Handle https://github.com/microsoft/regorus/issues/291
    let parts: Vec<Value> = if delimiter.as_ref() == "" {
        // If delimiter is "", str::split returns a leading and trailing "" whereas Golang's split doesn't.
        // Therefore avoid str::split and instead return each char as a Value::String.
        s.chars()
            .map(|c| {
                let value = Value::from(c.to_string());
                // Guard part accumulation when splitting into characters.
                enforce_limit()?;
                Ok(value)
            })
            .collect::<Result<Vec<Value>>>()?
    } else {
        s.split(delimiter.as_ref())
            .map(|s| {
                let value = Value::String(s.into());
                // Guard part accumulation when splitting by delimiter.
                enforce_limit()?;
                Ok(value)
            })
            .collect::<Result<Vec<Value>>>()?
    };

    Ok(Value::from(parts))
}

fn to_string(v: &Value, unescape: bool) -> String {
    match v {
        Value::Null => "null".to_owned(),
        Value::Bool(b) => b.to_string(),
        Value::String(s) if unescape => {
            serde_json::to_string(s.as_ref()).unwrap_or(s.as_ref().to_string())
        }
        Value::String(s) => s.as_ref().to_string(),
        Value::Number(n) => n.format_decimal(),
        Value::Array(a) => {
            "[".to_owned()
                + &a.iter()
                    .map(|e| to_string(e, true))
                    .collect::<Vec<String>>()
                    .join(", ")
                + "]"
        }
        Value::Set(s) => {
            "{".to_owned()
                + &s.iter()
                    .map(|e| to_string(e, true))
                    .collect::<Vec<String>>()
                    .join(", ")
                + "}"
        }
        Value::Object(o) => {
            "{".to_owned()
                + &o.iter_sorted()
                    .map(|(k, v)| to_string(k, true) + ": " + &to_string(v, true))
                    .collect::<Vec<String>>()
                    .join(", ")
                + "}"
        }
        Value::Undefined => "#undefined".to_string(),
    }
}

#[derive(Clone, Copy)]
enum Width {
    None,
    LeadingZeros(usize),
    Cell(usize),
    Decimals(usize),
}

#[derive(Clone, Copy, Default)]
struct FormatFlags {
    alternate: bool,
    zero: bool,
    plus: bool,
    minus: bool,
    space: bool,
}

#[derive(Clone, Copy, Default)]
struct FormatSpec {
    flags: FormatFlags,
    width: Option<usize>,
    precision: Option<usize>,
    bad_precision: bool,
}

impl FormatSpec {
    fn legacy_width(self) -> Width {
        match (self.width, self.precision) {
            (_, Some(precision)) => Width::Decimals(precision),
            (Some(width), None) if self.flags.zero && !self.flags.minus => {
                Width::LeadingZeros(width)
            }
            (Some(width), None) => Width::Cell(width),
            (None, None) => Width::None,
        }
    }
}

fn apply_width(w: Width, s: String) -> String {
    match w {
        Width::LeadingZeros(n) if n > s.len() => "0".repeat(n - s.len()) + &s,
        Width::Cell(n) if n > s.len() => " ".repeat(n - s.len()) + &s,
        _ => s,
    }
}

const LOWER_HEX: &[u8; 16] = b"0123456789abcdef";

// Append a string quoted like Go's fmt `%q`. Precision truncates the input by
// Unicode scalar values before quoting, while width pads the quoted result by
// Unicode scalar values. `%+q` forces ASCII escapes and `%#q` uses a raw string
// whenever strconv.CanBackquote permits it.
fn append_go_quoted(out: &mut String, input: &str, spec: FormatSpec) -> Result<()> {
    let input = spec
        .precision
        .map_or(input, |precision| truncate_chars(input, precision));
    let raw = spec.flags.alternate && can_backquote(input);
    let content_len = if raw {
        input.chars().count().saturating_add(2)
    } else {
        go_quoted_len(input, spec.flags.plus, '"')
    };
    let padding = spec.width.unwrap_or_default().saturating_sub(content_len);
    let padding_char = if spec.flags.zero && !spec.flags.minus {
        '0'
    } else {
        ' '
    };

    if !spec.flags.minus {
        append_padding(out, padding, padding_char)?;
    }

    if raw {
        out.push('`');
        for c in input.chars() {
            out.push(c);
            enforce_limit()?;
        }
        out.push('`');
        enforce_limit()?;
    } else {
        append_go_quoted_body(out, input, spec.flags.plus, '"')?;
    }

    if spec.flags.minus {
        append_padding(out, padding, ' ')?;
    }
    Ok(())
}

fn append_go_quoted_body(
    out: &mut String,
    input: &str,
    ascii_only: bool,
    quote: char,
) -> Result<()> {
    out.push(quote);
    for c in input.chars() {
        match c {
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            '\\' => out.push_str("\\\\"),
            '\u{0007}' => out.push_str("\\a"),
            '\u{0008}' => out.push_str("\\b"),
            '\u{000C}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{000B}' => out.push_str("\\v"),
            c if go_is_print::is_print(c) && (!ascii_only || c.is_ascii()) => out.push(c),
            c if (c as u32) <= 0x7f => append_hex_escape(out, 'x', c as u32, 2),
            c if (c as u32) <= 0xffff => append_hex_escape(out, 'u', c as u32, 4),
            c => append_hex_escape(out, 'U', c as u32, 8),
        }
        enforce_limit()?;
    }
    out.push(quote);
    enforce_limit()
}

fn append_padding(out: &mut String, count: usize, padding_char: char) -> Result<()> {
    for _ in 0..count {
        out.push(padding_char);
        enforce_limit()?;
    }
    Ok(())
}

fn can_backquote(s: &str) -> bool {
    s.chars()
        .all(|c| c != '`' && c != '\u{FEFF}' && c != '\u{007F}' && (c >= ' ' || c == '\t'))
}

fn truncate_chars(s: &str, count: usize) -> &str {
    s.char_indices()
        .nth(count)
        .map_or(s, |(byte_index, _)| &s[..byte_index])
}

fn go_quoted_len(s: &str, ascii_only: bool, quote: char) -> usize {
    s.chars().fold(2usize, |len, c| {
        let escaped_len = match c {
            c if c == quote => 2,
            '\\' | '\u{0007}' | '\u{0008}' | '\u{000C}' | '\n' | '\r' | '\t' | '\u{000B}' => 2,
            c if go_is_print::is_print(c) && (!ascii_only || c.is_ascii()) => 1,
            c if (c as u32) <= 0x7f => 4,
            c if (c as u32) <= 0xffff => 6,
            _ => 10,
        };
        len.saturating_add(escaped_len)
    })
}

fn append_go_quoted_rune(out: &mut String, value: i64, spec: FormatSpec) -> Result<()> {
    let rune = u32::try_from(value)
        .ok()
        .and_then(char::from_u32)
        .unwrap_or('\u{FFFD}');
    let mut encoded = [0u8; 4];
    let rune = rune.encode_utf8(&mut encoded);
    let content_len = go_quoted_len(rune, spec.flags.plus, '\'');
    let padding = spec.width.unwrap_or_default().saturating_sub(content_len);
    let padding_char = if spec.flags.zero && !spec.flags.minus {
        '0'
    } else {
        ' '
    };

    if !spec.flags.minus {
        append_padding(out, padding, padding_char)?;
    }
    append_go_quoted_body(out, rune, spec.flags.plus, '\'')?;
    if spec.flags.minus {
        append_padding(out, padding, ' ')?;
    }
    Ok(())
}

fn append_go_quoted_value(out: &mut String, value: &Value, spec: FormatSpec) -> Result<()> {
    match value {
        Value::String(value) => append_go_quoted(out, value.as_ref(), spec),
        Value::Number(Number::Int(value)) => append_go_quoted_rune(out, *value, spec),
        Value::Number(Number::UInt(value)) if *value <= i64::MAX as u64 => {
            append_go_quoted_rune(out, *value as i64, spec)
        }
        Value::Number(number @ (Number::UInt(_) | Number::BigInt(_))) => {
            out.push_str("%!q(big.Int=");
            out.push_str(&number.format_decimal());
            out.push(')');
            enforce_limit()
        }
        Value::Number(Number::Float(value)) => {
            out.push_str("%!q(float64=");
            append_go_float_value(out, value, spec)?;
            out.push(')');
            enforce_limit()
        }
        value => {
            let mut rendered = String::new();
            append_value_string(&mut rendered, value, false)?;
            append_go_quoted(out, &rendered, spec)
        }
    }
}

// Go renders an invalid %q float operand using the supplied flags, width, and
// precision as a nested %v conversion.
fn append_go_float_value(out: &mut String, value: &f64, spec: FormatSpec) -> Result<()> {
    let value = if let Some(precision) = spec.precision {
        format_go_float_v(*value, precision, spec.flags.alternate)
    } else {
        format_go_float_v(*value, 6, spec.flags.alternate)
    };
    let padding = spec.width.unwrap_or_default().saturating_sub(value.len());
    let padding_char = if spec.flags.zero && !spec.flags.minus {
        '0'
    } else {
        ' '
    };
    if !spec.flags.minus {
        append_padding(out, padding, padding_char)?;
    }
    out.push_str(&value);
    enforce_limit()?;
    if spec.flags.minus {
        append_padding(out, padding, ' ')?;
    }
    Ok(())
}

// Go's %v precision for floats is the number of significant digits, using the
// same general-format threshold as %g. The alternate form retains trailing
// zeroes up to that precision.
fn format_go_float_v(value: f64, precision: usize, alternate: bool) -> String {
    if !value.is_finite() || value == 0.0 {
        return value.to_string();
    }
    let precision = precision.max(1);
    let exponent = value.abs().log10().floor() as i32;
    let scientific = exponent >= precision as i32 || exponent < -4;
    let mut rendered = if scientific {
        let fraction_digits = precision - 1;
        let rendered = format!("{value:.fraction_digits$e}");
        let (mantissa, exponent) = rendered
            .split_once('e')
            .expect("scientific format has exponent");
        let mantissa = if alternate {
            mantissa.to_owned()
        } else {
            mantissa
                .trim_end_matches('0')
                .trim_end_matches('.')
                .to_owned()
        };
        let exponent = exponent.parse::<i32>().expect("Rust exponent is numeric");
        format!("{mantissa}e{exponent:+03}")
    } else {
        let fraction_digits = (precision as i32 - exponent - 1).max(0) as usize;
        format!("{value:.fraction_digits$}")
    };
    if !alternate && !scientific {
        rendered = rendered
            .trim_end_matches('0')
            .trim_end_matches('.')
            .to_owned();
    }
    rendered
}

fn append_value_string(out: &mut String, value: &Value, unescape: bool) -> Result<()> {
    match value {
        Value::Null => out.push_str("null"),
        Value::Bool(value) => out.push_str(&value.to_string()),
        Value::String(value) if unescape => out.push_str(
            &serde_json::to_string(value.as_ref()).unwrap_or_else(|_| value.as_ref().to_string()),
        ),
        Value::String(value) => out.push_str(value.as_ref()),
        Value::Number(value) => out.push_str(&value.format_decimal()),
        Value::Array(values) => {
            out.push('[');
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                append_value_string(out, value, true)?;
                enforce_limit()?;
            }
            out.push(']');
        }
        Value::Set(values) => {
            out.push('{');
            for (index, value) in values.iter().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                append_value_string(out, value, true)?;
                enforce_limit()?;
            }
            out.push('}');
        }
        Value::Object(values) => {
            out.push('{');
            for (index, (key, value)) in values.iter_sorted().enumerate() {
                if index > 0 {
                    out.push_str(", ");
                }
                append_value_string(out, key, true)?;
                out.push_str(": ");
                append_value_string(out, value, true)?;
                enforce_limit()?;
            }
            out.push('}');
        }
        Value::Undefined => out.push_str("#undefined"),
    }
    enforce_limit()
}

fn append_hex_escape(out: &mut String, prefix: char, value: u32, digits: usize) {
    out.push('\\');
    out.push(prefix);
    for digit in (0..digits).rev() {
        let nibble = ((value >> (digit * 4)) & 0x0f) as usize;
        out.push(LOWER_HEX[nibble] as char);
    }
}

fn sprintf(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "sprintf";
    ensure_args_count(span, name, params, args, 2)?;
    let fmt = ensure_string(name, &params[0], &args[0])?;
    let args = ensure_array(name, &params[1], args[1].clone())?;

    let mut s = String::default();
    let mut args_idx = 0usize;
    let mut cursor = 0usize;
    let mut reordered = false;
    let args_span = params[1].span();
    let format_span = params[0].span();
    loop {
        let Some(percent_offset) = fmt[cursor..].find('%') else {
            s.push_str(&fmt[cursor..]);
            enforce_limit()?;
            break;
        };
        let percent = cursor + percent_offset;
        s.push_str(&fmt[cursor..percent]);
        enforce_limit()?;

        let (spec, verb, next_cursor) = sprintf_format::parse(
            fmt.as_ref(),
            percent + 1,
            args.as_ref(),
            &mut args_idx,
            &mut reordered,
            args_span,
            format_span,
        )?;
        cursor = next_cursor;

        if verb == '%' {
            s.push('%');
            enforce_limit()?;
            continue;
        }

        if verb != 'q'
            && (spec.flags.alternate || spec.flags.plus || spec.flags.minus || spec.flags.space)
        {
            bail!(format_span.error(
                "sprintf flags '#', '+', '-' and space are currently supported only for %q"
            ));
        }

        if verb != 'q' && spec.width.is_some() && spec.precision.is_some() {
            bail!(format_span
                .error("sprintf combined width and precision are currently supported only for %q"));
        }

        if args_idx >= args.len() {
            bail!(args_span
                .error(format!("no argument specified for format verb {args_idx}").as_str()));
        }
        let arg = &args[args_idx];
        args_idx += 1;
        if spec.bad_precision {
            s.push_str("%!(BADPREC)");
            enforce_limit()?;
        }
        let width = spec.legacy_width();

        // Handle Golang flags.
        let emit_sign = false;
        let leave_space_for_elided_sign = false;

        let get_sign_value = |f: &Number| match (emit_sign, f) {
            (_, v) if v < &Number::from(0.0) => ("-", v.clone()),
            (true, v) => ("+", v.clone()),
            (false, v) if leave_space_for_elided_sign => (" ", v.clone()),
            (false, v) => ("", v.clone()),
        };

        // Handle Golang printing verbs.
        // https://pkg.go.dev/fmt
        match (verb, arg) {
            ('s', Value::String(sv)) => s += sv.as_ref(),
            ('s', v) => s += &to_string(v, false),

            ('v', _) => s += &to_string(arg, false),
            ('b', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += v.format_bin().as_str()
            }
            ('c', Value::Number(f)) if f.is_integer() => {
                // TODO: range error
                let ch_opt = f.as_u64().map(|ival| char::from_u32(ival as u32));
                match ch_opt {
                    Some(Some(c)) => s.push(c),
                    _ => {
                        bail!(args_span.error(
                            format!("invalid value {} for format verb c.", f.format_decimal())
                                .as_str()
                        ))
                    }
                }
            }
            ('d', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += apply_width(width, v.format_decimal()).as_str()
            }
            ('o', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += apply_width(width, "0O".to_owned() + &v.format_octal()).as_str()
            }
            ('O', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += apply_width(width, "0o".to_owned() + &v.format_octal()).as_str()
            }
            ('x', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += apply_width(width, v.format_hex()).as_str()
            }
            ('X', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += apply_width(width, v.format_big_hex()).as_str()
            }
            ('e', Value::Number(f)) => s += &f.format_scientific(),
            ('E', Value::Number(f)) => s += &f.format_scientific().replace('e', "E"),
            ('f' | 'F', Value::Number(f)) => {
                s += &match width {
                    Width::Decimals(d) => f.format_decimal_with_width(d as u32),
                    _ => apply_width(width, f.format_decimal()),
                }
            }
            ('g', Value::Number(f)) => {
                let (sign, v) = get_sign_value(f);
                let v = match v.as_f64() {
                    Some(v) => v,
                    _ => bail!(span.error("cannot print large float using g format specified")),
                };
                s += sign;
                let bits = v.to_bits();
                let exponent = (bits >> 52) & 0x7ff;
                // TODO: what is large exponent?
                if exponent > 32 {
                    s += format!("{v:e}").as_str()
                } else {
                    s += format!("{v}").as_str()
                }
            }
            ('G', Value::Number(f)) => {
                let (sign, v) = get_sign_value(f);
                let v = match v.as_f64() {
                    Some(v) => v,
                    _ => bail!("cannot print large float using g format specified"),
                };
                s += sign;
                let bits = v.to_bits();
                let exponent = (bits >> 52) & 0x7ff;
                // TODO: what is large exponent?
                if exponent > 32 {
                    s += format!("{v:E}").as_str()
                } else {
                    s += format!("{v}").as_str()
                }
            }
            ('q', value) => append_go_quoted_value(&mut s, value, spec)?,

            (_, Value::Number(_)) => {
                bail!(args_span.error(&format!("number specified for format verb {verb}.")));
            }

            ('T', _) | ('p', _) => {
                bail!(args_span.error("Go-syntax format verbs %#v, %p and %T are not supported."));
            }
            _ => {}
        }
    }

    if !reordered && args_idx < args.len() {
        bail!(args_span.error(
            format!(
                "extra arguments ({}) specified for {args_idx} format verbs.",
                args.len()
            )
            .as_str()
        ));
    }

    Ok(Value::String(s.into()))
}

fn any_prefix_match(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    strict: bool,
) -> Result<Value> {
    let name = "strings.any_prefix_match";
    ensure_args_count(span, name, params, args, 2)?;

    let search = match &args[0] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => {
            match ensure_string_collection(name, &params[0], &args[0]) {
                Ok(c) => c,
                Err(e) if strict => return Err(e),
                _ => return Ok(Value::Undefined),
            }
        }
        _ if strict => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
        _ => return Ok(Value::Undefined),
    };

    let base = match &args[1] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => {
            match ensure_string_collection(name, &params[1], &args[1]) {
                Ok(c) => c,
                Err(e) if strict => return Err(e),
                _ => return Ok(Value::Undefined),
            }
        }
        _ if strict => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
        _ => return Ok(Value::Undefined),
    };

    Ok(Value::Bool(
        search.iter().any(|s| base.iter().any(|b| s.starts_with(b))),
    ))
}

fn any_suffix_match(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    strict: bool,
) -> Result<Value> {
    let name = "strings.any_suffix_match";
    ensure_args_count(span, name, params, args, 2)?;

    let search = match &args[0] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => {
            match ensure_string_collection(name, &params[0], &args[0]) {
                Ok(c) => c,
                Err(e) if strict => return Err(e),
                _ => return Ok(Value::Undefined),
            }
        }
        _ if strict => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
        _ => return Ok(Value::Undefined),
    };

    let base = match &args[1] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => {
            match ensure_string_collection(name, &params[1], &args[1]) {
                Ok(c) => c,
                Err(e) if strict => return Err(e),
                _ => return Ok(Value::Undefined),
            }
        }
        _ if strict => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
        _ => return Ok(Value::Undefined),
    };

    Ok(Value::Bool(
        search.iter().any(|s| base.iter().any(|b| s.ends_with(b))),
    ))
}

fn strings_count(
    span: &Span,
    params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let name = "strings.count";
    ensure_args_count(span, name, params, args, 2)?;

    let search = ensure_string(name, &params[0], &args[0])?;
    let substring = ensure_string(name, &params[0], &args[1])?;

    Ok(Value::from(
        search
            .as_bytes()
            .windows(substring.len())
            .filter(|&w| w == substring.as_bytes())
            .count(),
    ))
}

fn startswith(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "startswith";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.starts_with(s2.as_ref())))
}

fn replace_n(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trim";
    ensure_args_count(span, name, params, args, 2)?;
    let obj = ensure_object(name, &params[0], args[0].clone())?;
    let mut s = ensure_string(name, &params[1], &args[1])?;

    let span = params[0].span();
    for item in obj.as_ref().iter_sorted() {
        match item {
            (Value::String(k), Value::String(v)) => {
                s = s.replace(k.as_ref(), v.as_ref()).into();
            }
            _ => {
                bail!(span.error(
                    format!("`{name}` expects string keys and values in pattern object.").as_str()
                ))
            }
        }
    }

    Ok(Value::String(s.clone()))
}

fn reverse(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "reverse";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.chars().rev().collect::<String>().into()))
}

fn substring(span: &Span, params: &[Ref<Expr>], args: &[Value], strict: bool) -> Result<Value> {
    let name = "substring";
    ensure_args_count(span, name, params, args, 3)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let offset = ensure_numeric(name, &params[1], &args[1])?;
    let length = ensure_numeric(name, &params[2], &args[2])?;

    match (offset.as_i64(), length.as_i64()) {
        (Some(offset), _) if offset < 0 && strict => {
            bail!(params[1].span().error("negative offset"))
        }
        (Some(offset), _) if offset < 0 => Ok(Value::Undefined),
        (Some(offset), Some(length)) => {
            let start = s.chars().skip(offset as usize);
            let length = if length < 0 { s.len() } else { length as usize };
            Ok(Value::String(start.take(length).collect::<String>().into()))
        }
        _ => Ok(Value::String("".into())),
    }
}

fn trim(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trim";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(s1.trim_matches(|c| s2.contains(c)).into()))
}

fn trim_left(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trim_left";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(
        s1.trim_start_matches(|c| s2.contains(c)).into(),
    ))
}

fn trim_prefix(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trim_prefix";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(match s1.strip_prefix(s2.as_ref()) {
        Some(s) => s.into(),
        _ => s1,
    }))
}

fn trim_right(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trim_right";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(
        s1.trim_end_matches(|c| s2.contains(c)).into(),
    ))
}

fn trim_space(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trim_space";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.trim().into()))
}

fn trim_suffix(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "trim_suffix";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(match s1.strip_suffix(s2.as_ref()) {
        Some(s) => s.into(),
        _ => s1,
    }))
}

fn upper(span: &Span, params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let name = "upper";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.to_uppercase().into()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn go_quote_string(s: &str) -> String {
        let mut out = String::new();
        append_go_quoted(&mut out, s, FormatSpec::default()).expect("quoting must succeed");
        out
    }

    // Reference values below were captured from `sprintf("%q", [...])`
    // evaluated with OPA (github.com/open-policy-agent/opa), which in turn
    // delegates to Go's `strconv.Quote`.
    #[test]
    fn quote_string_matches_go_strconv_quote() {
        assert_eq!(go_quote_string("foo"), "\"foo\"");
        assert_eq!(go_quote_string(""), "\"\"");
        assert_eq!(go_quote_string("a\"b"), "\"a\\\"b\"");
        assert_eq!(go_quote_string("back\\slash"), "\"back\\\\slash\"");
        assert_eq!(go_quote_string("tab\there"), "\"tab\\there\"");
        assert_eq!(go_quote_string("nl\nhere"), "\"nl\\nhere\"");
        assert_eq!(go_quote_string("cr\rhere"), "\"cr\\rhere\"");
        assert_eq!(go_quote_string("emoji\u{1F642}"), "\"emoji\u{1F642}\"");
        assert_eq!(
            go_quote_string("\u{044E}\u{043D}\u{0456}\u{043A}\u{043E}\u{0434}"),
            "\"\u{044E}\u{043D}\u{0456}\u{043A}\u{043E}\u{0434}\""
        );
        // %q does NOT HTML-escape < > & (unlike json.marshal).
        assert_eq!(go_quote_string("a<b>&c"), "\"a<b>&c\"");

        // Short escapes for the other named control characters.
        assert_eq!(go_quote_string("\u{0007}"), "\"\\a\"");
        assert_eq!(go_quote_string("\u{0008}"), "\"\\b\"");
        assert_eq!(go_quote_string("\u{000C}"), "\"\\f\"");
        assert_eq!(go_quote_string("\u{000B}"), "\"\\v\"");

        // Other C0 control characters fall back to \xNN.
        assert_eq!(go_quote_string("x\u{001F}y"), "\"x\\x1fy\"");
        // DEL (0x7f) is also escaped as \x7f.
        assert_eq!(go_quote_string("x\u{007F}y"), "\"x\\x7fy\"");
        // Non-breaking space is a non-ASCII-space separator: not printable,
        // and within the BMP so it uses \uNNNN.
        assert_eq!(go_quote_string("x\u{00A0}y"), "\"x\\u00a0y\"");
        // Format, private-use, noncharacter, and unassigned scalars are not
        // printable under Go's Unicode category definition.
        assert_eq!(go_quote_string("x\u{00AD}y"), "\"x\\u00ady\"");
        assert_eq!(go_quote_string("x\u{200B}y"), "\"x\\u200by\"");
        assert_eq!(go_quote_string("x\u{E000}y"), "\"x\\ue000y\"");
        assert_eq!(go_quote_string("x\u{FDD0}y"), "\"x\\ufdd0y\"");
        assert_eq!(go_quote_string("x\u{0378}y"), "\"x\\u0378y\"");
        // Astral-plane printable characters are left as-is.
        assert_eq!(go_quote_string("x\u{1F600}y"), "\"x\u{1F600}y\"");
    }

    #[test]
    fn quote_string_applies_supported_width_and_precision() {
        let quote = |input, spec| {
            let mut out = String::new();
            append_go_quoted(&mut out, input, spec).expect("quoting must succeed");
            out
        };

        assert_eq!(
            quote(
                "foo",
                FormatSpec {
                    width: Some(10),
                    ..FormatSpec::default()
                }
            ),
            "     \"foo\""
        );
        assert_eq!(
            quote(
                "a",
                FormatSpec {
                    flags: FormatFlags {
                        zero: true,
                        ..FormatFlags::default()
                    },
                    width: Some(5),
                    precision: None,
                    ..FormatSpec::default()
                }
            ),
            "00\"a\""
        );
        assert_eq!(
            quote(
                "abcdef",
                FormatSpec {
                    precision: Some(3),
                    ..FormatSpec::default()
                }
            ),
            "\"abc\""
        );
        assert_eq!(
            quote(
                "abc",
                FormatSpec {
                    precision: Some(0),
                    ..FormatSpec::default()
                }
            ),
            "\"\""
        );
        assert_eq!(
            quote(
                "\u{1F642}",
                FormatSpec {
                    width: Some(6),
                    ..FormatSpec::default()
                }
            ),
            "   \"\u{1F642}\""
        );
        assert_eq!(
            quote(
                "\u{1F642}x",
                FormatSpec {
                    precision: Some(1),
                    ..FormatSpec::default()
                }
            ),
            "\"\u{1F642}\""
        );
    }
}
