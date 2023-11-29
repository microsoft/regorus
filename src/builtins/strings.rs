// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::builtins::utils::{
    ensure_args_count, ensure_array, ensure_numeric, ensure_object, ensure_string,
    ensure_string_collection,
};
use crate::lexer::Span;
use crate::number::Number;
use crate::value::Value;

use std::collections::HashMap;

use anyhow::{bail, Result};

pub fn register(m: &mut HashMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("concat", (concat, 2));
    m.insert("contains", (contains, 2));
    m.insert("endswith", (endswith, 2));
    m.insert("format_int", (format_int, 2));
    m.insert("indexof", (indexof, 2));
    // TODO: implement this correctly.
    //m.insert("indexof_n", (indexof_n, 2));
    m.insert("lower", (lower, 1));
    m.insert("replace", (replace, 3));
    m.insert("split", (split, 2));
    m.insert("sprintf", (sprintf, 2));
    m.insert("startswith", (startswith, 2));
    m.insert("strings.any_prefix_match", (any_prefix_match, 2));
    m.insert("strings.any_suffix_match", (any_suffix_match, 2));
    m.insert("strings.replace_n", (replace_n, 2));
    m.insert("strings.reverse", (reverse, 1));
    m.insert("strings.substring", (substring, 3));
    m.insert("trim", (trim, 2));
    m.insert("trim_left", (trim_left, 2));
    m.insert("trim_prefix", (trim_prefix, 2));
    m.insert("trim_right", (trim_right, 2));
    m.insert("trim_space", (trim_space, 1));
    m.insert("trim_suffix", (trim_suffix, 2));
    m.insert("upper", (upper, 1));
}

fn concat(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "concat";
    ensure_args_count(span, name, params, args, 2)?;
    let delimiter = ensure_string(name, &params[0], &args[0])?;
    let collection = ensure_string_collection(name, &params[1], &args[1])?;
    Ok(Value::String(collection.join(&delimiter).into()))
}

fn contains(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "contains";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.contains(s2.as_ref())))
}

fn endswith(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "endswith";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.ends_with(s2.as_ref())))
}

fn format_number(n: &Number, base: u64) -> String {
    match base {
        2 => n.format_bin(),
        8 => n.format_octal(),
        10 => n.format_decimal(),
        16 => n.format_hex(),
        _ => "".to_owned(),
    }
}

fn format_int(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "format_int";
    ensure_args_count(span, name, params, args, 2)?;
    let mut n = ensure_numeric(name, &params[0], &args[0])?;
    let mut sign = "";
    if n < Number::from(0u64) {
        n = n.abs();
        sign = "-";
    }
    let n = n.floor();

    Ok(Value::String(
        (sign.to_owned()
            + &match ensure_numeric(name, &params[1], &args[1])?.as_u64() {
                Some(b) => format_number(&n, b),
                _ => return Ok(Value::Undefined),
            })
            .into(),
    ))
}

fn indexof(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "indexof";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::from(Number::from(match s1.find(s2.as_ref()) {
        Some(pos) => pos as i64,
        _ => -1,
    })))
}

#[allow(dead_code)]
fn indexof_n(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "indexof_n";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;

    let mut positions = vec![];
    let mut idx = 0;
    while idx < s1.len() {
        if let Some(pos) = s1.find(s2.as_ref()) {
            positions.push(Value::from(pos as u64));
            idx = pos + 1;
        } else {
            break;
        }
    }
    Ok(Value::from_array(positions))
}

fn lower(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "lower";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.to_lowercase().into()))
}

fn replace(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "replace";
    ensure_args_count(span, name, params, args, 3)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let old = ensure_string(name, &params[1], &args[1])?;
    let new = ensure_string(name, &params[2], &args[2])?;
    Ok(Value::String(s.replace(old.as_ref(), new.as_ref()).into()))
}

fn split(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "replace";
    ensure_args_count(span, name, params, args, 2)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let delimiter = ensure_string(name, &params[1], &args[1])?;

    Ok(Value::from_array(
        s.split(delimiter.as_ref())
            .map(|s| Value::String(s.into()))
            .collect(),
    ))
}

fn sprintf(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "sprintf";
    ensure_args_count(span, name, params, args, 2)?;
    let fmt = ensure_string(name, &params[0], &args[0])?;
    let args = ensure_array(name, &params[1], args[1].clone())?;

    let mut s = String::default();
    let mut args_idx = 0usize;
    let mut chars = fmt.chars().peekable();
    let args_span = params[1].span();
    loop {
        let verb = match chars.next() {
            Some('%') => match chars.next() {
                Some('%') => {
                    s.push('%');
                    continue;
                }
                Some(c) => c,
                None => {
                    let span = params[0].span();
                    bail!(span.error("missing format verb after `%` at end of format string"));
                }
            },
            Some(c) => {
                s.push(c);
                continue;
            }
            None => break,
        };

        if args_idx >= args.len() {
            bail!(args_span
                .error(format!("no argument specified for format verb {args_idx}").as_str()));
        }
        let arg = &args[args_idx];
        args_idx += 1;

        // Handle Golang flags.
        let mut emit_sign = false;
        let mut leave_space_for_elided_sign = false;
        match chars.peek() {
            Some('+') => {
                emit_sign = true;
                chars.next();
            }
            Some(' ') => {
                leave_space_for_elided_sign = true;
                chars.next();
            }
            _ => (),
        }

        let get_sign_value = |f: &Number| match (emit_sign, f) {
            (_, v) if v < &Number::from(0.0) => ("-", v.clone()),
            (true, v) => ("+", v.clone()),
            (false, v) if leave_space_for_elided_sign => (" ", v.clone()),
            (false, v) => ("", v.clone()),
        };

        // Handle Golang printing verbs.
        // https://pkg.go.dev/fmt
        match (verb, arg) {
            ('v', _) => s += format!("{arg}").as_str(),
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
                s += v.format_decimal().as_str()
            }
            ('o', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += ("0O".to_owned() + &v.format_octal()).as_str()
            }
            ('O', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += ("0o".to_owned() + &v.format_octal()).as_str()
            }
            ('x', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += v.format_hex().as_str()
            }
            ('X', Value::Number(f)) if f.is_integer() => {
                let (sign, v) = get_sign_value(f);
                s += sign;
                s += v.format_big_hex().as_str()
            }
            ('e', Value::Number(f)) => {
                s += match f.as_f64() {
                    Some(f) => format!("{:e}", f),
                    _ => bail!(span.error("cannot print large float using e format specifier")),
                }
                .as_str()
            }
            ('E', Value::Number(f)) => {
                s += match f.as_f64() {
                    Some(f) => format!("{:E}", f),
                    _ => bail!(span.error("cannot print large float using E format specifier")),
                }
                .as_str()
            }
            ('f' | 'F', Value::Number(f)) => s += f.format_decimal().as_str(),
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
            (_, Value::Number(_)) => {
                // TODO: binary for floating point.
                bail!(args_span.error("floating-point number specified for format verb {verb}."));
            }

            ('s', Value::String(sv)) => s += sv.as_ref(),
            ('s', _) => {
                bail!(args_span.error("invalid non string argument specified for format verb %s"));
            }

            ('+', _) if chars.next() == Some('v') => {
                bail!(args_span.error("Go-syntax fields names format verm %#v is not supported."));
            }
            ('T', _) | ('#', _) | ('q', _) | ('p', _) => {
                bail!(
                    args_span.error("Go-syntax format verbs %#v. %q, %p and %T are not supported.")
                );
            }
            _ => {}
        }
    }

    if args_idx < args.len() {
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

fn any_prefix_match(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "strings.any_prefix_match";
    ensure_args_count(span, name, params, args, 2)?;

    let search = match &args[0] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[0], &args[0])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    let base = match &args[1] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[1], &args[1])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    Ok(Value::Bool(
        search.iter().any(|s| base.iter().any(|b| s.starts_with(b))),
    ))
}

fn any_suffix_match(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "strings.any_suffix_match";
    ensure_args_count(span, name, params, args, 2)?;

    let search = match &args[0] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[0], &args[0])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    let base = match &args[1] {
        Value::String(s) => vec![s.as_ref()],
        Value::Array(_) | Value::Set(_) => ensure_string_collection(name, &params[1], &args[1])?,
        _ => {
            let span = params[0].span();
            bail!(span.error(
                format!("`{name}` expects string/array[string]/set[string] argument.").as_str()
            ));
        }
    };

    Ok(Value::Bool(
        search.iter().any(|s| base.iter().any(|b| s.ends_with(b))),
    ))
}

fn startswith(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "startswith";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::Bool(s1.starts_with(s2.as_ref())))
}

fn replace_n(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "trim";
    ensure_args_count(span, name, params, args, 2)?;
    let obj = ensure_object(name, &params[0], args[0].clone())?;
    let mut s = ensure_string(name, &params[1], &args[1])?;

    let span = params[0].span();
    for item in obj.as_ref().iter() {
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

fn reverse(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "reverse";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.chars().rev().collect::<String>().into()))
}

fn substring(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "substring";
    ensure_args_count(span, name, params, args, 3)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    let offset = ensure_numeric(name, &params[1], &args[1])?;
    let length = ensure_numeric(name, &params[2], &args[2])?;

    // TODO: distinguish between 20.0 and 20
    // Also: behavior of
    // x = substring("hello", 20 + 0.0, 25)
    match (offset.as_u64(), length.as_u64()) {
        (Some(offset), Some(length)) => {
            let offset = offset as usize;
            let length = length as usize;

            if offset > s.len() || length <= offset {
                return Ok(Value::String("".into()));
            }

            Ok(Value::String(s[offset..offset + length].into()))
        }
        _ => Ok(Value::Undefined),
    }
}

fn trim(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "trim";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(s1.trim_matches(|c| s2.contains(c)).into()))
}

fn trim_left(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "trim_left";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(
        s1.trim_start_matches(|c| s2.contains(c)).into(),
    ))
}

fn trim_prefix(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "trim_prefix";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(match s1.strip_prefix(s2.as_ref()) {
        Some(s) => s.into(),
        _ => s1,
    }))
}

fn trim_right(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "trim_right";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(
        s1.trim_end_matches(|c| s2.contains(c)).into(),
    ))
}

fn trim_space(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "trim_space";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.trim().into()))
}

fn trim_suffix(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "trim_suffix";
    ensure_args_count(span, name, params, args, 2)?;
    let s1 = ensure_string(name, &params[0], &args[0])?;
    let s2 = ensure_string(name, &params[1], &args[1])?;
    Ok(Value::String(match s1.strip_suffix(s2.as_ref()) {
        Some(s) => s.into(),
        _ => s1,
    }))
}

fn upper(span: &Span, params: &[Ref<Expr>], args: &[Value]) -> Result<Value> {
    let name = "upper";
    ensure_args_count(span, name, params, args, 1)?;
    let s = ensure_string(name, &params[0], &args[0])?;
    Ok(Value::String(s.to_uppercase().into()))
}
