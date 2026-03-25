// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template string function builtins for Azure Policy expressions.
//!
//! Implements: indexOf, lastIndexOf, trim, format.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::languages::azure_policy::strings::case_fold;
use crate::lexer::Span;
use crate::value::Value;

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use anyhow::Result;

use super::helpers::as_str;

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("azure.policy.fn.index_of", (fn_index_of, 2));
    m.insert("azure.policy.fn.last_index_of", (fn_last_index_of, 2));
    m.insert("azure.policy.fn.trim", (fn_trim, 1));
    m.insert("azure.policy.fn.format", (fn_format, 0));
}

/// `indexOf(stringToSearch, stringToFind)` → zero-based character index, or -1 if not found.
///
/// Azure documents this as case-insensitive.  Uses full Unicode case folding
/// via ICU4X (`case_fold::fold`) and returns a *character* index (not byte).
fn fn_index_of(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [hay_val, needle_val] = args
    else {
        return Ok(Value::Undefined);
    };
    let (Some(haystack), Some(needle)) = (as_str(hay_val), as_str(needle_val)) else {
        return Ok(Value::Undefined);
    };
    Ok(Value::from(case_insensitive_index_of(haystack, needle)))
}

/// `lastIndexOf(stringToSearch, stringToFind)` → zero-based character index, or -1.
///
/// Azure documents this as case-insensitive.  Uses full Unicode case folding
/// and returns a *character* index.
fn fn_last_index_of(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    #[allow(clippy::pattern_type_mismatch)]
    let [hay_val, needle_val] = args
    else {
        return Ok(Value::Undefined);
    };
    let (Some(haystack), Some(needle)) = (as_str(hay_val), as_str(needle_val)) else {
        return Ok(Value::Undefined);
    };
    Ok(Value::from(case_insensitive_last_index_of(
        haystack, needle,
    )))
}

/// Case-insensitive first-occurrence search returning a *character* index.
///
/// Case-folds both strings using ICU4X and searches in the folded domain.
/// The haystack is folded in a single pass that simultaneously builds a
/// byte-to-character-index mapping, avoiding a redundant second fold.
fn case_insensitive_index_of(haystack: &str, needle: &str) -> i64 {
    let folded_needle = case_fold::fold(needle);
    if folded_needle.is_empty() {
        return 0;
    }

    let (folded_hay, byte_to_char) = fold_with_char_map(haystack);
    if folded_needle.len() > folded_hay.len() {
        return -1;
    }

    folded_hay
        .find(&*folded_needle)
        .and_then(|byte_pos| byte_to_char.get(byte_pos).copied())
        .and_then(|ci| i64::try_from(ci).ok())
        .unwrap_or(-1)
}

/// Case-insensitive last-occurrence search returning a *character* index.
fn case_insensitive_last_index_of(haystack: &str, needle: &str) -> i64 {
    let folded_needle = case_fold::fold(needle);
    if folded_needle.is_empty() {
        return i64::try_from(haystack.chars().count()).unwrap_or(-1);
    }

    let (folded_hay, byte_to_char) = fold_with_char_map(haystack);
    if folded_needle.len() > folded_hay.len() {
        return -1;
    }

    folded_hay
        .rfind(&*folded_needle)
        .and_then(|byte_pos| byte_to_char.get(byte_pos).copied())
        .and_then(|ci| i64::try_from(ci).ok())
        .unwrap_or(-1)
}

/// Case-fold a string one character at a time, returning both the folded
/// string and a byte-to-character-index map in a single pass.
///
/// This replaces the previous approach of folding the full string, then
/// folding each character again to build the reverse map.
///
/// # Performance note
///
/// This function allocates a folded copy of the haystack and a parallel
/// `Vec<usize>` mapping every folded byte back to a source character index.
/// The allocation is inherent to Unicode case folding — you need the folded
/// string to search in it.  For the string sizes typical in Azure Policy
/// templates (field names, resource type strings) this is negligible.  If
/// profiling ever shows this as a hot path on very large inputs, a streaming
/// fold-and-match approach could replace it, but that is speculative
/// optimisation at this point.
fn fold_with_char_map(s: &str) -> (String, Vec<usize>) {
    let mut folded = String::with_capacity(s.len());
    let mut map = Vec::with_capacity(s.len());

    for (char_idx, (byte_idx, ch)) in s.char_indices().enumerate() {
        let ch_len = ch.len_utf8();
        let end = byte_idx.wrapping_add(ch_len);
        let ch_slice = s.get(byte_idx..end).unwrap_or("");
        let folded_ch = case_fold::fold(ch_slice);

        folded.push_str(&folded_ch);
        for _ in 0..folded_ch.len() {
            map.push(char_idx);
        }
    }

    (folded, map)
}

/// `trim(stringToTrim)` → string with leading/trailing whitespace removed.
fn fn_trim(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    let Some(arg) = args.first() else {
        return Ok(Value::Undefined);
    };
    let Some(s) = as_str(arg) else {
        return Ok(Value::Undefined);
    };
    Ok(Value::from(s.trim().to_string()))
}

/// `format(formatString, arg0, arg1, ...)` → formatted string.
///
/// ARM template format matches `System.String.Format` conventions:
/// - `{index[,alignment][:formatString]}` placeholders
/// - `{{` and `}}` are escaped literal braces
/// - Alignment: positive = right-padded, negative = left-padded
/// - Numeric format strings: N/n (number with thousands), D/d (decimal),
///   X/x (hex), F/f (fixed-point), etc.
fn fn_format(_span: &Span, _params: &[Ref<Expr>], args: &[Value], _strict: bool) -> Result<Value> {
    if args.is_empty() {
        return Ok(Value::Undefined);
    }
    let Some(first) = args.first() else {
        return Ok(Value::Undefined);
    };
    let Some(template) = as_str(first) else {
        return Ok(Value::Undefined);
    };

    let format_args: Vec<String> = args
        .get(1..)
        .unwrap_or_default()
        .iter()
        .map(|v| match *v {
            Value::String(ref s) => s.to_string(),
            Value::Number(ref n) => n.format_decimal(),
            Value::Bool(true) => "True".into(),
            Value::Bool(false) => "False".into(),
            Value::Null => String::new(),
            _ => v.to_string(),
        })
        .collect();

    let format_args_values = args.get(1..).unwrap_or_default();

    let mut result = String::new();
    let chars: Vec<char> = template.chars().collect();
    let len = chars.len();
    let mut i = 0;

    while i < len {
        let ch = chars.get(i).copied().unwrap_or('\0');
        match ch {
            '{' => {
                // Check for escaped brace {{
                if chars.get(i.wrapping_add(1)).copied() == Some('{') {
                    result.push('{');
                    i = i.wrapping_add(2);
                    continue;
                }
                // Parse placeholder: {index[,alignment][:formatString]}
                i = i.wrapping_add(1); // skip '{'
                let mut index_str = String::new();
                while i < len && chars.get(i).copied().unwrap_or('\0').is_ascii_digit() {
                    index_str.push(chars.get(i).copied().unwrap_or('\0'));
                    i = i.wrapping_add(1);
                }
                if index_str.is_empty() {
                    anyhow::bail!(
                        "format: invalid placeholder at position {}; expected '{{index}}'",
                        i.wrapping_sub(1)
                    );
                }
                let idx: usize = index_str.parse().map_err(|_| {
                    anyhow::anyhow!(
                        "format: invalid placeholder index '{}' at position {}; expected a non-negative integer within range",
                        index_str,
                        i.wrapping_sub(index_str.len()).wrapping_sub(1)
                    )
                })?;

                // Optional alignment
                let alignment: i32 = if chars.get(i).copied() == Some(',') {
                    i = i.wrapping_add(1); // skip ','
                    let mut align_str = String::new();
                    while i < len {
                        let c = chars.get(i).copied().unwrap_or('\0');
                        if c == ':' || c == '}' {
                            break;
                        }
                        align_str.push(c);
                        i = i.wrapping_add(1);
                    }
                    let trimmed = align_str.trim();
                    if trimmed.is_empty() {
                        anyhow::bail!(
                            "format: empty alignment value in placeholder at position {}",
                            i.wrapping_sub(align_str.len()).wrapping_sub(1)
                        );
                    }
                    trimmed.parse().map_err(|_| {
                        anyhow::anyhow!(
                            "format: invalid alignment '{}' in placeholder; expected an integer",
                            trimmed
                        )
                    })?
                } else {
                    0
                };

                // Optional format specifier
                let mut fmt_spec = String::new();
                if chars.get(i).copied() == Some(':') {
                    i = i.wrapping_add(1); // skip ':'
                    while i < len && chars.get(i).copied().unwrap_or('\0') != '}' {
                        fmt_spec.push(chars.get(i).copied().unwrap_or('\0'));
                        i = i.wrapping_add(1);
                    }
                }

                // Require closing '}'
                if chars.get(i).copied() == Some('}') {
                    i = i.wrapping_add(1);
                } else {
                    anyhow::bail!(
                        "format: unmatched opening brace '{{{{' at position {}; \
                         expected closing '}}}}'.",
                        i.wrapping_sub(index_str.len()).wrapping_sub(1)
                    );
                }

                // Format the argument — error if the index is out of range,
                // matching System.String.Format semantics.
                let Some(raw) = format_args.get(idx).cloned() else {
                    anyhow::bail!(
                        "format: placeholder {{{idx}}} references argument index {idx}, \
                         but only {} argument(s) were supplied",
                        format_args.len()
                    );
                };
                let formatted = if fmt_spec.is_empty() {
                    raw
                } else {
                    apply_format_spec(&raw, &fmt_spec, format_args_values.get(idx))?
                };

                // Apply alignment
                apply_alignment(&mut result, &formatted, alignment)?;
            }
            '}' => {
                // Escaped }} → literal '}'
                if chars.get(i.wrapping_add(1)).copied() == Some('}') {
                    result.push('}');
                    i = i.wrapping_add(2);
                } else {
                    anyhow::bail!("format: unmatched closing brace '}}' at position {i}");
                }
            }
            _ => {
                result.push(ch);
                i = i.wrapping_add(1);
            }
        }
    }

    Ok(Value::from(result))
}

/// Apply a .NET-style format specifier to a value string.
fn apply_format_spec(raw: &str, spec: &str, value: Option<&Value>) -> Result<String> {
    let spec_char = spec.chars().next().unwrap_or('G');
    let precision: Option<usize> = spec.get(1..).and_then(|s| s.parse().ok());

    // Try to get numeric value for numeric formatting
    let int_val = value.and_then(|v| match *v {
        Value::Number(ref n) => n.as_i64(),
        _ => None,
    });
    let float_val = value.and_then(|v| match *v {
        Value::Number(ref n) => n.as_f64(),
        _ => None,
    });

    Ok(match spec_char {
        // Fixed-point
        'F' | 'f' => {
            let prec = precision.unwrap_or(2);
            float_val.map_or_else(|| raw.to_string(), |f| alloc::format!("{f:.prec$}"))
        }
        // Number with thousands separator
        'N' | 'n' => {
            let prec = precision.unwrap_or(2);
            float_val.map_or_else(|| raw.to_string(), |f| format_with_thousands(f, prec))
        }
        // Decimal (integer)
        'D' | 'd' => {
            let width = precision.unwrap_or(0);
            int_val.map_or_else(
                || raw.to_string(),
                |n| {
                    if n < 0 {
                        alloc::format!("-{:0>width$}", n.unsigned_abs())
                    } else {
                        alloc::format!("{n:0>width$}")
                    }
                },
            )
        }
        // Hexadecimal
        'X' => {
            let width = precision.unwrap_or(0);
            int_val.map_or_else(
                || raw.to_string(),
                |n| alloc::format!("{:0>width$}", alloc::format!("{n:X}")),
            )
        }
        'x' => {
            let width = precision.unwrap_or(0);
            int_val.map_or_else(
                || raw.to_string(),
                |n| alloc::format!("{:0>width$}", alloc::format!("{n:x}")),
            )
        }
        // Percent
        'P' | 'p' => {
            let prec = precision.unwrap_or(2);
            float_val.map_or_else(
                || raw.to_string(),
                |f| {
                    let pct = f * 100.0;
                    alloc::format!("{pct:.prec$} %")
                },
            )
        }
        // Unknown specifier: error for numeric values (.NET throws FormatException),
        // pass through for non-numeric.
        _ => {
            if int_val.is_some() || float_val.is_some() {
                anyhow::bail!("format: invalid numeric format specifier '{spec_char}'");
            }
            raw.to_string()
        }
    })
}

/// Format a number with thousands separators and fixed decimal places.
fn format_with_thousands(value: f64, precision: usize) -> String {
    let formatted = alloc::format!("{value:.precision$}");
    let (int_part, dec_part) = formatted.split_once('.').unwrap_or((&formatted, ""));

    let negative = int_part.starts_with('-');
    let digits = if negative {
        int_part.get(1..).unwrap_or("")
    } else {
        int_part
    };

    let mut with_commas = String::new();
    for (i, ch) in digits.chars().rev().enumerate() {
        if i > 0 && i % 3 == 0 {
            with_commas.push(',');
        }
        with_commas.push(ch);
    }
    let with_commas: String = with_commas.chars().rev().collect();

    let mut result = String::new();
    if negative {
        result.push('-');
    }
    result.push_str(&with_commas);
    if precision > 0 {
        result.push('.');
        result.push_str(dec_part);
    }
    result
}

/// Maximum alignment width to prevent excessive memory allocation from
/// user-controlled format strings (e.g. `{0,1000000000}`).
const MAX_ALIGNMENT_WIDTH: usize = 10_000;

/// Apply alignment (padding) to a formatted value.
fn apply_alignment(result: &mut String, formatted: &str, alignment: i32) -> Result<()> {
    if alignment == 0 {
        result.push_str(formatted);
    } else {
        let width = usize::try_from(alignment.unsigned_abs()).unwrap_or(usize::MAX);
        if width > MAX_ALIGNMENT_WIDTH {
            anyhow::bail!(
                "format: alignment width {width} exceeds maximum allowed ({MAX_ALIGNMENT_WIDTH})"
            );
        }
        let char_len = formatted.chars().count();
        if char_len >= width {
            result.push_str(formatted);
        } else {
            let padding = width.saturating_sub(char_len);
            if alignment > 0 {
                // Right-align: pad on left
                for _ in 0..padding {
                    result.push(' ');
                }
                result.push_str(formatted);
            } else {
                // Left-align: pad on right
                result.push_str(formatted);
                for _ in 0..padding {
                    result.push(' ');
                }
            }
        }
    }
    Ok(())
}
