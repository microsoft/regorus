// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! ARM template date/time builtins: dateTimeAdd, dateTimeFromEpoch,
//! dateTimeToEpoch, addDays.
//!
//! `utcNow()` is handled in the compiler (loaded from context), not here.

use crate::ast::{Expr, Ref};
use crate::builtins;
use crate::lexer::Span;
use crate::value::Value;

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use anyhow::Result;

use core::fmt::Write as _;

use chrono::{DateTime, Duration, FixedOffset, Utc};

use super::helpers::as_str;

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("azure.policy.fn.date_time_add", (fn_date_time_add, 0));
    m.insert(
        "azure.policy.fn.date_time_from_epoch",
        (fn_date_time_from_epoch, 1),
    );
    m.insert(
        "azure.policy.fn.date_time_to_epoch",
        (fn_date_time_to_epoch, 1),
    );
    m.insert("azure.policy.fn.add_days", (fn_add_days, 0));
}

// ── ISO 8601 datetime parsing ─────────────────────────────────────────

/// Parse an ISO 8601 / RFC 3339 datetime string.
fn parse_datetime(s: &str) -> Option<DateTime<FixedOffset>> {
    parse_datetime_styled(s).map(|(dt, _)| dt)
}

/// The detected format style of a parsed datetime string, used to reproduce
/// the same shape when no explicit output format is given.
#[derive(Clone, Copy)]
enum DateTimeStyle {
    /// RFC 3339 with T separator and Z suffix.
    Rfc3339Z,
    /// RFC 3339 with T separator and explicit numeric offset.
    Rfc3339Offset,
    /// T separator, no timezone (assumed UTC).
    IsoNoTz,
    /// Space separator, no timezone (assumed UTC).
    SpaceNoTz,
    /// Space separator with Z suffix.
    SpaceZ,
    /// Space separator with explicit offset.
    SpaceOffset,
}

/// Parse a datetime string and return both the parsed value and the detected
/// input style so that output formatting can preserve it.
fn parse_datetime_styled(s: &str) -> Option<(DateTime<FixedOffset>, DateTimeStyle)> {
    // Check for space separator at position 10 (after "YYYY-MM-DD") so that
    // space-separated inputs are detected before RFC 3339 (which also allows
    // a space in place of T).
    if s.len() > 10 && s.as_bytes().get(10).copied() == Some(b' ') {
        // Space separator with explicit offset (e.g. "2020-04-07 14:55:59+00:00").
        if let Ok(dt) = DateTime::parse_from_str(s, "%Y-%m-%d %H:%M:%S%:z") {
            return Some((dt, DateTimeStyle::SpaceOffset));
        }
        if let Ok(dt) = DateTime::parse_from_str(s, "%Y-%m-%d %H:%M:%S%.f%:z") {
            return Some((dt, DateTimeStyle::SpaceOffset));
        }
        // Space separator with Z suffix (e.g. "2020-04-07 14:55:59Z").
        if let Some(stripped) = s.strip_suffix('Z').or_else(|| s.strip_suffix('z')) {
            if let Ok(naive) = chrono::NaiveDateTime::parse_from_str(stripped, "%Y-%m-%d %H:%M:%S")
            {
                let utc = DateTime::<Utc>::from_naive_utc_and_offset(naive, Utc);
                return Some((utc.fixed_offset(), DateTimeStyle::SpaceZ));
            }
            if let Ok(naive) =
                chrono::NaiveDateTime::parse_from_str(stripped, "%Y-%m-%d %H:%M:%S%.f")
            {
                let utc = DateTime::<Utc>::from_naive_utc_and_offset(naive, Utc);
                return Some((utc.fixed_offset(), DateTimeStyle::SpaceZ));
            }
        }
        // Space separator, no timezone (assume UTC).
        if let Ok(naive) = chrono::NaiveDateTime::parse_from_str(s, "%Y-%m-%d %H:%M:%S") {
            let utc = DateTime::<Utc>::from_naive_utc_and_offset(naive, Utc);
            return Some((utc.fixed_offset(), DateTimeStyle::SpaceNoTz));
        }
        if let Ok(naive) = chrono::NaiveDateTime::parse_from_str(s, "%Y-%m-%d %H:%M:%S%.f") {
            let utc = DateTime::<Utc>::from_naive_utc_and_offset(naive, Utc);
            return Some((utc.fixed_offset(), DateTimeStyle::SpaceNoTz));
        }
    }

    // Try RFC 3339 first (most common for ARM templates).
    if let Ok(dt) = DateTime::parse_from_rfc3339(s) {
        let style = if s.ends_with('Z') || s.ends_with('z') {
            DateTimeStyle::Rfc3339Z
        } else {
            DateTimeStyle::Rfc3339Offset
        };
        return Some((dt, style));
    }
    // Try with T separator, no timezone (assume UTC).
    if let Ok(naive) = chrono::NaiveDateTime::parse_from_str(s, "%Y-%m-%dT%H:%M:%S") {
        let utc = DateTime::<Utc>::from_naive_utc_and_offset(naive, Utc);
        return Some((utc.fixed_offset(), DateTimeStyle::IsoNoTz));
    }
    if let Ok(naive) = chrono::NaiveDateTime::parse_from_str(s, "%Y-%m-%dT%H:%M:%S%.f") {
        let utc = DateTime::<Utc>::from_naive_utc_and_offset(naive, Utc);
        return Some((utc.fixed_offset(), DateTimeStyle::IsoNoTz));
    }
    None
}

/// Format a datetime as ISO 8601 string.  UTC datetimes use the `Z` suffix
/// (matching Azure's documented output), while offset datetimes keep their
/// explicit offset.  Fractional seconds are included when non-zero.
fn format_datetime(dt: &DateTime<FixedOffset>) -> String {
    if dt.offset().local_minus_utc() == 0 {
        // UTC → use Z suffix
        dt.format("%Y-%m-%dT%H:%M:%S%.fZ").to_string()
    } else {
        dt.format("%Y-%m-%dT%H:%M:%S%.f%:z").to_string()
    }
}

/// Format a datetime preserving the detected input style.
fn format_datetime_styled(dt: &DateTime<FixedOffset>, style: DateTimeStyle) -> String {
    match style {
        DateTimeStyle::Rfc3339Z => dt.format("%Y-%m-%dT%H:%M:%S%.fZ").to_string(),
        DateTimeStyle::Rfc3339Offset => dt.format("%Y-%m-%dT%H:%M:%S%.f%:z").to_string(),
        DateTimeStyle::IsoNoTz => dt.format("%Y-%m-%dT%H:%M:%S%.f").to_string(),
        DateTimeStyle::SpaceNoTz => dt.format("%Y-%m-%d %H:%M:%S%.f").to_string(),
        DateTimeStyle::SpaceZ => dt.format("%Y-%m-%d %H:%M:%S%.fZ").to_string(),
        DateTimeStyle::SpaceOffset => dt.format("%Y-%m-%d %H:%M:%S%.f%:z").to_string(),
    }
}

// ── ISO 8601 duration parsing ─────────────────────────────────────────

/// Parse an ISO 8601 duration string into a `chrono::Duration`.
///
/// Supports: `P[nY][nM][nD][T[nH][nM][nS]]`
/// Examples: `P1D`, `PT1H`, `P1Y2M3DT4H5M6S`, `PT30M`, `-P1D`
///
/// Note: months/years are approximated (1 month = 30 days, 1 year = 365 days)
/// since chrono::Duration is absolute. ARM template behavior matches this.
fn parse_iso8601_duration(s: &str) -> Option<Duration> {
    let (s, negative) = s.strip_prefix('-').map_or((s, false), |rest| (rest, true));

    let s = s.strip_prefix('P')?;
    let mut total_seconds: i64 = 0;
    let mut in_time = false;
    let mut num_buf = String::new();

    for ch in s.chars() {
        match ch {
            'T' => {
                in_time = true;
            }
            '0'..='9' | '.' => {
                num_buf.push(ch);
            }
            'Y' if !in_time => {
                let n: f64 = num_buf.parse().ok()?;
                total_seconds = total_seconds.checked_add(f64_as_i64(n * 365.0 * 86400.0))?;
                num_buf.clear();
            }
            'M' if !in_time => {
                // Months in date part
                let n: f64 = num_buf.parse().ok()?;
                total_seconds = total_seconds.checked_add(f64_as_i64(n * 30.0 * 86400.0))?;
                num_buf.clear();
            }
            'W' if !in_time => {
                let n: f64 = num_buf.parse().ok()?;
                total_seconds = total_seconds.checked_add(f64_as_i64(n * 7.0 * 86400.0))?;
                num_buf.clear();
            }
            'D' if !in_time => {
                let n: f64 = num_buf.parse().ok()?;
                total_seconds = total_seconds.checked_add(f64_as_i64(n * 86400.0))?;
                num_buf.clear();
            }
            'H' if in_time => {
                let n: f64 = num_buf.parse().ok()?;
                total_seconds = total_seconds.checked_add(f64_as_i64(n * 3600.0))?;
                num_buf.clear();
            }
            'M' if in_time => {
                // Minutes in time part
                let n: f64 = num_buf.parse().ok()?;
                total_seconds = total_seconds.checked_add(f64_as_i64(n * 60.0))?;
                num_buf.clear();
            }
            'S' if in_time => {
                let n: f64 = num_buf.parse().ok()?;
                total_seconds = total_seconds.checked_add(f64_as_i64(n))?;
                num_buf.clear();
            }
            _ => return None,
        }
    }

    let dur = Duration::seconds(if negative {
        total_seconds.checked_neg()?
    } else {
        total_seconds
    });
    Some(dur)
}

// ── Builtin functions ─────────────────────────────────────────────────

/// `dateTimeAdd(base, duration, format?)` → add ISO 8601 duration to datetime.
///
/// ARM template: `dateTimeAdd('2020-04-07 14:55:59', 'P3Y2M', 'yyyy-MM-dd')`
/// The optional third argument is a .NET-style custom date/time format string.
/// When absent, the output uses the same format as the input base string.
fn fn_date_time_add(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(base_str) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    let Some(duration_str) = args.get(1).and_then(as_str) else {
        return Ok(Value::Undefined);
    };

    let Some((base_dt, style)) = parse_datetime_styled(base_str) else {
        return Ok(Value::Undefined);
    };
    let Some(duration) = parse_iso8601_duration(duration_str) else {
        return Ok(Value::Undefined);
    };

    let result = base_dt
        .checked_add_signed(duration)
        .ok_or_else(|| anyhow::anyhow!("dateTimeAdd: datetime overflow"))?;

    let output = match args.get(2).and_then(as_str) {
        Some(fmt) => format_datetime_dotnet(&result, fmt)?,
        None => format_datetime_styled(&result, style),
    };
    Ok(Value::from(output))
}

/// `dateTimeFromEpoch(epoch)` → ISO 8601 UTC datetime string from Unix epoch.
fn fn_date_time_from_epoch(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(epoch) = args.first().and_then(extract_i64) else {
        return Ok(Value::Undefined);
    };
    let Some(dt) = DateTime::from_timestamp(epoch, 0) else {
        return Ok(Value::Undefined);
    };
    // Always UTC, so use Z suffix.
    Ok(Value::from(dt.format("%Y-%m-%dT%H:%M:%SZ").to_string()))
}

/// `dateTimeToEpoch(dateTime)` → Unix epoch seconds from ISO 8601 string.
fn fn_date_time_to_epoch(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(s) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    let Some(dt) = parse_datetime(s) else {
        return Ok(Value::Undefined);
    };
    Ok(Value::from(dt.timestamp()))
}

/// `addDays(dateTime, numberOfDays)` → ISO 8601 datetime with days added.
///
/// Very common in real Azure Policy definitions (e.g., key expiry checks).
fn fn_add_days(
    _span: &Span,
    _params: &[Ref<Expr>],
    args: &[Value],
    _strict: bool,
) -> Result<Value> {
    let Some(base_str) = args.first().and_then(as_str) else {
        return Ok(Value::Undefined);
    };
    let Some(days) = args.get(1).and_then(extract_i64) else {
        return Ok(Value::Undefined);
    };

    let Some(base_dt) = parse_datetime(base_str) else {
        return Ok(Value::Undefined);
    };
    let duration = Duration::days(days);
    let result = base_dt
        .checked_add_signed(duration)
        .ok_or_else(|| anyhow::anyhow!("addDays: datetime overflow"))?;
    Ok(Value::from(format_datetime(&result)))
}

// ── Helpers ───────────────────────────────────────────────────────────

fn extract_i64(v: &Value) -> Option<i64> {
    match *v {
        Value::Number(ref n) => n.as_i64(),
        _ => None,
    }
}

/// Deliberate truncating conversion from `f64` → `i64`.
#[expect(clippy::as_conversions)]
const fn f64_as_i64(x: f64) -> i64 {
    x as i64
}

/// Segments produced by parsing a .NET custom datetime format string.
enum FmtSegment {
    /// A chrono format string.
    Chrono(String),
    /// Fractional seconds, truncated to `n` digits (1..=7).
    Frac(usize),
    /// First character of AM/PM (the .NET `t` specifier).
    AmPmShort,
    /// Timezone offset hours, no leading zero (the .NET `z` specifier).
    TzHoursNoPad,
    /// Timezone offset hours, with leading zero (the .NET `zz` specifier).
    TzHoursPad,
}

/// Result of trying to interpret a format string as a .NET standard specifier.
enum StandardFormat {
    /// Expanded custom format string.
    Expansion(String),
    /// A standard specifier that requires UTC conversion before formatting.
    UtcNormalized(String),
    /// Not a single-letter standard specifier (treat as custom format).
    NotStandard,
}

/// Format a datetime using a .NET-style date/time format string.
///
/// Handles both standard format strings (single character like `d`, `G`, `o`)
/// and custom format strings (multi-token patterns like `yyyy-MM-dd`).
///
/// # Compatibility note
///
/// This is an *approximation* of `System.DateTime.ToString()` targeting the
/// invariant culture only, which is what Azure Policy uses in practice.  The
/// segment-based architecture (`FmtSegment` + `dotnet_to_segments`) covers
/// the specifiers exercised by real-world policy definitions, but
/// culture-sensitive corners (localised day/month names, era designators,
/// calendar systems, etc.) are deliberately omitted.  Pulling in a full
/// ICU/globalisation stack would be disproportionate for this use case.
/// If a specific .NET format corner is needed later, it can be added
/// incrementally by extending the segment parser.
fn format_datetime_dotnet(dt: &DateTime<FixedOffset>, dotnet_fmt: &str) -> Result<String> {
    // Check for standard format specifiers and determine the effective
    // custom format and the datetime to format against.
    let (effective_fmt_owned, format_dt);
    let effective_fmt = match resolve_standard_format(dotnet_fmt)? {
        StandardFormat::Expansion(s) => {
            effective_fmt_owned = s;
            &effective_fmt_owned
        }
        StandardFormat::UtcNormalized(s) => {
            // Convert to UTC before formatting (e.g. the 'u' specifier).
            format_dt = dt.with_timezone(&Utc).fixed_offset();
            effective_fmt_owned = s;
            let is_utc = true;
            let segments = dotnet_to_segments(&effective_fmt_owned, is_utc);
            return Ok(render_segments(&format_dt, &segments));
        }
        StandardFormat::NotStandard => dotnet_fmt,
    };
    let is_utc = dt.offset().local_minus_utc() == 0;
    let segments = dotnet_to_segments(effective_fmt, is_utc);
    Ok(render_segments(dt, &segments))
}

/// Render pre-parsed format segments against a datetime value.
fn render_segments(dt: &DateTime<FixedOffset>, segments: &[FmtSegment]) -> String {
    let mut out = String::new();
    for seg in segments {
        match *seg {
            FmtSegment::Chrono(ref fmt) => {
                out.push_str(&dt.format(fmt).to_string());
            }
            FmtSegment::Frac(n) => {
                // %f gives 9-digit nanoseconds; take the first n digits.
                let nanos = dt.format("%f").to_string();
                let truncated: String = nanos.chars().take(n).collect();
                out.push_str(&truncated);
            }
            FmtSegment::AmPmShort => {
                let full = dt.format("%p").to_string();
                if let Some(c) = full.chars().next() {
                    out.push(c);
                }
            }
            FmtSegment::TzHoursNoPad => {
                let hours = dt.offset().local_minus_utc() / 3600;
                if hours >= 0 {
                    out.push('+');
                }
                let _ = write!(out, "{hours}");
            }
            FmtSegment::TzHoursPad => {
                let secs = dt.offset().local_minus_utc();
                let hours = secs / 3600;
                if secs >= 0 {
                    let _ = write!(out, "+{hours:02}");
                } else {
                    let _ = write!(out, "-{:02}", hours.wrapping_neg());
                }
            }
        }
    }
    out
}

/// Resolve a .NET standard date/time format specifier.
///
/// Returns the appropriate `StandardFormat` variant:
/// - `Expansion` for standard specifiers that can be expanded to custom tokens.
/// - `UtcNormalized` for specifiers that require UTC conversion first.
/// - `NotStandard` when the string is a multi-character custom format.
///
/// Single-letter strings that are *not* a recognised standard specifier are
/// also mapped to their equivalent custom token (via the .NET `%`-prefix
/// rule), so that e.g. `"U"` does not silently produce a literal `U`.
///
/// Reference: <https://learn.microsoft.com/dotnet/standard/base-types/standard-date-and-time-format-strings>
fn resolve_standard_format(fmt: &str) -> Result<StandardFormat> {
    if fmt.len() != 1 {
        return Ok(StandardFormat::NotStandard);
    }
    Ok(match fmt {
        // Short date  (invariant culture: MM/dd/yyyy)
        "d" => StandardFormat::Expansion("MM/dd/yyyy".into()),
        // Long date   (invariant: dddd, dd MMMM yyyy)
        "D" => StandardFormat::Expansion("dddd, dd MMMM yyyy".into()),
        // Short time  (invariant: HH:mm)
        "t" => StandardFormat::Expansion("HH:mm".into()),
        // Long time   (invariant: HH:mm:ss)
        "T" => StandardFormat::Expansion("HH:mm:ss".into()),
        // General short time  (short date + short time)
        "g" => StandardFormat::Expansion("MM/dd/yyyy HH:mm".into()),
        // General long time   (short date + long time)
        "G" => StandardFormat::Expansion("MM/dd/yyyy HH:mm:ss".into()),
        // Month/day   (invariant: MMMM dd)
        "M" | "m" => StandardFormat::Expansion("MMMM dd".into()),
        // Round-trip / ISO 8601  (o / O are identical)
        "o" | "O" => StandardFormat::Expansion("yyyy'-'MM'-'dd'T'HH':'mm':'ss'.'fffffffK".into()),
        // RFC1123  (invariant: ddd, dd MMM yyyy HH:mm:ss 'GMT') — requires UTC conversion
        "R" | "r" => StandardFormat::UtcNormalized("ddd, dd MMM yyyy HH':'mm':'ss 'GMT'".into()),
        // Sortable   (ISO 8601 without offset)
        "s" => StandardFormat::Expansion("yyyy'-'MM'-'dd'T'HH':'mm':'ss".into()),
        // Universal sortable  (UTC, trailing Z) — requires UTC conversion
        "u" => StandardFormat::UtcNormalized("yyyy'-'MM'-'dd HH':'mm':'ss'Z'".into()),
        // Full date/time (UTC) — requires UTC conversion
        "U" => StandardFormat::UtcNormalized("dddd, dd MMMM yyyy HH:mm:ss".into()),
        // Year/month  (invariant: yyyy MMMM)
        "Y" | "y" => StandardFormat::Expansion("yyyy MMMM".into()),
        // Full date/short time
        "f" => StandardFormat::Expansion("dddd, dd MMMM yyyy HH:mm".into()),
        // Full date/long time
        "F" => StandardFormat::Expansion("dddd, dd MMMM yyyy HH:mm:ss".into()),
        // Not a standard specifier → error.  In .NET, passing an
        // unrecognised single-letter string to DateTime.ToString() throws
        // FormatException rather than silently echoing the character.
        _ => anyhow::bail!(
            "dateTimeAdd: unrecognised standard format specifier '{}'",
            fmt
        ),
    })
}

/// Parse a .NET custom datetime format string into segments.
///
/// Consecutive chrono-compatible tokens are batched into a single `Chrono`
/// segment; tokens that need custom logic produce their own segment.
fn dotnet_to_segments(fmt: &str, is_utc: bool) -> Vec<FmtSegment> {
    let mut segments: Vec<FmtSegment> = Vec::new();
    let mut chrono_buf = String::new();
    let chars: Vec<char> = fmt.chars().collect();
    let len = chars.len();
    let mut i: usize = 0;

    macro_rules! flush {
        () => {
            if !chrono_buf.is_empty() {
                segments.push(FmtSegment::Chrono(core::mem::take(&mut chrono_buf)));
            }
        };
    }

    while i < len {
        let ch = chars.get(i).copied().unwrap_or('\0');
        let remaining = len.saturating_sub(i);

        match ch {
            // Escaped literal
            '\\' if remaining > 1 => {
                i = i.wrapping_add(1);
                let next = chars.get(i).copied().unwrap_or('\0');
                chrono_buf.push(next);
                i = i.wrapping_add(1);
            }
            // Quoted literal
            '\'' => {
                i = i.wrapping_add(1);
                while i < len {
                    let c = chars.get(i).copied().unwrap_or('\0');
                    if c == '\'' {
                        i = i.wrapping_add(1);
                        break;
                    }
                    chrono_buf.push(c);
                    i = i.wrapping_add(1);
                }
            }
            // Year
            'y' if remaining >= 4 && matches_run(&chars, i, 'y', 4) => {
                chrono_buf.push_str("%Y");
                i = i.wrapping_add(4);
            }
            'y' if remaining >= 2 && matches_run(&chars, i, 'y', 2) => {
                chrono_buf.push_str("%y");
                i = i.wrapping_add(2);
            }
            // Month
            'M' if remaining >= 4 && matches_run(&chars, i, 'M', 4) => {
                chrono_buf.push_str("%B");
                i = i.wrapping_add(4);
            }
            'M' if remaining >= 3 && matches_run(&chars, i, 'M', 3) => {
                chrono_buf.push_str("%b");
                i = i.wrapping_add(3);
            }
            'M' if remaining >= 2 && matches_run(&chars, i, 'M', 2) => {
                chrono_buf.push_str("%m");
                i = i.wrapping_add(2);
            }
            'M' => {
                chrono_buf.push_str("%-m");
                i = i.wrapping_add(1);
            }
            // Day
            'd' if remaining >= 4 && matches_run(&chars, i, 'd', 4) => {
                chrono_buf.push_str("%A");
                i = i.wrapping_add(4);
            }
            'd' if remaining >= 3 && matches_run(&chars, i, 'd', 3) => {
                chrono_buf.push_str("%a");
                i = i.wrapping_add(3);
            }
            'd' if remaining >= 2 && matches_run(&chars, i, 'd', 2) => {
                chrono_buf.push_str("%d");
                i = i.wrapping_add(2);
            }
            'd' => {
                chrono_buf.push_str("%-d");
                i = i.wrapping_add(1);
            }
            // 24-hour
            'H' if remaining >= 2 && matches_run(&chars, i, 'H', 2) => {
                chrono_buf.push_str("%H");
                i = i.wrapping_add(2);
            }
            'H' => {
                chrono_buf.push_str("%-H");
                i = i.wrapping_add(1);
            }
            // 12-hour
            'h' if remaining >= 2 && matches_run(&chars, i, 'h', 2) => {
                chrono_buf.push_str("%I");
                i = i.wrapping_add(2);
            }
            'h' => {
                chrono_buf.push_str("%-I");
                i = i.wrapping_add(1);
            }
            // Minute
            'm' if remaining >= 2 && matches_run(&chars, i, 'm', 2) => {
                chrono_buf.push_str("%M");
                i = i.wrapping_add(2);
            }
            'm' => {
                chrono_buf.push_str("%-M");
                i = i.wrapping_add(1);
            }
            // Second
            's' if remaining >= 2 && matches_run(&chars, i, 's', 2) => {
                chrono_buf.push_str("%S");
                i = i.wrapping_add(2);
            }
            's' => {
                chrono_buf.push_str("%-S");
                i = i.wrapping_add(1);
            }
            // Fractions of second — consume the full run of 'f' chars
            'f' => {
                let mut count: usize = 0;
                while i < len && chars.get(i).copied() == Some('f') {
                    count = count.wrapping_add(1);
                    i = i.wrapping_add(1);
                }
                flush!();
                // Clamp to 9 (nanosecond precision from chrono).
                segments.push(FmtSegment::Frac(count.min(9)));
            }
            // AM/PM
            't' if remaining >= 2 && matches_run(&chars, i, 't', 2) => {
                chrono_buf.push_str("%p");
                i = i.wrapping_add(2);
            }
            't' => {
                flush!();
                segments.push(FmtSegment::AmPmShort);
                i = i.wrapping_add(1);
            }
            // Timezone: K in .NET → offset or Z
            'K' => {
                if is_utc {
                    chrono_buf.push('Z');
                } else {
                    chrono_buf.push_str("%:z");
                }
                i = i.wrapping_add(1);
            }
            // Timezone offset zzz → full offset +00:00
            'z' if remaining >= 3 && matches_run(&chars, i, 'z', 3) => {
                chrono_buf.push_str("%:z");
                i = i.wrapping_add(3);
            }
            // zz → offset hours with leading zero
            'z' if remaining >= 2 && matches_run(&chars, i, 'z', 2) => {
                flush!();
                segments.push(FmtSegment::TzHoursPad);
                i = i.wrapping_add(2);
            }
            // z → offset hours without leading zero
            'z' => {
                flush!();
                segments.push(FmtSegment::TzHoursNoPad);
                i = i.wrapping_add(1);
            }
            // Literal characters (including T, :, -, etc.)
            _ => {
                chrono_buf.push(ch);
                i = i.wrapping_add(1);
            }
        }
    }

    flush!();
    segments
}

/// Check whether the slice starting at `start` contains at least `count`
/// consecutive occurrences of `ch`.
fn matches_run(chars: &[char], start: usize, ch: char, count: usize) -> bool {
    (0..count).all(|offset| chars.get(start.wrapping_add(offset)).copied() == Some(ch))
}
