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

use alloc::string::String;
use alloc::vec::Vec;
use anyhow::Result;

use core::fmt::Write as _;

use jiff::{fmt::strtime, tz::TimeZone, SignedDuration, Timestamp, ZonedDateTime};

use super::helpers::as_str;
use crate::builtins::datetime::{format_rfc3339, parse_rfc3339};

pub(super) fn register(m: &mut builtins::BuiltinsMap<&'static str, builtins::BuiltinFcn>) {
    m.insert("azure.policy.fn.date_time_add", (fn_date_time_add, 3));
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
///
/// Accepts multiple formats common in Azure Policy and ARM templates:
/// - RFC 3339 with `T` separator (`2024-01-15T12:00:00Z`, `...+05:30`)
/// - ISO 8601 without timezone (assumed UTC)
/// - Space-separated variants (`2024-01-15 12:00:00Z`)
fn parse_datetime(s: &str) -> Option<ZonedDateTime> {
    if let Ok(dt) = parse_rfc3339(s) {
        return Some(dt);
    }
    let separator = if s.as_bytes().get(10) == Some(&b' ') {
        " "
    } else {
        "T"
    };
    let datetime =
        strtime::BrokenDownTime::parse(alloc::format!("%Y-%m-%d{separator}%H:%M:%S%.f"), s)
            .ok()?
            .to_datetime()
            .ok()?
            .to_zoned_datetime(TimeZone::UTC)
            .ok()?;
    if s.get(17..19) == Some("60") {
        datetime.checked_add(SignedDuration::from_secs(1)).ok()
    } else {
        Some(datetime)
    }
}

/// Format a datetime as ISO 8601 string.  UTC datetimes use the `Z` suffix
/// (matching Azure's documented output), while offset datetimes keep their
/// explicit offset.  Fractional seconds are included when non-zero.
fn format_datetime(dt: &ZonedDateTime) -> Result<String> {
    format_rfc3339(dt, true)
}

// ── ISO 8601 duration parsing ─────────────────────────────────────────

/// Parse an ISO 8601 duration string into an absolute duration.
///
/// Supports: `P[nY][nM][nD][T[nH][nM][nS]]`
/// Examples: `P1D`, `PT1H`, `P1Y2M3DT4H5M6S`, `PT30M`, `-P1D`
///
/// Note: months/years are approximated (1 month = 30 days, 1 year = 365 days)
/// ARM template behavior matches this.
fn parse_iso8601_duration(s: &str) -> Option<SignedDuration> {
    let (s, negative) = s.strip_prefix('-').map_or((s, false), |rest| (rest, true));

    let s = s.strip_prefix('P')?;
    let mut total_seconds: i64 = 0;
    let mut in_time = false;
    let mut num_buf = String::new();

    for ch in s.chars() {
        match ch {
            'T' => {
                if !num_buf.is_empty() {
                    return None;
                }
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

    if !num_buf.is_empty() {
        return None;
    }

    let dur = SignedDuration::from_secs(if negative {
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
/// When absent, the output is normalized to ISO 8601 with T separator and
/// timezone; UTC/zero-offset values are emitted with a `Z` suffix (e.g.
/// `2023-06-07T14:55:59Z`).
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

    let Some(base_dt) = parse_datetime(base_str) else {
        return Ok(Value::Undefined);
    };
    let Some(duration) = parse_iso8601_duration(duration_str) else {
        return Ok(Value::Undefined);
    };

    let result = base_dt
        .checked_add(duration)
        .map_err(|err| anyhow::anyhow!("dateTimeAdd: datetime overflow: {err}"))?;

    let output = match args.get(2).and_then(as_str) {
        Some(fmt) => format_datetime_dotnet(&result, fmt)?,
        None => format_datetime(&result)?,
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
    let Ok(dt) = Timestamp::from_second(epoch) else {
        return Ok(Value::Undefined);
    };
    // Always UTC, so use Z suffix.
    Ok(Value::from(strtime::format("%Y-%m-%dT%H:%M:%SZ", dt)?))
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
    Ok(Value::from(dt.timestamp().as_second()))
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
    let duration = SignedDuration::from_secs(
        days.checked_mul(86400)
            .ok_or_else(|| anyhow::anyhow!("addDays: datetime overflow"))?,
    );
    let result = base_dt
        .checked_add(duration)
        .map_err(|err| anyhow::anyhow!("addDays: datetime overflow: {err}"))?;
    Ok(Value::from(format_datetime(&result)?))
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
    /// A strftime format string.
    Strftime(String),
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
fn format_datetime_dotnet(dt: &ZonedDateTime, dotnet_fmt: &str) -> Result<String> {
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
            format_dt = dt.with_time_zone(TimeZone::UTC);
            effective_fmt_owned = s;
            let is_utc = true;
            let segments = dotnet_to_segments(&effective_fmt_owned, is_utc);
            return render_segments(&format_dt, &segments);
        }
        StandardFormat::NotStandard => dotnet_fmt,
    };
    let is_utc = dt.offset().seconds() == 0;
    let segments = dotnet_to_segments(effective_fmt, is_utc);
    render_segments(dt, &segments)
}

/// Render pre-parsed format segments against a datetime value.
fn render_segments(dt: &ZonedDateTime, segments: &[FmtSegment]) -> Result<String> {
    let mut out = String::new();
    for seg in segments {
        match *seg {
            FmtSegment::Strftime(ref fmt) => {
                out.push_str(&strtime::format(fmt, dt)?);
            }
            FmtSegment::Frac(n) => {
                // %f gives 9-digit nanoseconds; take the first n digits.
                let nanos = strtime::format("%9f", dt)?;
                let truncated: String = nanos.chars().take(n).collect();
                out.push_str(&truncated);
            }
            FmtSegment::AmPmShort => {
                let full = strtime::format("%p", dt)?;
                if let Some(c) = full.chars().next() {
                    out.push(c);
                }
            }
            FmtSegment::TzHoursNoPad => {
                let hours = dt.offset().seconds() / 3600;
                if hours >= 0 {
                    out.push('+');
                }
                let _ = write!(out, "{hours}");
            }
            FmtSegment::TzHoursPad => {
                let secs = dt.offset().seconds();
                let hours = secs / 3600;
                if secs >= 0 {
                    let _ = write!(out, "+{hours:02}");
                } else {
                    let _ = write!(out, "-{:02}", hours.wrapping_neg());
                }
            }
        }
    }
    Ok(out)
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
/// Consecutive strftime-compatible tokens are batched into a single `Strftime`
/// segment; tokens that need custom logic produce their own segment.
fn dotnet_to_segments(fmt: &str, is_utc: bool) -> Vec<FmtSegment> {
    let mut segments: Vec<FmtSegment> = Vec::new();
    let mut strftime_buf = String::new();
    let chars: Vec<char> = fmt.chars().collect();
    let len = chars.len();
    let mut i: usize = 0;

    macro_rules! flush {
        () => {
            if !strftime_buf.is_empty() {
                segments.push(FmtSegment::Strftime(core::mem::take(&mut strftime_buf)));
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
                strftime_buf.push(next);
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
                    strftime_buf.push(c);
                    i = i.wrapping_add(1);
                }
            }
            // Year
            'y' if remaining >= 4 && matches_run(&chars, i, 'y', 4) => {
                strftime_buf.push_str("%Y");
                i = i.wrapping_add(4);
            }
            'y' if remaining >= 2 && matches_run(&chars, i, 'y', 2) => {
                strftime_buf.push_str("%y");
                i = i.wrapping_add(2);
            }
            // Month
            'M' if remaining >= 4 && matches_run(&chars, i, 'M', 4) => {
                strftime_buf.push_str("%B");
                i = i.wrapping_add(4);
            }
            'M' if remaining >= 3 && matches_run(&chars, i, 'M', 3) => {
                strftime_buf.push_str("%b");
                i = i.wrapping_add(3);
            }
            'M' if remaining >= 2 && matches_run(&chars, i, 'M', 2) => {
                strftime_buf.push_str("%m");
                i = i.wrapping_add(2);
            }
            'M' => {
                strftime_buf.push_str("%-m");
                i = i.wrapping_add(1);
            }
            // Day
            'd' if remaining >= 4 && matches_run(&chars, i, 'd', 4) => {
                strftime_buf.push_str("%A");
                i = i.wrapping_add(4);
            }
            'd' if remaining >= 3 && matches_run(&chars, i, 'd', 3) => {
                strftime_buf.push_str("%a");
                i = i.wrapping_add(3);
            }
            'd' if remaining >= 2 && matches_run(&chars, i, 'd', 2) => {
                strftime_buf.push_str("%d");
                i = i.wrapping_add(2);
            }
            'd' => {
                strftime_buf.push_str("%-d");
                i = i.wrapping_add(1);
            }
            // 24-hour
            'H' if remaining >= 2 && matches_run(&chars, i, 'H', 2) => {
                strftime_buf.push_str("%H");
                i = i.wrapping_add(2);
            }
            'H' => {
                strftime_buf.push_str("%-H");
                i = i.wrapping_add(1);
            }
            // 12-hour
            'h' if remaining >= 2 && matches_run(&chars, i, 'h', 2) => {
                strftime_buf.push_str("%I");
                i = i.wrapping_add(2);
            }
            'h' => {
                strftime_buf.push_str("%-I");
                i = i.wrapping_add(1);
            }
            // Minute
            'm' if remaining >= 2 && matches_run(&chars, i, 'm', 2) => {
                strftime_buf.push_str("%M");
                i = i.wrapping_add(2);
            }
            'm' => {
                strftime_buf.push_str("%-M");
                i = i.wrapping_add(1);
            }
            // Second
            's' if remaining >= 2 && matches_run(&chars, i, 's', 2) => {
                strftime_buf.push_str("%S");
                i = i.wrapping_add(2);
            }
            's' => {
                strftime_buf.push_str("%-S");
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
                // Clamp to 9 (nanosecond precision).
                segments.push(FmtSegment::Frac(count.min(9)));
            }
            // AM/PM
            't' if remaining >= 2 && matches_run(&chars, i, 't', 2) => {
                strftime_buf.push_str("%p");
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
                    strftime_buf.push('Z');
                } else {
                    strftime_buf.push_str("%:z");
                }
                i = i.wrapping_add(1);
            }
            // Timezone offset zzz → full offset +00:00
            'z' if remaining >= 3 && matches_run(&chars, i, 'z', 3) => {
                strftime_buf.push_str("%:z");
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
                strftime_buf.push(ch);
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
