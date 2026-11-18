// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
//
// This module contains methods for compatibility with Go's `time` package.
//
// Copyright (c) 2009 The Go Authors. All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
//    * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//    * Redistributions in binary form must reproduce the above
// copyright notice, this list of conditions and the following disclaimer
// in the documentation and/or other materials provided with the
// distribution.
//    * Neither the name of Google Inc. nor the names of its
// contributors may be used to endorse or promote products derived from
// this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

#![allow(
    clippy::arithmetic_side_effects,
    clippy::unseparated_literal_suffix,
    clippy::pattern_type_mismatch
)] // ported Go time parsing uses intentional arithmetic and explicit suffixes

use crate::*;
use anyhow::{bail, Result};
use core::fmt;
use jiff::{fmt::strtime, tz::Offset, SignedDuration as Duration, ZonedDateTime};

const NANOSECOND: u64 = 1;
const MICROSECOND: u64 = 1000 * NANOSECOND;
const MILLISECOND: u64 = 1000 * MICROSECOND;
const SECOND: u64 = 1000 * MILLISECOND;
const MINUTE: u64 = 60 * SECOND;
const HOUR: u64 = 60 * MINUTE;

#[derive(Debug)]
pub enum ParseDurationError {
    InvalidDuration(String),
    UnknownUnit(String),
    Overflow,
}

impl fmt::Display for ParseDurationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseDurationError::InvalidDuration(dur) => {
                write!(f, "invalid duration: {dur}")
            }
            ParseDurationError::UnknownUnit(unit) => {
                write!(f, "unknown unit: {unit}")
            }
            ParseDurationError::Overflow => {
                write!(f, "overflow")
            }
        }
    }
}

// Parses a duration string in the form of `10h12m45s`.
//
// Adapted from Go's `time.ParseDuration`:
// https://github.com/golang/go/blob/8db131082d08e497fd8e9383d0ff7715e1bef478/src/time/format.go#L1584-L1686
pub fn parse_duration(mut s: &str) -> Result<Duration, ParseDurationError> {
    // Input is in the format of `[-+]?([0-9]*(\.[0-9]*)?[a-z]+)+`
    let orig = s;

    // Consume [-+]?
    let neg = if s.starts_with('-') {
        s = &s[1..];
        true
    } else if s.starts_with('+') {
        s = &s[1..];
        false
    } else {
        false
    };

    // Special case: if all that is left is "0", this is zero.
    if s == "0" {
        return Ok(Duration::ZERO);
    }

    if s.is_empty() {
        return Err(ParseDurationError::InvalidDuration(orig.to_string()));
    }

    let mut dur = 0u64;

    while !s.is_empty() {
        // The next character must be [0-9.]
        if !(s.starts_with('.') || s.starts_with(|c: char| c.is_ascii_digit())) {
            return Err(ParseDurationError::InvalidDuration(orig.to_string()));
        }

        let previous_len = s.len();
        // v is the integers before the decimal point
        // Consume [0-9]*
        let (mut v, rem) = leading_int(s)?;
        s = rem;

        // whether we consumed anything before a period
        let pre = previous_len != s.len();

        // Consume (\.[0-9]*)?
        let mut post = false;
        let mut f = 0;
        let mut scale = 0.0;
        if !s.is_empty() && s.starts_with('.') {
            s = &s[1..];
            let previous_len = s.len();
            (f, scale, s) = leading_fraction(s);
            post = previous_len != s.len();
        }
        if !pre && !post {
            // no digits (e.g. ".s" or "-.s")
            return Err(ParseDurationError::InvalidDuration(orig.to_string()));
        }

        // Consume unit.
        let mut idx = 0;
        for (i, c) in s.char_indices() {
            if c == '.' || c.is_ascii_digit() {
                break;
            }
            idx = i;
        }

        let unit = match &s[..idx + 1] {
            "ns" => NANOSECOND,
            "us" => MICROSECOND,
            "µs" => MICROSECOND, // U+00B5 = micro symbol
            "μs" => MICROSECOND, // U+03BC = Greek letter mu
            "ms" => MILLISECOND,
            "s" => SECOND,
            "m" => MINUTE,
            "h" => HOUR,
            unkonwn => return Err(ParseDurationError::UnknownUnit(unkonwn.to_string())),
        };

        s = &s[idx + 1..];

        if v > ((1 << 63) / unit) {
            // overflow
            return Err(ParseDurationError::InvalidDuration(orig.to_string()));
        }
        v *= unit;
        if f > 0 {
            // f64 is needed to be nanosecond accurate for fractions of hours.
            // v >= 0 && (f*unit/scale) <= 3.6e+12 (ns/h, h is the largest unit)
            v += (f as f64 * (unit as f64 / scale)) as u64;
            if v > 1 << 63 {
                // overflow
                return Err(ParseDurationError::InvalidDuration(orig.to_string()));
            }
        }

        dur += v;
        if dur > 1 << 63 {
            return Err(ParseDurationError::InvalidDuration(orig.to_string()));
        }
    }

    if neg {
        let dur = dur as i64;
        if dur < 0 {
            return Ok(Duration::from_nanos(dur));
        }
        return Ok(-Duration::from_nanos(dur));
    }

    if dur > i64::MAX as u64 {
        return Err(ParseDurationError::InvalidDuration(orig.to_string()));
    }

    Ok(Duration::from_nanos(dur as i64))
}

fn leading_int(s: &str) -> Result<(u64, &str), ParseDurationError> {
    let mut last_idx = 0;
    let mut num: u64 = 0;
    for (i, c) in s.char_indices() {
        last_idx = i;

        let n = match c.to_digit(10) {
            Some(n) => n as u64,
            None => break,
        };

        if num > ((1 << 63) / 10) {
            // overflow
            return Err(ParseDurationError::Overflow);
        }

        num = num * 10 + n;

        if num > 1 << 63 {
            // overflow
            return Err(ParseDurationError::Overflow);
        }
    }

    Ok((num, &s[last_idx..]))
}

fn leading_fraction(s: &str) -> (u64, f64, &str) {
    let mut num: u64 = 0;
    let mut scale = 1.0;
    let mut overflow = false;
    let mut last_idx = 0;
    for (i, c) in s.char_indices() {
        last_idx = i;

        let n = match c.to_digit(10) {
            Some(n) => n as u64,
            None => break,
        };

        if overflow {
            continue;
        }

        if num > (i64::MAX as u64 / 10) {
            // It's possible for overflow to give a positive number, so take care.
            overflow = true;
            continue;
        }

        let y = num * 10 + n;
        if y > 1 << 63 {
            overflow = true;
            continue;
        }

        num = y;
        scale *= 10.0;
    }

    (num, scale, &s[last_idx..])
}

#[derive(Clone, Copy, Debug)]
enum GoTimeItem<'a> {
    Directive(&'static str),
    Literal(&'a str),
    Fraction(Option<usize>),
    ZoneName,
    ZoneOffset(&'static str, bool),
}

struct GoTimeFormatItems<'a> {
    remainder: &'a str,
    parsing: bool,
    pending_fraction: bool,
}

impl<'a> GoTimeFormatItems<'a> {
    const fn new(layout: &'a str, parsing: bool) -> Self {
        Self {
            remainder: layout,
            parsing,
            pending_fraction: false,
        }
    }
}

impl<'a> Iterator for GoTimeFormatItems<'a> {
    type Item = GoTimeItem<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        use GoTimeItem::*;
        if core::mem::take(&mut self.pending_fraction) {
            return Some(Fraction(None));
        }
        let first = self.remainder.chars().next()?;
        if matches!(first, '.' | ',') {
            let digits = &self.remainder[1..];
            if let Some(repeating @ ('0' | '9')) = digits.chars().next() {
                let count = digits.chars().take_while(|&c| c == repeating).count();
                if !digits[count..].starts_with(|c: char| c.is_ascii_digit()) {
                    let precision = match (first, repeating, count) {
                        (_, '0', 3 | 6 | 9) | (',', '9', 3 | 6 | 9) => Some(count),
                        _ => None,
                    };
                    self.remainder = &digits[count..];
                    return Some(Fraction(precision));
                }
            }
        }
        for &(token, item) in &[
            ("January", Directive("%B")),
            ("Jan", Directive("%b")),
            ("Monday", Directive("%A")),
            ("Mon", Directive("%a")),
            ("MST", ZoneName),
            ("002", Directive("%j")),
            ("01", Directive("%m")),
            ("02", Directive("%d")),
            ("03", Directive("%I")),
            ("04", Directive("%M")),
            ("05", Directive("%S")),
            ("06", Directive("%y")),
            ("15", Directive("%H")),
            ("1", Directive("%-m")),
            ("2006", Directive("%Y")),
            ("2", Directive("%-d")),
            ("_2006", Directive("_%-Y")),
            ("__2", Directive("%_j")),
            ("_2", Directive("%e")),
            ("3", Directive("%-I")),
            ("4", Directive("%-M")),
            ("5", Directive("%-S")),
            ("PM", Directive("%p")),
            ("pm", Directive("%P")),
            ("-070000", ZoneOffset("%::z", false)),
            ("-07:00:00", ZoneOffset("%::z", false)),
            ("-0700", ZoneOffset("%z", false)),
            ("-07:00", ZoneOffset("%:z", false)),
            ("-07", ZoneOffset("%:::z", false)),
            ("Z0700", ZoneOffset("%z", true)),
            ("Z07:00", ZoneOffset("%:z", true)),
        ] {
            if let Some(rest) = self.remainder.strip_prefix(token) {
                self.remainder = rest;
                self.pending_fraction =
                    self.parsing && matches!(token, "05" | "5") && !rest.starts_with('.');
                return Some(item);
            }
        }
        let literal = &self.remainder[..first.len_utf8()];
        self.remainder = &self.remainder[first.len_utf8()..];
        Some(Literal(literal))
    }
}

fn push_literal(format: &mut String, literal: &str) {
    for ch in literal.chars() {
        format.push(ch);
        if ch == '%' {
            format.push('%');
        }
    }
}

fn legacy_offset(name: &str) -> Option<Offset> {
    let hours = match name.to_ascii_lowercase().as_str() {
        "utc" | "gmt" | "ut" => 0,
        "edt" => -4,
        "est" | "cdt" => -5,
        "cst" | "mdt" => -6,
        "mst" | "pdt" => -7,
        "pst" => -8,
        _ => return None,
    };
    Some(jiff::tz::offset(hours))
}

// Parses Go layouts while retaining their optional fractions and legacy zones.
pub fn parse(layout: &str, value: &str) -> Result<ZonedDateTime> {
    let mut format = String::new();
    let mut offset = None;
    let mut leap_second = false;
    for item in GoTimeFormatItems::new(layout, true) {
        match item {
            GoTimeItem::Directive(directive) => {
                if matches!(directive, "%S" | "%-S") {
                    let (_, consumed) = strtime::BrokenDownTime::parse_prefix(&format, value)?;
                    leap_second = value[consumed..].starts_with("60");
                }
                format.push_str(directive);
            }
            GoTimeItem::Literal(literal) => push_literal(&mut format, literal),
            GoTimeItem::Fraction(_) => format.push_str("%.f"),
            GoTimeItem::ZoneName | GoTimeItem::ZoneOffset(_, true) => {
                let (_, consumed) = strtime::BrokenDownTime::parse_prefix(&format, value)?;
                let remainder = &value[consumed..];
                if matches!(item, GoTimeItem::ZoneName) {
                    let len = remainder
                        .bytes()
                        .take_while(u8::is_ascii_alphabetic)
                        .count();
                    if len == 0 {
                        bail!("missing timezone name");
                    }
                    let name = &remainder[..len];
                    if let Some(zone_offset) = legacy_offset(name) {
                        if offset.is_some_and(|offset| offset != zone_offset) {
                            bail!("conflicting timezone offsets");
                        }
                        offset = Some(zone_offset);
                    }
                    push_literal(&mut format, name);
                } else if remainder.starts_with('Z') {
                    if offset.is_some_and(|offset| offset != Offset::ZERO) {
                        bail!("conflicting timezone offsets");
                    }
                    format.push('Z');
                    offset = Some(Offset::ZERO);
                } else if let GoTimeItem::ZoneOffset(directive, _) = item {
                    format.push_str(directive);
                }
            }
            GoTimeItem::ZoneOffset(directive, false) => format.push_str(directive),
        }
    }
    let mut parsed = strtime::BrokenDownTime::parse(&format, value)?;
    if parsed.year().is_none() {
        parsed.set_year(Some(0))?;
    }
    if parsed.hour().is_none() && parsed.minute().is_none() && parsed.second().is_none() {
        parsed.set_hour(Some(0))?;
        parsed.set_minute(Some(0))?;
        parsed.set_second(Some(0))?;
    }
    if let Some(offset) = offset {
        if parsed.offset().is_some_and(|parsed| parsed != offset) {
            bail!("conflicting timezone offsets");
        }
        parsed.set_offset(Some(offset));
    } else if parsed.offset().is_none() {
        parsed.set_offset(Some(Offset::ZERO));
    }
    if parsed
        .offset()
        .is_some_and(|offset| offset.seconds().unsigned_abs() >= 86400)
    {
        bail!("timezone offset outside of valid range");
    }
    let datetime = parsed.to_zoned_datetime()?;
    if leap_second {
        Ok(datetime.checked_add(Duration::from_secs(1))?)
    } else {
        Ok(datetime)
    }
}

// Formats Go layouts without exposing strftime directives in literal text.
pub fn format(date: &ZonedDateTime, layout: &str) -> Result<String> {
    let mut output = String::new();
    for item in GoTimeFormatItems::new(layout, false) {
        let directive = match item {
            GoTimeItem::Literal(literal) => {
                output.push_str(literal);
                continue;
            }
            GoTimeItem::Directive(directive) => directive,
            GoTimeItem::ZoneName => {
                if date.time_zone().to_fixed_offset().is_ok() {
                    "%:z"
                } else {
                    "%Z"
                }
            }
            GoTimeItem::ZoneOffset(_, true) if date.offset() == Offset::ZERO => "Z",
            GoTimeItem::ZoneOffset(directive, _) => directive,
            GoTimeItem::Fraction(precision) => {
                let precision = precision.unwrap_or_else(|| {
                    super::super::datetime::fractional_precision(date.subsec_nanosecond())
                });
                if precision != 0 {
                    output.push_str(&strtime::format(format!("%.{precision}f"), date)?);
                }
                continue;
            }
        };
        output.push_str(&strtime::format(directive, date)?);
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    #![allow(
        clippy::unwrap_used,
        clippy::unused_trait_names,
        clippy::as_conversions
    )] // test fixtures build durations with unwrap for brevity
    use jiff::{civil::Weekday, Timestamp};

    use super::*;

    #[test]
    fn parses_durations() {
        // Test cases are copied from Go's `time.ParseDuration` tests:
        // https://github.com/golang/go/blob/8db131082d08e497fd8e9383d0ff7715e1bef478/src/time/time_test.go#L891-L951

        for (input, expected_dur) in [
            // simple
            ("0", Duration::ZERO),
            ("5s", Duration::from_secs(5)),
            ("30s", Duration::from_secs(30)),
            ("1478s", Duration::from_secs(1478)),
            // sign
            ("-5s", -Duration::from_secs(5)),
            ("+5s", Duration::from_secs(5)),
            ("-0", Duration::ZERO),
            ("+0", Duration::ZERO),
            // decimal
            ("5.0s", Duration::from_secs(5)),
            ("5.6s", Duration::from_secs(5) + Duration::from_millis(600)),
            ("5.s", Duration::from_secs(5)),
            (".5s", Duration::from_millis(500)),
            ("1.0s", Duration::from_secs(1)),
            ("1.00s", Duration::from_secs(1)),
            ("1.004s", Duration::from_secs(1) + Duration::from_millis(4)),
            ("1.0040s", Duration::from_secs(1) + Duration::from_millis(4)),
            (
                "100.00100s",
                Duration::from_secs(100) + Duration::from_millis(1),
            ),
            // different units
            ("10ns", Duration::from_nanos(10)),
            ("11us", Duration::from_micros(11)),
            ("12µs", Duration::from_micros(12)), // U+00B5
            ("12μs", Duration::from_micros(12)), // U+03BC
            ("13ms", Duration::from_millis(13)),
            ("14s", Duration::from_secs(14)),
            ("15m", Duration::from_mins(15)),
            ("16h", Duration::from_hours(16)),
            // composite durations
            ("3h30m", Duration::from_hours(3) + Duration::from_mins(30)),
            (
                "10.5s4m",
                Duration::from_mins(4) + Duration::from_secs(10) + Duration::from_millis(500),
            ),
            (
                "-2m3.4s",
                -(Duration::from_mins(2) + Duration::from_secs(3) + Duration::from_millis(400)),
            ),
            (
                "1h2m3s4ms5us6ns",
                Duration::from_hours(1)
                    + Duration::from_mins(2)
                    + Duration::from_secs(3)
                    + Duration::from_millis(4)
                    + Duration::from_micros(5)
                    + Duration::from_nanos(6),
            ),
            (
                "39h9m14.425s",
                Duration::from_hours(39)
                    + Duration::from_mins(9)
                    + Duration::from_secs(14)
                    + Duration::from_millis(425),
            ),
            // large value
            ("52763797000ns", Duration::from_nanos(52763797000)),
            // more than 9 digits after decimal point, see https://golang.org/issue/6617
            ("0.3333333333333333333h", Duration::from_mins(20)),
            // 9007199254740993 = 1<<53+1 cannot be stored precisely in a float64
            ("9007199254740993ns", Duration::from_nanos((1 << 53) + 1)),
            // largest duration that can be represented by int64 in nanoseconds
            ("9223372036854775807ns", Duration::from_nanos(i64::MAX)),
            ("9223372036854775.807us", Duration::from_nanos(i64::MAX)),
            ("9223372036s854ms775us807ns", Duration::from_nanos(i64::MAX)),
            ("-9223372036854775808ns", Duration::from_nanos(i64::MIN)),
            ("-9223372036854775.808us", Duration::from_nanos(i64::MIN)),
            (
                "-9223372036s854ms775us808ns",
                Duration::from_nanos(i64::MIN),
            ),
            // largest negative value
            ("-9223372036854775808ns", Duration::from_nanos(i64::MIN)),
            // largest negative round trip value, see https://golang.org/issue/48629
            ("-2562047h47m16.854775808s", Duration::from_nanos(i64::MIN)),
            // huge string; issue 15011.
            ("0.100000000000000000000h", Duration::from_mins(6)),
            // This value tests the first overflow check in leadingFraction.
            (
                "0.830103483285477580700h",
                Duration::from_mins(49) + Duration::from_secs(48) + Duration::from_nanos(372539827),
            ),
        ] {
            let dur = parse_duration(input).unwrap();
            assert_eq!(dur, expected_dur);
        }
    }

    #[test]
    fn parses_datetimes() {
        // Test cases are copied from Go's `time.Parse` tests:
        // https://github.com/golang/go/blob/e9b3ff15f40d6b258217b3467c662f816b078477/src/time/format_test.go#L266-L339

        struct ParseTest {
            name: String,
            format: String,
            value: String,
            has_tz: bool,       // contains a time zone
            has_wd: bool,       // contains a weekday
            year_sign: i32,     // sign of year, -1 indicates the year is not present in the format
            frac_digits: usize, // number of digits of fractional second
        }

        fn parse_test_case(
            name: &str,
            format: &str,
            value: &str,
            has_tz: bool,
            has_wd: bool,
            year_sign: i32,
            frac_digits: usize,
        ) -> ParseTest {
            ParseTest {
                name: name.to_string(),
                format: format.to_string(),
                value: value.to_string(),
                has_tz,
                has_wd,
                year_sign,
                frac_digits,
            }
        }

        fn check_time(time: ZonedDateTime, test_case: &ParseTest) {
            // The time should be Thu Feb  4 21:00:57 PST 2010
            if test_case.year_sign >= 0 {
                assert_eq!(test_case.year_sign * i32::from(time.year()), 2010);
            }
            assert_eq!(time.month(), 2);
            assert_eq!(time.day(), 4);
            assert_eq!(time.hour(), 21);
            assert_eq!(time.minute(), 0);
            assert_eq!(time.second(), 57);

            let nanosec = "012345678"[..test_case.frac_digits].to_string()
                + &"000000000"[..9 - test_case.frac_digits];
            assert_eq!(time.subsec_nanosecond(), nanosec.parse::<i32>().unwrap());

            if test_case.has_tz {
                assert_eq!(time.offset().seconds(), -28800);
            }

            if test_case.has_wd {
                assert_eq!(time.weekday(), Weekday::Thursday);
            }
        }

        let test_cases = vec![
            parse_test_case(
                "ANSIC",
                ANSIC,
                "Thu Feb  4 21:00:57 2010",
                false,
                true,
                1,
                0,
            ),
            parse_test_case(
                "UnixDate",
                UNIX_DATE,
                "Thu Feb  4 21:00:57 PST 2010",
                true,
                true,
                1,
                0,
            ),
            parse_test_case(
                "RubyDate",
                RUBY_DATE,
                "Thu Feb 04 21:00:57 -0800 2010",
                true,
                true,
                1,
                0,
            ),
            parse_test_case(
                "RFC850",
                RFC850,
                "Thursday, 04-Feb-10 21:00:57 PST",
                true,
                true,
                1,
                0,
            ),
            parse_test_case(
                "RFC1123",
                RFC1123,
                "Thu, 04 Feb 2010 21:00:57 PST",
                true,
                true,
                1,
                0,
            ),
            // parse_test_case(
            //     "RFC1123",
            //     RFC1123,
            //     "Thu, 04 Feb 2010 22:00:57 PDT",
            //     true,
            //     true,
            //     1,
            //     0,
            // ),
            parse_test_case(
                "RFC1123Z",
                RFC1123Z,
                "Thu, 04 Feb 2010 21:00:57 -0800",
                true,
                true,
                1,
                0,
            ),
            parse_test_case(
                "RFC3339",
                RFC3339,
                "2010-02-04T21:00:57-08:00",
                true,
                false,
                1,
                0,
            ),
            // parse_test_case(
            //     "custom: \"2006-01-02 15:04:05-07\"",
            //     "2006-01-02 15:04:05-07",
            //     "2010-02-04 21:00:57-08",
            //     true,
            //     false,
            //     1,
            //     0,
            // ),
            // Optional fractional seconds.
            parse_test_case(
                "ANSIC",
                ANSIC,
                "Thu Feb  4 21:00:57.0 2010",
                false,
                true,
                1,
                1,
            ),
            parse_test_case(
                "UnixDate",
                UNIX_DATE,
                "Thu Feb  4 21:00:57.01 PST 2010",
                true,
                true,
                1,
                2,
            ),
            parse_test_case(
                "RubyDate",
                RUBY_DATE,
                "Thu Feb 04 21:00:57.012 -0800 2010",
                true,
                true,
                1,
                3,
            ),
            parse_test_case(
                "RFC850",
                RFC850,
                "Thursday, 04-Feb-10 21:00:57.0123 PST",
                true,
                true,
                1,
                4,
            ),
            parse_test_case(
                "RFC1123",
                RFC1123,
                "Thu, 04 Feb 2010 21:00:57.01234 PST",
                true,
                true,
                1,
                5,
            ),
            parse_test_case(
                "RFC1123Z",
                RFC1123Z,
                "Thu, 04 Feb 2010 21:00:57.01234 -0800",
                true,
                true,
                1,
                5,
            ),
            parse_test_case(
                "RFC3339",
                RFC3339,
                "2010-02-04T21:00:57.012345678-08:00",
                true,
                false,
                1,
                9,
            ),
            parse_test_case(
                "custom: \"2006-01-02 15:04:05\"",
                "2006-01-02 15:04:05",
                "2010-02-04 21:00:57.0",
                false,
                false,
                1,
                0,
            ),
            // Amount of white space should not matter.
            parse_test_case("ANSIC", ANSIC, "Thu Feb 4 21:00:57 2010", false, true, 1, 0),
            parse_test_case(
                "ANSIC",
                ANSIC,
                "Thu      Feb     4     21:00:57     2010",
                false,
                true,
                1,
                0,
            ),
            // Case should not matter
            parse_test_case("ANSIC", ANSIC, "THU FEB 4 21:00:57 2010", false, true, 1, 0),
            parse_test_case("ANSIC", ANSIC, "thu feb 4 21:00:57 2010", false, true, 1, 0),
            // Fractional seconds.
            parse_test_case(
                "millisecond:: dot separator",
                "Mon Jan _2 15:04:05.000 2006",
                "Thu Feb  4 21:00:57.012 2010",
                false,
                true,
                1,
                3,
            ),
            parse_test_case(
                "microsecond:: dot separator",
                "Mon Jan _2 15:04:05.000000 2006",
                "Thu Feb  4 21:00:57.012345 2010",
                false,
                true,
                1,
                6,
            ),
            parse_test_case(
                "nanosecond:: dot separator",
                "Mon Jan _2 15:04:05.000000000 2006",
                "Thu Feb  4 21:00:57.012345678 2010",
                false,
                true,
                1,
                9,
            ),
            parse_test_case(
                "millisecond:: comma separator",
                "Mon Jan _2 15:04:05,000 2006",
                "Thu Feb  4 21:00:57.012 2010",
                false,
                true,
                1,
                3,
            ),
            parse_test_case(
                "microsecond:: comma separator",
                "Mon Jan _2 15:04:05,000000 2006",
                "Thu Feb  4 21:00:57.012345 2010",
                false,
                true,
                1,
                6,
            ),
            parse_test_case(
                "nanosecond:: comma separator",
                "Mon Jan _2 15:04:05,000000000 2006",
                "Thu Feb  4 21:00:57.012345678 2010",
                false,
                true,
                1,
                9,
            ),
            // Leading zeros in other places should not be taken as fractional seconds.
            parse_test_case(
                "zero1",
                "2006.01.02.15.04.05.0",
                "2010.02.04.21.00.57.0",
                false,
                false,
                1,
                1,
            ),
            parse_test_case(
                "zero2",
                "2006.01.02.15.04.05.00",
                "2010.02.04.21.00.57.01",
                false,
                false,
                1,
                2,
            ),
            // Month and day names only match when not followed by a lower-case letter.
            // parse_test_case(
            //     "Janet",
            //     "Hi Janet, the Month is January: Jan _2 15:04:05 2006",
            //     "Hi Janet, the Month is February: Feb  4 21:00:57 2010",
            //     false,
            //     true,
            //     1,
            //     0,
            // ),
            // GMT with offset.
            // parse_test_case(
            //     "GMT-8",
            //     UNIX_DATE,
            //     "Fri Feb  5 05:00:57 GMT-8 2010",
            //     true,
            //     true,
            //     1,
            //     0,
            // ),
            // Accept any number of fractional second digits (including none) for .999...
            // In Go 1, .999... was completely ignored in the format, meaning the first two
            // cases would succeed, but the next four would not. Go 1.1 accepts all six.
            // decimal "." separator.
            parse_test_case(
                "",
                "2006-01-02 15:04:05.9999 -0700 MST",
                "2010-02-04 21:00:57 -0800 PST",
                true,
                false,
                1,
                0,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05.999999999 -0700 MST",
                "2010-02-04 21:00:57 -0800 PST",
                true,
                false,
                1,
                0,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05.9999 -0700 MST",
                "2010-02-04 21:00:57.0123 -0800 PST",
                true,
                false,
                1,
                4,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05.999999999 -0700 MST",
                "2010-02-04 21:00:57.0123 -0800 PST",
                true,
                false,
                1,
                4,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05.9999 -0700 MST",
                "2010-02-04 21:00:57.012345678 -0800 PST",
                true,
                false,
                1,
                9,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05.999999999 -0700 MST",
                "2010-02-04 21:00:57.012345678 -0800 PST",
                true,
                false,
                1,
                9,
            ),
            // comma "," separator.
            parse_test_case(
                "",
                "2006-01-02 15:04:05,9999 -0700 MST",
                "2010-02-04 21:00:57 -0800 PST",
                true,
                false,
                1,
                0,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05,999999999 -0700 MST",
                "2010-02-04 21:00:57 -0800 PST",
                true,
                false,
                1,
                0,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05,9999 -0700 MST",
                "2010-02-04 21:00:57.0123 -0800 PST",
                true,
                false,
                1,
                4,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05,999999999 -0700 MST",
                "2010-02-04 21:00:57.0123 -0800 PST",
                true,
                false,
                1,
                4,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05,9999 -0700 MST",
                "2010-02-04 21:00:57.012345678 -0800 PST",
                true,
                false,
                1,
                9,
            ),
            parse_test_case(
                "",
                "2006-01-02 15:04:05,999999999 -0700 MST",
                "2010-02-04 21:00:57.012345678 -0800 PST",
                true,
                false,
                1,
                9,
            ),
            // issue 4502.
            parse_test_case(
                "",
                STAMP_NANO,
                "Feb  4 21:00:57.012345678",
                false,
                false,
                -1,
                9,
            ),
            parse_test_case(
                "",
                "Jan _2 15:04:05.999",
                "Feb  4 21:00:57.012300000",
                false,
                false,
                -1,
                4,
            ),
            parse_test_case(
                "",
                "Jan _2 15:04:05.999",
                "Feb  4 21:00:57.012345678",
                false,
                false,
                -1,
                9,
            ),
            parse_test_case(
                "",
                "Jan _2 15:04:05.999999999",
                "Feb  4 21:00:57.0123",
                false,
                false,
                -1,
                4,
            ),
            parse_test_case(
                "",
                "Jan _2 15:04:05.999999999",
                "Feb  4 21:00:57.012345678",
                false,
                false,
                -1,
                9,
            ),
            // Day of year.
            parse_test_case(
                "",
                "2006-01-02 002 15:04:05",
                "2010-02-04 035 21:00:57",
                false,
                false,
                1,
                0,
            ),
            parse_test_case(
                "",
                "2006-01 002 15:04:05",
                "2010-02 035 21:00:57",
                false,
                false,
                1,
                0,
            ),
            parse_test_case(
                "",
                "2006-002 15:04:05",
                "2010-035 21:00:57",
                false,
                false,
                1,
                0,
            ),
            parse_test_case(
                "",
                "200600201 15:04:05",
                "201003502 21:00:57",
                false,
                false,
                1,
                0,
            ),
            // parse_test_case(
            //     "",
            //     "200600204 15:04:05",
            //     "201003504 21:00:57",
            //     false,
            //     false,
            //     1,
            //     0,
            // ),
        ];

        for tc in test_cases {
            std::println!("Test case {}", tc.name);
            let time = parse(&tc.format, &tc.value).unwrap();
            check_time(time, &tc);
        }
    }

    #[test]
    fn formats_datetimes() {
        // Test cases are copied from Go's `time.Format` tests:
        // https://github.com/golang/go/blob/e9b3ff15f40d6b258217b3467c662f816b078477/src/time/format_test.go#L144-L176

        struct FormatTest {
            name: String,
            format: String,
            result: String,
        }

        fn format_test_case(name: &str, format: &str, result: &str) -> FormatTest {
            FormatTest {
                name: name.to_string(),
                format: format.to_string(),
                result: result.to_string(),
            }
        }

        let test_cases = vec![
            format_test_case("ANSIC", ANSIC, "Wed Feb  4 21:00:57 2009"),
            format_test_case("UnixDate", UNIX_DATE, "Wed Feb  4 21:00:57 PST 2009"),
            format_test_case("RubyDate", RUBY_DATE, "Wed Feb 04 21:00:57 -0800 2009"),
            format_test_case("RFC822", RFC822, "04 Feb 09 21:00 PST"),
            format_test_case("RFC850", RFC850, "Wednesday, 04-Feb-09 21:00:57 PST"),
            format_test_case("RFC1123", RFC1123, "Wed, 04 Feb 2009 21:00:57 PST"),
            format_test_case("RFC1123Z", RFC1123Z, "Wed, 04 Feb 2009 21:00:57 -0800"),
            format_test_case("RFC3339", RFC3339, "2009-02-04T21:00:57-08:00"),
            // format_test_case(
            //     "RFC3339Nano",
            //     RFC3339_NANO,
            //     "2009-02-04T21:00:57.0123456-08:00",
            // ),
            format_test_case("Kitchen", KITCHEN, "9:00PM"),
            format_test_case("am/pm", "3pm", "9pm"),
            format_test_case("AM/PM", "3PM", "9PM"),
            format_test_case("two-digit year", "06 01 02", "09 02 04"),
            // Three-letter months and days must not be followed by lower-case letter.
            // format_test_case(
            //     "Janet",
            //     "Hi Janet, the Month is January",
            //     "Hi Janet, the Month is February",
            // ),
            // Time stamps, Fractional seconds.
            format_test_case("Stamp", STAMP, "Feb  4 21:00:57"),
            format_test_case("StampMilli", STAMP_MILLI, "Feb  4 21:00:57.012"),
            format_test_case("StampMicro", STAMP_MICRO, "Feb  4 21:00:57.012345"),
            format_test_case("StampNano", STAMP_NANO, "Feb  4 21:00:57.012345600"),
            format_test_case("DateTime", DATE_TIME, "2009-02-04 21:00:57"),
            format_test_case("DateOnly", DATE_ONLY, "2009-02-04"),
            format_test_case("TimeOnly", TIME_ONLY, "21:00:57"),
            format_test_case("YearDay", "Jan  2 002 __2 2", "Feb  4 035  35 4"),
            // format_test_case("Year", "2006 6 06 _6 __6 ___6", "2009 6 09 _6 __6 ___6"),
            // format_test_case("Month", "Jan January 1 01 _1", "Feb February 2 02 _2"),
            format_test_case("DayOfMonth", "2 02 _2 __2", "4 04  4  35"),
            format_test_case("DayOfWeek", "Mon Monday", "Wed Wednesday"),
            // format_test_case("Hour", "15 3 03 _3", "21 9 09 _9"),
            // format_test_case("Minute", "4 04 _4", "0 00 _0"),
            // format_test_case("Second", "5 05 _5", "57 57 _57"),
        ];

        // The numeric time represents Thu Feb  4 21:00:57.012345600 PST 2009
        let time = Timestamp::from_nanosecond(1233810057012345600)
            .unwrap()
            .in_tz("America/Los_Angeles")
            .unwrap();

        for tc in test_cases {
            std::println!("Test case {}", tc.name);
            let result = format(&time, &tc.format).unwrap();
            assert_eq!(result, tc.result);
        }
    }

    #[test]
    fn parses_date_only() {
        let time = parse("2006-01-02", "2020-02-02").unwrap();
        assert_eq!(time.year(), 2020);
        assert_eq!(time.month(), 2);
        assert_eq!(time.day(), 2);
    }

    const _LAYOUT: &str = "01/02 03:04:05PM '06 -0700"; // The reference time, in numerical order.
    const ANSIC: &str = "Mon Jan _2 15:04:05 2006";
    const UNIX_DATE: &str = "Mon Jan _2 15:04:05 MST 2006";
    const RUBY_DATE: &str = "Mon Jan 02 15:04:05 -0700 2006";
    const RFC822: &str = "02 Jan 06 15:04 MST";
    const _RFC822Z: &str = "02 Jan 06 15:04 -0700"; // RFC822 with numeric zone
    const RFC850: &str = "Monday, 02-Jan-06 15:04:05 MST";
    const RFC1123: &str = "Mon, 02 Jan 2006 15:04:05 MST";
    const RFC1123Z: &str = "Mon, 02 Jan 2006 15:04:05 -0700"; // RFC1123 with numeric zone
    const RFC3339: &str = "2006-01-02T15:04:05Z07:00";
    const _RFC3339_NANO: &str = "2006-01-02T15:04:05.999999999Z07:00";
    const KITCHEN: &str = "3:04PM";
    // Handy time stamps.
    const STAMP: &str = "Jan _2 15:04:05";
    const STAMP_MILLI: &str = "Jan _2 15:04:05.000";
    const STAMP_MICRO: &str = "Jan _2 15:04:05.000000";
    const STAMP_NANO: &str = "Jan _2 15:04:05.000000000";
    const DATE_TIME: &str = "2006-01-02 15:04:05";
    const DATE_ONLY: &str = "2006-01-02";
    const TIME_ONLY: &str = "15:04:05";
}
