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

use std::error::Error;
use std::fmt;
use std::iter;

use chrono::TimeZone;
use chrono::{
    format::{self, Fixed, Parsed},
    DateTime, Duration, FixedOffset, ParseResult,
};

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

impl Error for ParseDurationError {}

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
        return Ok(Duration::zero());
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
            return Ok(Duration::nanoseconds(dur));
        }
        return Ok(-Duration::nanoseconds(dur));
    }

    if dur > i64::MAX as u64 {
        return Err(ParseDurationError::InvalidDuration(orig.to_string()));
    }

    Ok(Duration::nanoseconds(dur as i64))
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

#[derive(Debug, Clone, PartialEq, Eq)]
enum GoTimeFormatItemsMode {
    Parse,
    Format,
}

#[derive(Debug, Clone)]
struct GoTimeFormatItems<'a> {
    reminder: &'a str,
    queue: &'static [format::Item<'static>],
    mode: GoTimeFormatItemsMode,
}

impl<'a> GoTimeFormatItems<'a> {
    fn parse(reminder: &str) -> GoTimeFormatItems {
        GoTimeFormatItems {
            reminder,
            queue: &[],
            mode: GoTimeFormatItemsMode::Parse,
        }
    }

    fn format(reminder: &str) -> GoTimeFormatItems {
        GoTimeFormatItems {
            reminder,
            queue: &[],
            mode: GoTimeFormatItemsMode::Format,
        }
    }
}

impl<'a> Iterator for GoTimeFormatItems<'a> {
    type Item = format::Item<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        use format::{Fixed::*, Item::*, Numeric, Pad};

        macro_rules! token {
            ($prefix:expr, $kind:expr $(, $queue:expr)*) => {
                if self.reminder.starts_with($prefix) {
                    self.reminder = &self.reminder[$prefix.len()..];
                    self.queue = &[$($queue),*];
                    return Some($kind);
                }
            };
        }

        fn is_fractional_seconds(val: &str) -> bool {
            // first char is either '.' or ','
            let mut chars = val.chars().skip(1);
            let Some(repeating @ ('0' | '9')) = chars.next() else {
                return false;
            };
            let next = chars.find(|c| c != &repeating);
            !matches!(next, Some('0'..='9'))
        }

        if let Some((item, reminder)) = self.queue.split_first() {
            self.queue = reminder;
            return Some(item.clone());
        }

        match self.reminder.chars().next() {
            // January, Jan
            Some('J') => {
                token!("January", Fixed(LongMonthName));
                token!("Jan", Fixed(ShortMonthName));
            }

            // Monday, Mon, MST
            Some('M') => {
                token!("Monday", Fixed(LongWeekdayName));
                token!("Mon", Fixed(ShortWeekdayName));
                token!("MST", Fixed(TimezoneName));
            }

            // 01, 02, 03, 04, 05, 06, 002
            Some('0') => {
                token!("002", Numeric(Numeric::Ordinal, Pad::Zero));
                token!("01", Numeric(Numeric::Month, Pad::Zero));
                token!("02", Numeric(Numeric::Day, Pad::Zero));
                token!("03", Numeric(Numeric::Hour12, Pad::Zero));
                token!("04", Numeric(Numeric::Minute, Pad::Zero));

                if self.reminder.starts_with("05") {
                    self.reminder = &self.reminder[2..];
                    if !self.reminder.starts_with('.') && self.mode == GoTimeFormatItemsMode::Parse
                    {
                        self.queue = &[Fixed(Nanosecond)];
                    }
                    return Some(Numeric(Numeric::Second, Pad::Zero));
                }

                token!("06", Numeric(Numeric::YearMod100, Pad::Zero));
            }

            // 15, 1
            Some('1') => {
                use Numeric::*;
                token!("15", Numeric(Hour, Pad::Zero));
                token!("1", Numeric(Month, Pad::None));
            }

            // 2006, 2
            Some('2') => {
                use Numeric::*;
                token!("2006", Numeric(Year, Pad::Zero));
                token!("2", Numeric(Day, Pad::None));
            }
            // _2, _2006, __2
            Some('_') => {
                use Numeric::*;
                token!("_2006", Literal("_"), Numeric(Year, Pad::None));
                token!("__2", Numeric(Ordinal, Pad::Space));
                token!("_2", Numeric(Day, Pad::Space));
            }

            Some('3') => {
                use Numeric::*;
                token!("3", Numeric(Hour12, Pad::None));
            }

            Some('4') => {
                use Numeric::*;
                token!("4", Numeric(Minute, Pad::None));
            }

            Some('5') => {
                token!("5", Numeric(Numeric::Second, Pad::None), Fixed(Nanosecond));
            }

            // PM
            Some('P') => {
                token!("PM", Fixed(UpperAmPm));
            }

            // pm
            Some('p') => {
                token!("pm", Fixed(LowerAmPm));
            }

            // -070000, -07:00:00, -0700, -07:00, -07
            Some('-') => {
                token!("-070000", Fixed(TimezoneOffsetDoubleColon));
                token!("-07:00:00", Fixed(TimezoneOffsetDoubleColon));

                token!("-0700", Fixed(TimezoneOffset));
                token!("-07:00", Fixed(TimezoneOffsetColon));

                token!("-07", Fixed(TimezoneOffsetTripleColon));

                token!("-", Literal("-"));
            }

            // Z070000, Z07:00:00, Z0700, Z07:00, Z07
            Some('Z') => {
                // token!("Z070000", Fixed(TimezoneOffsetDoubleColonZ));
                // token!("Z07:00:00", Fixed(TimezoneOffsetDoubleColonZ));

                token!("Z0700", Fixed(TimezoneOffsetZ));
                token!("Z07:00", Fixed(TimezoneOffsetColonZ));

                // token!("Z07", Fixed(TimezoneOffsetTripleColonZ));
            }

            // ,000, or .000, or ,999, or .999 - repeated digits for fractional seconds.
            Some('.' | ',') if is_fractional_seconds(self.reminder) => {
                token!(".000000000", Fixed(Nanosecond9));
                token!(".00000000", Fixed(Nanosecond));
                token!(".0000000", Fixed(Nanosecond));
                token!(".000000", Fixed(Nanosecond6));
                token!(".00000", Fixed(Nanosecond));
                token!(".0000", Fixed(Nanosecond));
                token!(".000", Fixed(Nanosecond3));
                token!(".00", Fixed(Nanosecond));
                token!(".0", Fixed(Nanosecond));
                token!(".999999999", Fixed(Nanosecond));
                token!(".99999999", Fixed(Nanosecond));
                token!(".9999999", Fixed(Nanosecond));
                token!(".999999", Fixed(Nanosecond));
                token!(".99999", Fixed(Nanosecond));
                token!(".9999", Fixed(Nanosecond));
                token!(".999", Fixed(Nanosecond));
                token!(".99", Fixed(Nanosecond));
                token!(".9", Fixed(Nanosecond));
                token!(".", Literal("."));

                token!(",000000000", Fixed(Nanosecond9));
                token!(",00000000", Fixed(Nanosecond));
                token!(",0000000", Fixed(Nanosecond));
                token!(",000000", Fixed(Nanosecond6));
                token!(",00000", Fixed(Nanosecond));
                token!(",0000", Fixed(Nanosecond));
                token!(",000", Fixed(Nanosecond3));
                token!(",00", Fixed(Nanosecond));
                token!(",0", Fixed(Nanosecond));
                token!(",999999999", Fixed(Nanosecond9));
                token!(",99999999", Fixed(Nanosecond));
                token!(",9999999", Fixed(Nanosecond));
                token!(",999999", Fixed(Nanosecond6));
                token!(",99999", Fixed(Nanosecond));
                token!(",9999", Fixed(Nanosecond));
                token!(",999", Fixed(Nanosecond3));
                token!(",99", Fixed(Nanosecond));
                token!(",9", Fixed(Nanosecond));
                token!(",", Literal(","));
            }
            Some(c) if c.is_whitespace() => {
                let next_non_ws = self
                    .reminder
                    .find(|c: char| !c.is_whitespace())
                    .unwrap_or(self.reminder.len());

                let literal = &self.reminder[..next_non_ws];
                token!(&literal, Space(literal));
            }

            Some(_) => {
                let literal = &self.reminder[..1];
                token!(&literal, Literal(literal));
            }

            None => {}
        }

        None
    }
}

// Adapted from chrono's `scan::timezone_offset_2822`:
// https://github.com/chronotope/chrono/blob/baa55d084784e4e88b5332efe8e96af794a52e8a/src/format/scan.rs#L285-L322
fn parse_legacy_timezone(parsed: &mut Parsed, val: &str) -> ParseResult<()> {
    let upto = val
        .as_bytes()
        .iter()
        .position(|&c| !c.is_ascii_alphabetic())
        .unwrap_or(val.len());
    if upto == 0 {
        return Ok(());
    }

    let name = &val.as_bytes()[..upto];
    if name.eq_ignore_ascii_case(b"gmt") || name.eq_ignore_ascii_case(b"ut") {
        parsed.set_offset(0)
    } else if name.eq_ignore_ascii_case(b"edt") {
        parsed.set_offset(-4 * 3600)
    } else if name.eq_ignore_ascii_case(b"est") || name.eq_ignore_ascii_case(b"cdt") {
        parsed.set_offset(-5 * 3600)
    } else if name.eq_ignore_ascii_case(b"cst") || name.eq_ignore_ascii_case(b"mdt") {
        parsed.set_offset(-6 * 3600)
    } else if name.eq_ignore_ascii_case(b"mst") || name.eq_ignore_ascii_case(b"pdt") {
        parsed.set_offset(-7 * 3600)
    } else if name.eq_ignore_ascii_case(b"pst") {
        parsed.set_offset(-8 * 3600)
    } else {
        Ok(())
    }
}

// Parses a date in Go's time format like 'Mon Jan _2 15:04:05 2006'.
pub fn parse(layout: &str, value: &str) -> ParseResult<DateTime<FixedOffset>> {
    let mut items = GoTimeFormatItems::parse(layout);
    let mut parsed = Parsed::new();
    let remainder = format::parse_and_remainder(
        &mut parsed,
        value,
        items
            .by_ref()
            .take_while(|i| !matches!(i, format::Item::Fixed(Fixed::TimezoneName))),
    )?;

    // The reason for splitting parsing procedure to two part is handling legacy
    // time zone names like EDT, EST etc. They are supported by chrono but not
    // exposed to us. As a workaround, we copied chrono's implementation to
    // `parse_legacy_timezone` function and whenever we encounter a
    // `Fixed::TimezoneName` we stop parsing with our regular parser,
    // parse timezone with `parse_legacy_timezone` and then continue parsing.
    if !remainder.is_empty() {
        parse_legacy_timezone(&mut parsed, remainder)?;

        format::parse(
            &mut parsed,
            remainder,
            iter::once(format::Item::Fixed(Fixed::TimezoneName)).chain(items),
        )?;
    }

    // Go's `time.Parse` allows missing years but chrono fails to parse them,
    // we're setting year field to `0` if year field is missing.
    if parsed.year.is_none()
        && parsed.year_div_100.is_none()
        && parsed.year_mod_100.is_none()
        && parsed.isoyear.is_none()
        && parsed.isoyear_div_100.is_none()
        && parsed.isoyear_mod_100.is_none()
        && parsed.timestamp.is_none()
    {
        parsed.set_year(0)?;
    }

    // Go's `time.Parse` allows missing time (hour, minute, second) but
    // chrono fails to parse them, we're setting time to `0` if time is missing.
    if parsed.hour_div_12.is_none()
        && parsed.hour_mod_12.is_none()
        && parsed.minute.is_none()
        && parsed.second.is_none()
    {
        parsed.set_hour(0)?;
        parsed.set_minute(0)?;
        parsed.set_second(0)?;
    }

    if parsed.offset.is_some() {
        parsed.to_datetime()
    } else {
        let naive = parsed.to_naive_datetime_with_offset(0)?;
        Ok(naive.and_utc().fixed_offset())
    }
}

// Formats a date in Go's time format like 'Mon Jan _2 15:04:05 2006'.
pub fn format<Tz: TimeZone>(date: DateTime<Tz>, fmt: &str) -> String
where
    Tz::Offset: fmt::Display,
{
    date.format_with_items(GoTimeFormatItems::format(fmt))
        .to_string()
}

#[cfg(test)]
mod tests {
    use chrono::{Datelike, Month, TimeZone, Timelike, Weekday};
    use chrono_tz::PST8PDT;

    use super::*;

    #[test]
    fn parses_durations() {
        // Test cases are copied from Go's `time.ParseDuration` tests:
        // https://github.com/golang/go/blob/8db131082d08e497fd8e9383d0ff7715e1bef478/src/time/time_test.go#L891-L951

        for (input, expected_dur) in [
            // simple
            ("0", Duration::zero()),
            ("5s", Duration::try_seconds(5).unwrap()),
            ("30s", Duration::try_seconds(30).unwrap()),
            ("1478s", Duration::try_seconds(1478).unwrap()),
            // sign
            ("-5s", -Duration::try_seconds(5).unwrap()),
            ("+5s", Duration::try_seconds(5).unwrap()),
            ("-0", Duration::zero()),
            ("+0", Duration::zero()),
            // decimal
            ("5.0s", Duration::try_seconds(5).unwrap()),
            (
                "5.6s",
                Duration::try_seconds(5).unwrap() + Duration::try_milliseconds(600).unwrap(),
            ),
            ("5.s", Duration::try_seconds(5).unwrap()),
            (".5s", Duration::try_milliseconds(500).unwrap()),
            ("1.0s", Duration::try_seconds(1).unwrap()),
            ("1.00s", Duration::try_seconds(1).unwrap()),
            (
                "1.004s",
                Duration::try_seconds(1).unwrap() + Duration::try_milliseconds(4).unwrap(),
            ),
            (
                "1.0040s",
                Duration::try_seconds(1).unwrap() + Duration::try_milliseconds(4).unwrap(),
            ),
            (
                "100.00100s",
                Duration::try_seconds(100).unwrap() + Duration::try_milliseconds(1).unwrap(),
            ),
            // different units
            ("10ns", Duration::nanoseconds(10)),
            ("11us", Duration::microseconds(11)),
            ("12µs", Duration::microseconds(12)), // U+00B5
            ("12μs", Duration::microseconds(12)), // U+03BC
            ("13ms", Duration::try_milliseconds(13).unwrap()),
            ("14s", Duration::try_seconds(14).unwrap()),
            ("15m", Duration::try_minutes(15).unwrap()),
            ("16h", Duration::try_hours(16).unwrap()),
            // composite durations
            (
                "3h30m",
                Duration::try_hours(3).unwrap() + Duration::try_minutes(30).unwrap(),
            ),
            (
                "10.5s4m",
                Duration::try_minutes(4).unwrap()
                    + Duration::try_seconds(10).unwrap()
                    + Duration::try_milliseconds(500).unwrap(),
            ),
            (
                "-2m3.4s",
                -(Duration::try_minutes(2).unwrap()
                    + Duration::try_seconds(3).unwrap()
                    + Duration::try_milliseconds(400).unwrap()),
            ),
            (
                "1h2m3s4ms5us6ns",
                Duration::try_hours(1).unwrap()
                    + Duration::try_minutes(2).unwrap()
                    + Duration::try_seconds(3).unwrap()
                    + Duration::try_milliseconds(4).unwrap()
                    + Duration::microseconds(5)
                    + Duration::nanoseconds(6),
            ),
            (
                "39h9m14.425s",
                Duration::try_hours(39).unwrap()
                    + Duration::try_minutes(9).unwrap()
                    + Duration::try_seconds(14).unwrap()
                    + Duration::try_milliseconds(425).unwrap(),
            ),
            // large value
            ("52763797000ns", Duration::nanoseconds(52763797000)),
            // more than 9 digits after decimal point, see https://golang.org/issue/6617
            ("0.3333333333333333333h", Duration::try_minutes(20).unwrap()),
            // 9007199254740993 = 1<<53+1 cannot be stored precisely in a float64
            ("9007199254740993ns", Duration::nanoseconds((1 << 53) + 1)),
            // largest duration that can be represented by int64 in nanoseconds
            ("9223372036854775807ns", Duration::nanoseconds(i64::MAX)),
            ("9223372036854775.807us", Duration::nanoseconds(i64::MAX)),
            (
                "9223372036s854ms775us807ns",
                Duration::nanoseconds(i64::MAX),
            ),
            ("-9223372036854775808ns", Duration::nanoseconds(i64::MIN)),
            ("-9223372036854775.808us", Duration::nanoseconds(i64::MIN)),
            (
                "-9223372036s854ms775us808ns",
                Duration::nanoseconds(i64::MIN),
            ),
            // largest negative value
            ("-9223372036854775808ns", Duration::nanoseconds(i64::MIN)),
            // largest negative round trip value, see https://golang.org/issue/48629
            ("-2562047h47m16.854775808s", Duration::nanoseconds(i64::MIN)),
            // huge string; issue 15011.
            (
                "0.100000000000000000000h",
                Duration::try_minutes(6).unwrap(),
            ),
            // This value tests the first overflow check in leadingFraction.
            (
                "0.830103483285477580700h",
                Duration::try_minutes(49).unwrap()
                    + Duration::try_seconds(48).unwrap()
                    + Duration::nanoseconds(372539827),
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

        fn check_time(time: DateTime<FixedOffset>, test_case: &ParseTest) {
            // The time should be Thu Feb  4 21:00:57 PST 2010
            if test_case.year_sign >= 0 {
                assert_eq!(test_case.year_sign * time.year(), 2010);
            }
            assert_eq!(time.month0(), Month::February as u32);
            assert_eq!(time.day(), 4);
            assert_eq!(time.hour(), 21);
            assert_eq!(time.minute(), 0);
            assert_eq!(time.second(), 57);

            let nanosec = "012345678"[..test_case.frac_digits].to_string()
                + &"000000000"[..9 - test_case.frac_digits];
            assert_eq!(time.nanosecond(), nanosec.parse::<u32>().unwrap());

            if test_case.has_tz {
                assert_eq!(time.timezone().local_minus_utc(), -28800);
            }

            if test_case.has_wd {
                assert_eq!(time.weekday(), Weekday::Thu);
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
            println!("Test case {}", tc.name);
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
        let time = PST8PDT.timestamp_nanos(1233810057012345600);

        for tc in test_cases {
            println!("Test case {}", tc.name);
            let result = format(time, &tc.format);
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
