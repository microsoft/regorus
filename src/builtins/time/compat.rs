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

use chrono::Duration;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_durations() {
        // Test cases are copied from Go's `time.ParseDuration` tests:
        // https://github.com/golang/go/blob/8db131082d08e497fd8e9383d0ff7715e1bef478/src/time/time_test.go#L891-L951

        for (input, expected_dur) in [
            // simple
            ("0", Duration::zero()),
            ("5s", Duration::seconds(5)),
            ("30s", Duration::seconds(30)),
            ("1478s", Duration::seconds(1478)),
            // sign
            ("-5s", -Duration::seconds(5)),
            ("+5s", Duration::seconds(5)),
            ("-0", Duration::zero()),
            ("+0", Duration::zero()),
            // decimal
            ("5.0s", Duration::seconds(5)),
            ("5.6s", Duration::seconds(5) + Duration::milliseconds(600)),
            ("5.s", Duration::seconds(5)),
            (".5s", Duration::milliseconds(500)),
            ("1.0s", Duration::seconds(1)),
            ("1.00s", Duration::seconds(1)),
            ("1.004s", Duration::seconds(1) + Duration::milliseconds(4)),
            ("1.0040s", Duration::seconds(1) + Duration::milliseconds(4)),
            (
                "100.00100s",
                Duration::seconds(100) + Duration::milliseconds(1),
            ),
            // different units
            ("10ns", Duration::nanoseconds(10)),
            ("11us", Duration::microseconds(11)),
            ("12µs", Duration::microseconds(12)), // U+00B5
            ("12μs", Duration::microseconds(12)), // U+03BC
            ("13ms", Duration::milliseconds(13)),
            ("14s", Duration::seconds(14)),
            ("15m", Duration::minutes(15)),
            ("16h", Duration::hours(16)),
            // composite durations
            ("3h30m", Duration::hours(3) + Duration::minutes(30)),
            (
                "10.5s4m",
                Duration::minutes(4) + Duration::seconds(10) + Duration::milliseconds(500),
            ),
            (
                "-2m3.4s",
                -(Duration::minutes(2) + Duration::seconds(3) + Duration::milliseconds(400)),
            ),
            (
                "1h2m3s4ms5us6ns",
                Duration::hours(1)
                    + Duration::minutes(2)
                    + Duration::seconds(3)
                    + Duration::milliseconds(4)
                    + Duration::microseconds(5)
                    + Duration::nanoseconds(6),
            ),
            (
                "39h9m14.425s",
                Duration::hours(39)
                    + Duration::minutes(9)
                    + Duration::seconds(14)
                    + Duration::milliseconds(425),
            ),
            // large value
            ("52763797000ns", Duration::nanoseconds(52763797000)),
            // more than 9 digits after decimal point, see https://golang.org/issue/6617
            ("0.3333333333333333333h", Duration::minutes(20)),
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
            ("0.100000000000000000000h", Duration::minutes(6)),
            // This value tests the first overflow check in leadingFraction.
            (
                "0.830103483285477580700h",
                Duration::minutes(49) + Duration::seconds(48) + Duration::nanoseconds(372539827),
            ),
        ] {
            let dur = parse_duration(input).unwrap();
            assert_eq!(dur, expected_dur);
        }
    }
}
