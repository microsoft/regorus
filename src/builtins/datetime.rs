// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::String;
use anyhow::{bail, Result};
use jiff::{fmt::strtime, tz::Offset, SignedDuration, ZonedDateTime};

pub fn parse_rfc3339(value: &str) -> Result<ZonedDateTime> {
    let bytes = value.as_bytes();
    if bytes.len() < 20
        || bytes.get(4) != Some(&b'-')
        || bytes.get(7) != Some(&b'-')
        || bytes.get(13) != Some(&b':')
        || bytes.get(16) != Some(&b':')
        || bytes
            .iter()
            .take(19)
            .enumerate()
            .any(|(index, byte)| !matches!(index, 4 | 7 | 10 | 13 | 16) && !byte.is_ascii_digit())
    {
        bail!("invalid RFC3339 datetime");
    }
    let separator = match value.as_bytes().get(10).copied() {
        Some(b'T') => "T",
        Some(b't') => "t",
        Some(b' ') => " ",
        _ => bail!("invalid RFC3339 datetime separator"),
    };
    let zulu = value.ends_with(['Z', 'z']);
    let suffix = if zulu {
        value
            .get(value.len().saturating_sub(1)..)
            .ok_or_else(|| anyhow::anyhow!("invalid RFC3339 datetime"))?
    } else {
        let offset = value
            .get(value.len().saturating_sub(6)..)
            .ok_or_else(|| anyhow::anyhow!("missing RFC3339 offset"))?;
        if !offset.starts_with(['+', '-']) || offset.as_bytes().get(3) != Some(&b':') {
            bail!("invalid RFC3339 offset");
        }
        "%:z"
    };
    let mut parsed =
        strtime::BrokenDownTime::parse(format!("%Y-%m-%d{separator}%H:%M:%S%.f{suffix}"), value)?;
    if zulu {
        parsed.set_offset(Some(Offset::ZERO));
    }
    if parsed
        .offset()
        .is_some_and(|offset| offset.seconds().unsigned_abs() >= 86400)
    {
        bail!("invalid RFC3339 offset");
    }
    let datetime = parsed.to_zoned_datetime()?;
    // Jiff clamps leap seconds to 59. Preserve their legacy epoch value.
    if value.get(17..19) == Some("60") {
        Ok(datetime.checked_add(SignedDuration::from_secs(1))?)
    } else {
        Ok(datetime)
    }
}

pub fn format_rfc3339(datetime: &ZonedDateTime, zulu: bool) -> Result<String> {
    let precision = fractional_precision(datetime.subsec_nanosecond());
    let suffix = if zulu && datetime.offset() == Offset::ZERO {
        "Z"
    } else {
        "%:z"
    };
    let fraction = if precision == 0 {
        String::new()
    } else {
        format!("%.{precision}f")
    };
    Ok(strtime::format(
        format!("%Y-%m-%dT%H:%M:%S{fraction}{suffix}"),
        datetime,
    )?)
}

pub const fn fractional_precision(nanos: i32) -> usize {
    if nanos == 0 {
        0
    } else if nanos % 1_000_000 == 0 {
        3
    } else if nanos % 1_000 == 0 {
        6
    } else {
        9
    }
}

#[cfg(test)]
mod tests {
    use super::parse_rfc3339;

    #[test]
    #[allow(clippy::unwrap_used)]
    fn rejects_non_rfc3339_temporal_syntax() {
        for value in [
            "2024-01-01T00:00:00+00:00[UTC]",
            "2024-01-01T00:00Z",
            "2024-1-01T00:00:00Z",
            "2024-01-01T00:00:00+0000",
            "2024-01-01T00:00:00+24:00",
        ] {
            parse_rfc3339(value).unwrap_err();
        }
    }
}
