// Copyright (c) Microsoft Corporation.
// Licensed under the MIT and Apache 2.0 License.

use anyhow::{anyhow, Result};
use chrono::{DateTime, Datelike, FixedOffset, TimeZone, Timelike, Utc};

// Adapted from the official Go implementation:
// https://github.com/open-policy-agent/opa/blob/eb17a716b97720a27c6569395ba7c4b7409aae87/topdown/time.go#L179-L243
pub fn diff_between_datetimes(
    datetime1: DateTime<FixedOffset>,
    datetime2: DateTime<FixedOffset>,
) -> Result<(i32, i32, i32, i32, i32, i32)> {
    // The following implementation of this function is taken
    // from https://github.com/icza/gox licensed under Apache 2.0.
    // The only modification made is to variable names.
    //
    // For details, see https://stackoverflow.com/a/36531443/1705598
    //
    // Copyright 2021 icza
    // BEGIN REDISTRIBUTION FROM APACHE 2.0 LICENSED PROJECT

    // Make sure both datetimes in the same timezone
    let datetime2 = datetime2.with_timezone(&datetime1.timezone());

    // Make sure `datetime1` is always the smallest one
    let (datetime1, datetime2) = if datetime1 > datetime2 {
        (datetime2, datetime1)
    } else {
        (datetime1, datetime2)
    };

    let mut year = datetime2.year() - datetime1.year();
    let mut month = datetime2.month() as i32 - datetime1.month() as i32;
    let mut day = datetime2.day() as i32 - datetime1.day() as i32;
    let mut hour = datetime2.hour() as i32 - datetime1.hour() as i32;
    let mut min = datetime2.minute() as i32 - datetime1.minute() as i32;
    let mut sec = datetime2.second() as i32 - datetime1.second() as i32;

    // Normalize negative values
    if sec < 0 {
        sec += 60;
        min -= 1;
    }
    if min < 0 {
        min += 60;
        hour -= 1;
    }
    if hour < 0 {
        hour += 24;
        day -= 1;
    }
    if day < 0 {
        // Days in month:
        let t = Utc
            .with_ymd_and_hms(datetime1.year(), datetime1.month(), 32, 0, 0, 0)
            .single()
            .ok_or(anyhow!("Could not convert `ns1` to datetime"))?;
        day += 32 - t.day() as i32;
        month -= 1;
    }
    if month < 0 {
        month += 12;
        year -= 1;
    }

    // END REDISTRIBUTION FROM APACHE 2.0 LICENSED PROJECT

    Ok((year, month, day, hour, min, sec))
}
