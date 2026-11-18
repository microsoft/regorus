// Copyright (c) Microsoft Corporation.
// Licensed under the MIT and Apache 2.0 License.
#![allow(clippy::as_conversions, clippy::unused_trait_names)]
use anyhow::Result;
use jiff::ZonedDateTime;

// Adapted from the official Go implementation:
// https://github.com/open-policy-agent/opa/blob/eb17a716b97720a27c6569395ba7c4b7409aae87/topdown/time.go#L179-L243
pub fn diff_between_datetimes(
    datetime1: ZonedDateTime,
    datetime2: ZonedDateTime,
) -> Result<(i32, i32, i32, i32, i32, i32)> {
    // The following implementation of this function is taken
    // from https://github.com/icza/gox licensed under Apache 2.0.
    //
    // For details, see https://stackoverflow.com/a/36531443/1705598
    //
    // Copyright 2021 icza
    // BEGIN REDISTRIBUTION FROM APACHE 2.0 LICENSED PROJECT

    // Make sure both datetimes in the same timezone
    let datetime2 = datetime2.with_time_zone(datetime1.time_zone().clone());

    // Make sure `datetime1` is always the smallest one
    let (datetime1, datetime2) = if datetime1 > datetime2 {
        (datetime2, datetime1)
    } else {
        (datetime1, datetime2)
    };

    let mut year = i32::from(datetime2.year()) - i32::from(datetime1.year());
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
        let days_in_month = datetime1.days_in_month();
        day += days_in_month as i32;
        month -= 1;
    }
    if month < 0 {
        month += 12;
        year -= 1;
    }

    // END REDISTRIBUTION FROM APACHE 2.0 LICENSED PROJECT

    Ok((year, month, day, hour, min, sec))
}
