<!-- Copyright (c) Microsoft Corporation. All rights reserved. -->
<!-- Licensed under the MIT License. -->

# Knowledge: Time Builtins Compatibility

Deep knowledge about the time builtin functions, especially the Go
`time.Parse` compatibility layer. Read this before modifying
`src/builtins/time/` or any time-related builtins.

## Architecture

```
src/builtins/
  time.rs              Main time builtins
  time/
    compat.rs          Go time.Parse compatibility layer (largest builtin module)
    diff.rs            Time difference calculation
```

`compat.rs` is the single most complex builtin module in the codebase.

## Why Go Compatibility Matters

OPA is written in Go and uses Go's `time.Parse()` function. Go's time parsing
is fundamentally different from standard approaches:

**Standard (C, Rust, Python)**: format strings with `%Y`, `%m`, `%d` etc.

**Go**: uses a **reference time** as the layout. The reference time is:
```
Mon Jan 2 15:04:05 MST 2006
```
This specific date/time was chosen because each component is unique:
- Month: January (1)
- Day: 2
- Hour: 15 (3 PM)
- Minute: 04
- Second: 05
- Year: 2006
- Timezone: MST

OPA test cases use Go layouts, so regorus must parse and format times using
this same convention to pass conformance tests.

## The compat.rs Module

This is essentially a **Rust port of Go's time parsing logic**. Key functions:

### `parse(layout, value)` → Parsed time

Implements Go's `time.Parse()`:
1. Scans the layout string for known reference time components
2. Extracts corresponding values from the input string
3. Handles timezone parsing, AM/PM, fractional seconds
4. Returns a Chrono `DateTime` or `NaiveDateTime`

### `format(time, layout)` → Formatted string

Implements Go's `time.Format()`:
1. Scans the layout string for reference time components
2. Substitutes actual time values
3. Handles timezone abbreviation, offset formatting

### `parse_duration(s)` → Duration

Parses Go-style duration strings: `"10h12m45s"`, `"1.5h"`, `"300ms"`.
Go's duration format is different from ISO 8601.

## Tricky Aspects

### Missing Components

Go's `time.Parse` allows missing year or time components. Chrono is stricter.
The compatibility layer fills in defaults:
- Missing year → 0 (or current year depending on context)
- Missing time → 00:00:00
- Missing timezone → UTC

### Timezone Parsing

Go has a custom timezone parsing approach that differs from standard timezone
databases. The compatibility layer handles:
- Named timezones (MST, EST, PST)
- Numeric offsets (+0700, -05:00)
- Legacy formats
- `parse_legacy_timezone()` for OPA-specific timezone handling

### Fractional Seconds

Go layouts use `.000` for milliseconds, `.000000` for microseconds,
`.000000000` for nanoseconds. The number of zeros determines precision.
The parser must count zeros to know the precision.

### Lint Suppressions

`compat.rs` suppresses several lints:
- `clippy::arithmetic_side_effects` — ported Go code uses arithmetic directly
- `clippy::unseparated_literal_suffix` — literal style from Go port
- `clippy::pattern_type_mismatch`

This is intentional — the module is a faithful port and the arithmetic has
been verified in the original Go implementation.

## Main Time Builtins (`time.rs`)

| Function | Purpose | Complexity |
|----------|---------|------------|
| `time.now_ns()` | Current time in nanoseconds | Low |
| `time.parse_rfc3339_ns()` | Parse RFC 3339 timestamp | Low |
| `time.parse_ns()` | Parse with Go layout → nanoseconds | High (uses compat.rs) |
| `time.parse_duration_ns()` | Parse Go duration string | Medium |
| `time.format()` | Format with Go layout | High (uses compat.rs) |
| `time.date()` | Extract year/month/day | Medium |
| `time.clock()` | Extract hour/minute/second | Medium |
| `time.weekday()` | Day of week string | Low |
| `time.add_date()` | Date arithmetic | Medium |
| `time.diff()` | Time difference | Medium |

### Date Arithmetic

`time.add_date()` uses checked arithmetic:
- `checked_add()` and `checked_sub_months()` for year/month bounds
- Leap year adjustments
- Returns `Undefined` on overflow (OPA compatibility)

### Nanosecond Precision

All time functions work with nanosecond timestamps internally.
`safe_timestamp_nanos()` prevents overflow when converting from seconds
to nanoseconds.

### Predefined Format Layouts

`layout_with_predefined_formats()` maps OPA layout names to Chrono formats:
- RFC 3339, RFC 822, RFC 850
- ANSIC, Unix, Kitchen, Stamp formats
- These must match OPA's predefined layouts exactly

## OPA Conformance

Time builtins are a rich source of conformance edge cases:

1. **Go layout parsing** must match Go's behavior exactly
2. **Nanosecond overflow** must return `Undefined`, not error
3. **Timezone names** must be recognized consistently
4. **Duration parsing** must handle Go's format (not ISO 8601)
5. **Date arithmetic** edge cases (Feb 29, month overflow)

## Dependencies

- `chrono` — date/time handling (feature-gated behind `time`)
- `chrono-tz` — timezone database (feature-gated behind `time`)

Both are optional dependencies. Time builtins are not available in `no_std`
or `opa-no-std` configurations.
