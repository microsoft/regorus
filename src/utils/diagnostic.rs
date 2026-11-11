// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::fmt;

pub struct Diagnostic<'a>(fmt::Arguments<'a>);

pub const fn bounded(args: fmt::Arguments<'_>) -> Diagnostic<'_> {
    Diagnostic(args)
}

impl fmt::Display for Diagnostic<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut writer = DiagnosticWriter {
            output: f,
            remaining: 256,
            truncated: false,
        };
        match fmt::write(&mut writer, self.0) {
            Ok(()) => Ok(()),
            Err(_) if writer.truncated => writer.output.write_str("..."),
            Err(error) => Err(error),
        }
    }
}

struct DiagnosticWriter<'a, 'b> {
    output: &'a mut fmt::Formatter<'b>,
    remaining: usize,
    truncated: bool,
}

impl fmt::Write for DiagnosticWriter<'_, '_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        let mut end = text.len().min(self.remaining);
        while !text.is_char_boundary(end) {
            end = end.saturating_sub(1);
        }
        let prefix = text.get(..end).ok_or(fmt::Error)?;
        self.output.write_str(prefix)?;
        self.remaining = self.remaining.saturating_sub(end);
        if end < text.len() {
            self.truncated = true;
            // Stop the producer too: truncating an already formatted String is too late.
            Err(fmt::Error)
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;
    use core::cell::Cell;

    #[test]
    fn bounds_utf8_and_stops_formatting_at_the_limit() {
        struct Producer<'a>(&'a Cell<usize>);
        impl fmt::Display for Producer<'_> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                for _ in 0..10_000 {
                    self.0.set(self.0.get().saturating_add(1));
                    f.write_str("\u{20ac}")?;
                }
                Ok(())
            }
        }

        let writes = Cell::new(0);
        let text = format!("{}", bounded(format_args!("{}", Producer(&writes))));
        assert_eq!(text, format!("{}...", "\u{20ac}".repeat(85)));
        assert_eq!(writes.get(), 86);
        assert_eq!(format!("{}", bounded(format_args!("short"))), "short");
    }
}
