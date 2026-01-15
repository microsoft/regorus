// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// SAFETY: Arithmetic operations in this module are safe by design:
// 1. MAX_COL=1024 prevents column counter overflow (enforced by advance_col)
// 2. File size is capped by MAX_FILE_BYTES at load time
// 3. Total line count is capped by MAX_LINES at load time
// 4. State-modifying operations (advance_col/advance_line) use checked arithmetic
// 5. Remaining arithmetic is for bounded calculations (spans, error reporting)
//    where operands are constrained by MAX_COL and file size/line limits
// 6. Defensive saturating_sub used for subtractions that could theoretically underflow
use crate::*;
use core::cmp;
use core::fmt::{self, Debug, Formatter};
use core::iter::Peekable;
use core::ops::Range;
use core::str::CharIndices;

use crate::Value;

use anyhow::{anyhow, bail, Result};

#[inline]
fn check_memory_limit() -> Result<()> {
    crate::utils::limits::check_memory_limit_if_needed().map_err(|err| anyhow!(err))
}

// Maximum column width to prevent overflow and catch pathological input.
// Lines exceeding this are likely minified/generated code or attack attempts.
const MAX_COL: u32 = 1024;
// Maximum allowed policy file size in bytes (1 MiB) to reject pathological inputs early.
const MAX_FILE_BYTES: usize = 1_048_576;
// Maximum allowed number of lines to avoid pathological or minified inputs.
const MAX_LINES: usize = 20_000;

#[inline]
fn usize_to_u32(value: usize) -> Result<u32> {
    u32::try_from(value).map_err(|_| anyhow!("value exceeds u32::MAX"))
}

#[inline]
fn span_range(start: u32, end: u32) -> Option<Range<usize>> {
    let s = usize::try_from(start).ok()?;
    let e = usize::try_from(end).ok()?;
    Some(s..e)
}

#[derive(Clone)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
struct SourceInternal {
    pub file: String,
    pub contents: String,
    #[cfg_attr(feature = "ast", serde(skip_serializing))]
    pub lines: Vec<(u32, u32)>,
}

/// A policy file.
#[derive(Clone)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct Source {
    #[cfg_attr(feature = "ast", serde(flatten))]
    src: Rc<SourceInternal>,
}

impl Source {
    /// The path associated with the policy file.
    pub fn get_path(&self) -> &String {
        &self.src.file
    }

    /// The contents of the policy file.
    pub fn get_contents(&self) -> &String {
        &self.src.contents
    }
}

impl cmp::Ord for Source {
    fn cmp(&self, other: &Source) -> cmp::Ordering {
        Rc::as_ptr(&self.src).cmp(&Rc::as_ptr(&other.src))
    }
}

impl cmp::PartialOrd for Source {
    fn partial_cmp(&self, other: &Source) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::PartialEq for Source {
    fn eq(&self, other: &Source) -> bool {
        Rc::as_ptr(&self.src) == Rc::as_ptr(&other.src)
    }
}

impl cmp::Eq for Source {}

#[cfg(feature = "std")]
impl core::hash::Hash for Source {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.src).hash(state);
    }
}

impl Debug for Source {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        self.src.file.fmt(f)
    }
}

#[derive(Clone)]
pub struct SourceStr {
    source: Source,
    start: u32,
    end: u32,
}

impl Debug for SourceStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        self.text().fmt(f)
    }
}

impl fmt::Display for SourceStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(&self.text(), f)
    }
}

impl SourceStr {
    pub const fn new(source: Source, start: u32, end: u32) -> Self {
        Self { source, start, end }
    }

    pub fn text(&self) -> &str {
        // Use safe slicing to avoid panics on malformed spans
        span_range(self.start, self.end).map_or("<invalid-span>", |range| {
            self.source
                .contents()
                .get(range)
                .unwrap_or("<invalid-span>")
        })
    }

    pub fn clone_empty(&self) -> SourceStr {
        Self {
            source: self.source.clone(),
            start: 0,
            end: 0,
        }
    }
}

impl cmp::PartialEq for SourceStr {
    fn eq(&self, other: &Self) -> bool {
        self.text().eq(other.text())
    }
}

impl cmp::Eq for SourceStr {}

impl cmp::PartialOrd for SourceStr {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl cmp::Ord for SourceStr {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.text().cmp(other.text())
    }
}

impl Source {
    pub fn from_contents(file: String, contents: String) -> Result<Source> {
        if contents.len() > MAX_FILE_BYTES {
            bail!("{file} exceeds maximum allowed policy file size {MAX_FILE_BYTES} bytes");
        }
        let mut lines = vec![];
        let mut prev_ch = ' ';
        let mut prev_pos = 0_u32;
        let mut start = 0_u32;
        for (i, ch) in contents.char_indices() {
            let i_u32 = usize_to_u32(i)?;
            if ch == '\n' {
                let end = match prev_ch {
                    '\r' => prev_pos,
                    _ => i_u32,
                };
                if lines.len() >= MAX_LINES {
                    bail!("{file} exceeds maximum allowed line count {MAX_LINES}");
                }
                lines.push((start, end));
                // Enforce the current global memory cap after recording each line span.
                check_memory_limit()?;
                start = i_u32.saturating_add(1);
            }
            prev_ch = ch;
            prev_pos = i_u32;
        }

        let start_usize = usize::try_from(start).unwrap_or(usize::MAX);
        if start_usize < contents.len() {
            if lines.len() >= MAX_LINES {
                bail!("{file} exceeds maximum allowed line count {MAX_LINES}");
            }
            lines.push((start, usize_to_u32(contents.len())?));
            // Enforce the global limit after appending the final line span.
            check_memory_limit()?;
        } else if contents.is_empty() {
            lines.push((0, 0));
            // Enforce the global limit even for empty sources.
            check_memory_limit()?;
        } else {
            let s = usize_to_u32(contents.len().saturating_sub(1))?;
            if lines.len() >= MAX_LINES {
                bail!("{file} exceeds maximum allowed line count {MAX_LINES}");
            }
            lines.push((s, s));
            // Enforce the global limit after storing the trailing span.
            check_memory_limit()?;
        }
        Ok(Self {
            src: Rc::new(SourceInternal {
                file,
                contents,
                lines,
            }),
        })
    }

    #[cfg(feature = "std")]
    pub fn from_file<P: AsRef<std::path::Path>>(path: P) -> Result<Source> {
        let contents = match std::fs::read_to_string(&path) {
            Ok(c) => c,
            Err(e) => bail!("Failed to read {}. {e}", path.as_ref().display()),
        };
        // TODO: retain path instead of converting to string
        Self::from_contents(path.as_ref().to_string_lossy().to_string(), contents)
    }

    pub fn file(&self) -> &String {
        &self.src.file
    }
    pub fn contents(&self) -> &String {
        &self.src.contents
    }
    pub fn line(&self, idx: u32) -> &str {
        let idx = usize::try_from(idx).unwrap_or(usize::MAX);
        match self.src.lines.get(idx) {
            Some(&(start, end)) => self
                .src
                .contents
                .get(span_range(start, end).unwrap_or(0..0))
                .unwrap_or(""),
            None => "",
        }
    }

    pub fn message(&self, line: u32, col: u32, kind: &str, msg: &str) -> String {
        if usize::try_from(line).unwrap_or(usize::MAX) > self.src.lines.len() {
            return format!("{}: invalid line {} specified", self.src.file, line);
        }

        let line_str = format!("{line}");
        let line_num_width = line_str.len().saturating_add(1);
        let col_spaces = usize::try_from(col).unwrap_or(0).saturating_sub(1);

        format!(
            "\n--> {}:{}:{}\n{:<line_num_width$}|\n\
		{:<line_num_width$}| {}\n\
		{:<line_num_width$}| {:<col_spaces$}^\n\
		{}: {}",
            self.src.file,
            line,
            col,
            "",
            line,
            self.line(line.saturating_sub(1)),
            "",
            "",
            kind,
            msg
        )
    }

    pub fn error(&self, line: u32, col: u32, msg: &str) -> anyhow::Error {
        anyhow!(self.message(line, col, "error", msg))
    }
}

#[derive(Clone)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct Span {
    #[cfg_attr(feature = "ast", serde(skip_serializing))]
    pub source: Source,
    pub line: u32,
    pub col: u32,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn text(&self) -> &str {
        // Use safe slicing to avoid panics on malformed spans
        span_range(self.start, self.end).map_or("<invalid-span>", |range| {
            self.source
                .contents()
                .get(range)
                .unwrap_or("<invalid-span>")
        })
    }

    pub fn source_str(&self) -> SourceStr {
        SourceStr::new(self.source.clone(), self.start, self.end)
    }

    pub fn message(&self, kind: &str, msg: &str) -> String {
        self.source.message(self.line, self.col, kind, msg)
    }

    pub fn error(&self, msg: &str) -> anyhow::Error {
        self.source.error(self.line, self.col, msg)
    }
}

impl Debug for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), fmt::Error> {
        let t = self.text().escape_debug().to_string();
        let max = 32;
        let (txt, trailer) = if t.len() > max {
            (&t[0..max], "...")
        } else {
            (t.as_str(), "")
        };

        f.write_fmt(format_args!(
            "{}:{}:{}:{}, \"{}{}\"",
            self.line, self.col, self.start, self.end, txt, trailer
        ))
    }
}

#[cfg(feature = "azure-rbac")]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AzureRbacTokenKind {
    At,         // @ symbol for attribute sources (@Request, @Resource, etc.)
    LogicalAnd, // && operator
    LogicalOr,  // || operator
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind {
    Symbol,
    String,
    RawString,
    Number,
    Ident,
    Eof,
    // Azure RBAC-specific tokens
    #[cfg(feature = "azure-rbac")]
    AzureRbac(AzureRbacTokenKind),
}

#[derive(Debug, Clone)]
pub struct Token(pub TokenKind, pub Span);

#[derive(Clone)]
pub struct Lexer<'source> {
    source: Source,
    iter: Peekable<CharIndices<'source>>,
    line: u32,
    col: u32,
    unknown_char_is_symbol: bool,
    allow_slash_star_escape: bool,
    comment_starts_with_double_slash: bool,
    double_colon_token: bool,
    #[cfg(feature = "azure-rbac")]
    enable_rbac_tokens: bool,
    #[cfg(feature = "azure-rbac")]
    allow_single_quoted_strings: bool,
}

impl<'source> fmt::Debug for Lexer<'source> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lexer").finish_non_exhaustive()
    }
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source Source) -> Self {
        Self {
            source: source.clone(),
            iter: source.contents().char_indices().peekable(),
            line: 1,
            col: 1,
            unknown_char_is_symbol: false,
            allow_slash_star_escape: false,
            comment_starts_with_double_slash: false,
            double_colon_token: false,
            #[cfg(feature = "azure-rbac")]
            enable_rbac_tokens: false,
            #[cfg(feature = "azure-rbac")]
            allow_single_quoted_strings: false,
        }
    }

    pub const fn set_unknown_char_is_symbol(&mut self, b: bool) {
        self.unknown_char_is_symbol = b;
    }

    pub const fn set_allow_slash_star_escape(&mut self, b: bool) {
        self.allow_slash_star_escape = b;
    }

    pub const fn set_comment_starts_with_double_slash(&mut self, b: bool) {
        self.comment_starts_with_double_slash = b;
    }

    pub const fn set_double_colon_token(&mut self, b: bool) {
        self.double_colon_token = b;
    }

    #[cfg(feature = "azure-rbac")]
    pub const fn set_enable_rbac_tokens(&mut self, b: bool) {
        self.enable_rbac_tokens = b;
    }

    #[cfg(feature = "azure-rbac")]
    pub const fn set_allow_single_quoted_strings(&mut self, b: bool) {
        self.allow_single_quoted_strings = b;
    }

    fn peek(&mut self) -> (usize, char) {
        match self.iter.peek() {
            Some(&(index, chr)) => (index, chr),
            _ => (self.source.contents().len(), '\x00'),
        }
    }

    #[inline]
    fn advance_col(&mut self, delta: u32) -> Result<()> {
        let new_col = self
            .col
            .checked_add(delta)
            .filter(|&c| c <= MAX_COL)
            .ok_or_else(|| {
                self.source.error(
                    self.line,
                    self.col,
                    &format!("line exceeds maximum column width of {MAX_COL}"),
                )
            })?;
        self.col = new_col;
        Ok(())
    }

    #[inline]
    fn advance_line(&mut self, delta: u32) -> Result<()> {
        self.line = self.line.checked_add(delta).ok_or_else(|| {
            self.source
                .error(self.line, self.col, "line number overflow")
        })?;
        Ok(())
    }

    fn peekahead(&mut self, n: usize) -> (usize, char) {
        match self.iter.clone().nth(n) {
            Some((index, chr)) => (index, chr),
            _ => (self.source.contents().len(), '\x00'),
        }
    }

    fn read_ident(&mut self) -> Result<Token> {
        let start = self.peek().0;
        let col = self.col;
        loop {
            let ch = self.peek().1;
            if ch.is_ascii_alphanumeric() || ch == '_' {
                self.iter.next();
            } else {
                break;
            }
        }
        let end = self.peek().0;
        self.advance_col(usize_to_u32(end.saturating_sub(start))?)?;
        Ok(Token(
            TokenKind::Ident,
            Span {
                source: self.source.clone(),
                line: self.line,
                col,
                start: usize_to_u32(start)?,
                end: usize_to_u32(end)?,
            },
        ))
    }

    fn read_digits(&mut self) {
        while self.peek().1.is_ascii_digit() {
            self.iter.next();
        }
    }

    // See https://www.json.org/json-en.html for number's grammar
    fn read_number(&mut self) -> Result<Token> {
        let (start, chr) = self.peek();
        let col = self.col;
        self.iter.next();

        // Read integer part.
        if chr != '0' {
            // Starts with 1.. or 9. Read digits.
            self.read_digits();
        }

        // Read fraction part
        // . must be followed by at least 1 digit.
        if self.peek().1 == '.' && self.peekahead(1).1.is_ascii_digit() {
            self.iter.next(); // .
            self.read_digits();
        }

        // Read exponent part
        let exp_ch = self.peek().1;
        if exp_ch == 'e' || exp_ch == 'E' {
            self.iter.next();
            // e must be followed by an optional sign and digits
            if matches!(self.peek().1, '+' | '-') {
                self.iter.next();
            }
            // Read digits. Absence of digit will be validated by serde later.
            self.read_digits();
        }

        let end = self.peek().0;
        self.advance_col(usize_to_u32(end.saturating_sub(start))?)?;

        // Check for invalid number.Valid number cannot be followed by
        // these characters:
        let trailing_ch = self.peek().1;
        if trailing_ch == '_' || trailing_ch == '.' || trailing_ch.is_ascii_alphanumeric() {
            return Err(self.source.error(self.line, self.col, "invalid number"));
        }

        // Ensure that the number is parsable in Rust.
        let num_slice = self
            .source
            .contents()
            .get(start..end)
            .ok_or_else(|| self.source.error(self.line, col, "invalid number span"))?;

        let parsed_number = match serde_json::from_str::<Value>(num_slice) {
            Ok(value) => value,
            Err(e) => {
                let serde_msg = &e.to_string();
                let msg = match &serde_msg {
                    m if m.contains("out of range") => "out of range",
                    m if m.contains("invalid number") => "invalid number",
                    m if m.contains("expected value") => "expected value",
                    m if m.contains("trailing characters") => "trailing characters",
                    m => m.to_owned(),
                };

                bail!(
                    "{} {}",
                    self.source.error(
                        self.line,
                        col,
                        "invalid number. serde_json cannot parse number:"
                    ),
                    msg
                )
            }
        };

        // Enforce the global memory limit after serde allocates the temporary Value.
        check_memory_limit()?;
        drop(parsed_number);

        Ok(Token(
            TokenKind::Number,
            Span {
                source: self.source.clone(),
                line: self.line,
                col,
                start: usize_to_u32(start)?,
                end: usize_to_u32(end)?,
            },
        ))
    }

    fn read_raw_string(&mut self) -> Result<Token> {
        self.iter.next();
        self.advance_col(1)?;
        let (start, _) = self.peek();
        let (line, col) = (self.line, self.col);
        loop {
            let (_, ch) = self.peek();
            self.iter.next();
            match ch {
                '`' => {
                    self.advance_col(1)?;
                    break;
                }
                '\x00' => {
                    return Err(self.source.error(line, col, "unmatched `"));
                }
                '\t' => self.advance_col(4)?,
                '\n' => {
                    self.advance_line(1)?;
                    self.col = 1;
                }
                _ => self.advance_col(1)?,
            }
        }
        let end = self.peek().0;
        if end <= start {
            // Guard against invalid span that would underflow end - 1
            return Err(self.source.error(line, col, "invalid raw string span"));
        }
        check_memory_limit()?;
        Ok(Token(
            TokenKind::RawString,
            Span {
                source: self.source.clone(),
                line,
                col,
                start: usize_to_u32(start)?,
                end: usize_to_u32(end)?.saturating_sub(1),
            },
        ))
    }

    fn read_string(&mut self) -> Result<Token> {
        let (line, col) = (self.line, self.col);
        self.iter.next();
        self.advance_col(1)?;
        let (start, _) = self.peek();
        loop {
            let (offset, ch) = self.peek();
            match ch {
                '"' | '\x00' => {
                    break;
                }
                '\\' => {
                    self.iter.next();
                    let (_, escape_ch) = self.peek();
                    self.iter.next();
                    match escape_ch {
                        // json escape sequence
                        '"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' => (),
                        '*' if self.allow_slash_star_escape => (),
                        'u' => {
                            for _i in 0..4 {
                                let (hex_offset, hex_ch) = self.peek();
                                let rel = usize_to_u32(hex_offset.saturating_sub(start))?;
                                let cursor_col = self.col.saturating_add(rel);
                                if !hex_ch.is_ascii_hexdigit() {
                                    return Err(self.source.error(
                                        line,
                                        cursor_col,
                                        "invalid hex escape sequence",
                                    ));
                                }
                                self.iter.next();
                            }
                        }
                        _ => {
                            let cursor_col = self
                                .col
                                .saturating_add(usize_to_u32(offset.saturating_sub(start))?);
                            return Err(self.source.error(
                                line,
                                cursor_col,
                                "invalid escape sequence",
                            ));
                        }
                    }
                }
                _ => {
                    // check for valid json chars
                    let cursor_col = self
                        .col
                        .saturating_add(usize_to_u32(offset.saturating_sub(start))?);
                    if !('\u{0020}'..='\u{10FFFF}').contains(&ch) {
                        return Err(self.source.error(
                            line,
                            cursor_col,
                            "invalid character in string",
                        ));
                    }
                    self.iter.next();
                }
            }
        }

        if self.peek().1 != '"' {
            return Err(self.source.error(line, col, "unmatched \""));
        }

        self.iter.next();
        let end = self.peek().0;
        self.advance_col(usize_to_u32(end.saturating_sub(start))?)?;

        if start == 0 || end <= start {
            // Reject invalid spans before slicing/serde to avoid panic
            return Err(self.source.error(line, col, "invalid string span"));
        }

        let str_slice = self
            .source
            .contents()
            .get(start.saturating_sub(1)..end)
            .ok_or_else(|| self.source.error(line, col, "invalid string span"))?;

        // Ensure that the string is parsable in Rust.
        match serde_json::from_str::<String>(str_slice) {
            Ok(_) => (),
            Err(e) => {
                let serde_msg = &e.to_string();
                let msg = serde_msg;
                bail!(
                    "{} {}",
                    self.source
                        .error(self.line, col, "serde_json cannot parse string:"),
                    msg
                )
            }
        }

        check_memory_limit()?;

        Ok(Token(
            TokenKind::String,
            Span {
                source: self.source.clone(),
                line,
                col: col.saturating_add(1),
                start: usize_to_u32(start)?,
                end: usize_to_u32(end)?.saturating_sub(1),
            },
        ))
    }

    #[cfg(feature = "azure-rbac")]
    fn read_single_quoted_string(&mut self) -> Result<Token> {
        let (line, col) = (self.line, self.col);
        self.iter.next();
        self.advance_col(1)?;
        let (start, _) = self.peek();
        loop {
            let (offset, ch) = self.peek();
            let cursor_col = self
                .col
                .saturating_add(usize_to_u32(offset.saturating_sub(start))?);
            match ch {
                '\'' | '\x00' => {
                    break;
                }
                '\\' => {
                    self.iter.next();
                    let (_, escape_ch) = self.peek();
                    self.iter.next();
                    match escape_ch {
                        // Basic escape sequences for single-quoted strings
                        '\'' | '\\' | 'n' | 'r' | 't' => (),
                        _ => {
                            return Err(self.source.error(
                                line,
                                cursor_col,
                                "invalid escape sequence",
                            ))
                        }
                    }
                }
                _ => {
                    // check for valid chars
                    let inner_cursor_col = self
                        .col
                        .saturating_add(usize_to_u32(offset.saturating_sub(start))?);
                    if !('\u{0020}'..='\u{10FFFF}').contains(&ch) {
                        return Err(self.source.error(
                            line,
                            inner_cursor_col,
                            "invalid character in string",
                        ));
                    }
                    self.iter.next();
                }
            }
        }

        if self.peek().1 != '\'' {
            return Err(self.source.error(line, col, "unmatched '"));
        }

        self.iter.next();
        let end = self.peek().0;
        self.advance_col(usize_to_u32(end.saturating_sub(start))?)?;

        check_memory_limit()?;

        Ok(Token(
            TokenKind::String,
            Span {
                source: self.source.clone(),
                line,
                col: col.saturating_add(1),
                start: usize_to_u32(start)?,
                end: usize_to_u32(end)?.saturating_sub(1),
            },
        ))
    }

    #[inline]
    fn skip_past_newline(&mut self) -> Result<()> {
        self.iter.next();
        loop {
            match self.peek().1 {
                '\n' | '\x00' => break,
                _ => self.iter.next(),
            };
        }
        Ok(())
    }

    fn skip_ws(&mut self) -> Result<()> {
        // Only the 4 json whitespace characters are recognized.
        // https://www.crockford.com/mckeeman.html.
        // Additionally, comments are also skipped.
        // A tab is considered 4 space characters.
        loop {
            match self.peek().1 {
                ' ' => self.advance_col(1)?,
                '\t' => self.advance_col(4)?,
                '\r' => {
                    if self.peekahead(1).1 != '\n' {
                        return Err(self.source.error(
                            self.line,
                            self.col,
                            "\\r must be followed by \\n",
                        ));
                    }
                }
                '\n' => {
                    self.col = 1;
                    self.advance_line(1)?;
                }
                '#' if !self.comment_starts_with_double_slash => {
                    self.skip_past_newline()?;
                    continue;
                }
                '/' if self.comment_starts_with_double_slash && self.peekahead(1).1 == '/' => {
                    self.skip_past_newline()?;
                    continue;
                }
                _ => break,
            }
            self.iter.next();
        }
        Ok(())
    }

    pub fn next_token(&mut self) -> Result<Token> {
        self.skip_ws()?;

        let (start, chr) = self.peek();
        let start_u32 = usize_to_u32(start)?;
        let col = self.col;

        let token = match chr {
            // Special case for - followed by digit which is a
            // negative json number.
            // . followed by digit is invalid number.
            '-' | '.' if self.peekahead(1).1.is_ascii_digit() => self.read_number()?,
            // grouping characters
            '{' | '}' | '[' | ']' | '(' | ')' |
            // arith operator
            '+' | '-' | '*' | '/' | '%' |
            // separators
            ',' | ';' | '.' => {
                self.advance_col(1)?;
                self.iter.next();
                Token(TokenKind::Symbol, Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: start_u32.saturating_add(1),
                })
            }
            #[cfg(feature = "azure-rbac")]
            // RBAC logical AND operator (&&)
            '&' if self.enable_rbac_tokens && self.peekahead(1).1 == '&' => {
                self.advance_col(2)?;
                self.iter.next();
                self.iter.next();
                Token(TokenKind::AzureRbac(AzureRbacTokenKind::LogicalAnd), Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: start_u32.saturating_add(2),
                })
            }
            #[cfg(feature = "azure-rbac")]
            // RBAC logical OR operator (||)
            '|' if self.enable_rbac_tokens && self.peekahead(1).1 == '|' => {
                self.advance_col(2)?;
                self.iter.next();
                self.iter.next();
                Token(TokenKind::AzureRbac(AzureRbacTokenKind::LogicalOr), Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: start_u32.saturating_add(2),
                })
            }
            // Generic bin operators (when RBAC tokens not enabled or single & |)
            '&' | '|' => {
                self.advance_col(1)?;
                self.iter.next();
                Token(TokenKind::Symbol, Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: start_u32.saturating_add(1),
                })
            }
            ':' => {
                self.advance_col(1)?;
                self.iter.next();
                let mut end = start_u32.saturating_add(1);
                if self.peek().1 == '=' || (self.peek().1 == ':' && self.double_colon_token) {
                    self.advance_col(1)?;
                    self.iter.next();
                    end = end.saturating_add(1);
                }
                Token(TokenKind::Symbol, Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end,
                })
            }
            // < <= > >= = ==
            '<' | '>' | '=' => {
                self.advance_col(1)?;
                self.iter.next();
                if self.peek().1 == '=' {
                    self.advance_col(1)?;
                    self.iter.next();
                };
                Token(TokenKind::Symbol, Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: usize_to_u32(self.peek().0)?,
                })
            }
            '!' if self.peekahead(1).1 == '=' => {
                self.advance_col(2)?;
                self.iter.next();
                self.iter.next();
                Token(TokenKind::Symbol, Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: usize_to_u32(self.peek().0)?,
                })
            }
            #[cfg(feature = "azure-rbac")]
            // RBAC @ token for attribute references
            '@' if self.enable_rbac_tokens => {
                self.advance_col(1)?;
                self.iter.next();
                Token(TokenKind::AzureRbac(AzureRbacTokenKind::At), Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: start_u32.saturating_add(1),
                })
            }
            '"' => self.read_string()?,
            #[cfg(feature = "azure-rbac")]
            '\'' if self.allow_single_quoted_strings => self.read_single_quoted_string()?,
            '`' => self.read_raw_string()?,
            '\x00' => Token(TokenKind::Eof, Span {
                source: self.source.clone(),
                line: self.line,
                col,
                start: start_u32,
                end: start_u32,
            }),
            _ if chr.is_ascii_digit() => self.read_number()?,
            _ if chr.is_ascii_alphabetic() || chr == '_' => {
                let mut ident = self.read_ident()?;
                if ident.1.text() == "set" && self.peek().1 == '(' {
                    // set immediately followed by ( is treated as set( if
                    // the next token is ).
                    let state = (self.iter.clone(), self.line, self.col);
                    self.iter.next();

                    // Check it next token is ).
                    let next_tok = self.next_token()?;
                    let is_setp = next_tok.1.text() == ")";

                    // Restore state
                    (self.iter, self.line, self.col) = state;

                    if is_setp {
                        self.iter.next();
                        self.advance_col(1)?;
                        ident.1.end = ident.1.end.saturating_add(1);
                    }
                }
                ident
            }
            _ if self.unknown_char_is_symbol => {
                self.advance_col(1)?;
                self.iter.next();
                Token(TokenKind::Symbol, Span {
                    source: self.source.clone(),
                    line: self.line,
                    col,
                    start: start_u32,
                    end: start_u32.saturating_add(1),
                })
            }
            _ => return Err(self.source.error(self.line, self.col, "invalid character")),
        };

        check_memory_limit()?;
        Ok(token)
    }
}
