// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use core::fmt::{Debug, Formatter};
use core::iter::Peekable;
use core::str::CharIndices;

use std::convert::AsRef;
use std::hash::{Hash, Hasher};
use std::path::Path;

use crate::Rc;
use crate::Value;

use anyhow::{anyhow, bail, Result};

#[derive(Clone)]
struct SourceInternal {
    pub file: String,
    pub contents: String,
    pub lines: Vec<(u16, u16)>,
}

#[derive(Clone)]
pub struct Source {
    src: Rc<SourceInternal>,
}

impl std::cmp::Ord for Source {
    fn cmp(&self, other: &Source) -> std::cmp::Ordering {
        Rc::as_ptr(&self.src).cmp(&Rc::as_ptr(&other.src))
    }
}

impl std::cmp::PartialOrd for Source {
    fn partial_cmp(&self, other: &Source) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl std::cmp::PartialEq for Source {
    fn eq(&self, other: &Source) -> bool {
        Rc::as_ptr(&self.src) == Rc::as_ptr(&other.src)
    }
}

impl std::cmp::Eq for Source {}

impl Hash for Source {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.src).hash(state)
    }
}

impl Debug for Source {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.src.file.fmt(f)
    }
}

#[derive(Clone)]
pub struct SourceStr {
    source: Source,
    start: u16,
    end: u16,
}

impl Debug for SourceStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.text().fmt(f)
    }
}

impl std::fmt::Display for SourceStr {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        std::fmt::Display::fmt(&self.text(), f)
    }
}

impl SourceStr {
    pub fn new(source: Source, start: u16, end: u16) -> Self {
        Self { source, start, end }
    }

    pub fn text(&self) -> &str {
        &self.source.contents()[self.start as usize..self.end as usize]
    }

    pub fn clone_empty(&self) -> SourceStr {
        Self {
            source: self.source.clone(),
            start: 0,
            end: 0,
        }
    }
}

impl std::cmp::PartialEq for SourceStr {
    fn eq(&self, other: &Self) -> bool {
        self.text().eq(other.text())
    }
}

impl std::cmp::Eq for SourceStr {}

impl std::cmp::PartialOrd for SourceStr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.text().cmp(other.text()))
    }
}

impl std::cmp::Ord for SourceStr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.text().cmp(other.text())
    }
}

impl Source {
    pub fn new(file: String, contents: String) -> Source {
        let mut lines = vec![];
        let mut prev_ch = ' ';
        let mut prev_pos = 0u16;
        let mut start = 0u16;
        for (i, ch) in contents.char_indices() {
            if ch == '\n' {
                let end = match prev_ch {
                    '\r' => prev_pos,
                    _ => i as u16,
                };
                lines.push((start, end));
                start = i as u16 + 1;
            }
            prev_ch = ch;
            prev_pos = i as u16;
        }

        if (start as usize) < contents.len() {
            lines.push((start, contents.len() as u16));
        } else if contents.is_empty() {
            lines.push((0, 0));
        } else {
            let s = (contents.len() - 1) as u16;
            lines.push((s, s));
        }
        Self {
            src: Rc::new(SourceInternal {
                file,
                contents,
                lines,
            }),
        }
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Source> {
        let contents = match std::fs::read_to_string(&path) {
            Ok(c) => c,
            Err(e) => bail!("Failed to read {}. {e}", path.as_ref().display()),
        };
        // TODO: retain path instead of converting to string
        Ok(Self::new(
            path.as_ref().to_string_lossy().to_string(),
            contents,
        ))
    }

    pub fn file(&self) -> &String {
        &self.src.file
    }
    pub fn contents(&self) -> &String {
        &self.src.contents
    }
    pub fn line(&self, idx: u16) -> &str {
        let idx = idx as usize;
        if idx < self.src.lines.len() {
            let (start, end) = self.src.lines[idx];
            &self.src.contents[start as usize..end as usize]
        } else {
            ""
        }
    }

    pub fn message(&self, line: u16, col: u16, kind: &str, msg: &str) -> String {
        if line as usize > self.src.lines.len() {
            return format!("{}: invalid line {} specified", self.src.file, line);
        }

        let line_str = format!("{line}");
        let line_num_width = line_str.len() + 1;
        let col_spaces = col as usize - 1;

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
            self.line(line - 1),
            "",
            "",
            kind,
            msg
        )
    }

    pub fn error(&self, line: u16, col: u16, msg: &str) -> anyhow::Error {
        anyhow!(self.message(line, col, "error", msg))
    }
}

#[derive(Clone)]
pub struct Span {
    pub source: Source,
    pub line: u16,
    pub col: u16,
    pub start: u16,
    pub end: u16,
}

impl Span {
    pub fn text(&self) -> &str {
        &self.source.contents()[self.start as usize..self.end as usize]
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
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TokenKind {
    Symbol,
    String,
    RawString,
    Number,
    Ident,
    Eof,
}

#[derive(Debug, Clone)]
pub struct Token(pub TokenKind, pub Span);

#[derive(Clone)]
pub struct Lexer<'source> {
    source: Source,
    iter: Peekable<CharIndices<'source>>,
    line: u16,
    col: u16,
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source Source) -> Self {
        Self {
            source: source.clone(),
            iter: source.contents().char_indices().peekable(),
            line: 1,
            col: 1,
        }
    }

    fn peek(&mut self) -> (usize, char) {
        match self.iter.peek() {
            Some((index, chr)) => (*index, *chr),
            _ => (self.source.contents().len(), '\x00'),
        }
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
        self.col += (end - start) as u16;
        Ok(Token(
            TokenKind::Ident,
            Span {
                source: self.source.clone(),
                line: self.line,
                col,
                start: start as u16,
                end: end as u16,
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
        let ch = self.peek().1;
        if ch == 'e' || ch == 'E' {
            self.iter.next();
            // e must be followed by an optional sign and digits
            if matches!(self.peek().1, '+' | '-') {
                self.iter.next();
            }
            // Read digits. Absence of digit will be validated by serde later.
            self.read_digits();
        }

        let end = self.peek().0;
        self.col += (end - start) as u16;

        // Check for invalid number.Valid number cannot be followed by
        // these characters:
        let ch = self.peek().1;
        if ch == '_' || ch == '.' || ch.is_ascii_alphanumeric() {
            return Err(self.source.error(self.line, self.col, "invalid number"));
        }

        // Ensure that the number is parsable in Rust.
        match serde_json::from_str::<Value>(&self.source.contents()[start..end]) {
            Ok(_) => (),
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
        }

        Ok(Token(
            TokenKind::Number,
            Span {
                source: self.source.clone(),
                line: self.line,
                col,
                start: start as u16,
                end: end as u16,
            },
        ))
    }

    fn read_raw_string(&mut self) -> Result<Token> {
        self.iter.next();
        self.col += 1;
        let (start, _) = self.peek();
        let (line, col) = (self.line, self.col);
        loop {
            let (_, ch) = self.peek();
            self.iter.next();
            match ch {
                '`' => {
                    self.col += 1;
                    break;
                }
                '\x00' => {
                    return Err(self.source.error(line, col, "unmatched `"));
                }
                '\t' => self.col += 4,
                '\n' => {
                    self.line += 1;
                    self.col = 1;
                }
                _ => self.col += 1,
            }
        }
        let end = self.peek().0;
        Ok(Token(
            TokenKind::RawString,
            Span {
                source: self.source.clone(),
                line,
                col,
                start: start as u16,
                end: end as u16 - 1,
            },
        ))
    }

    fn read_string(&mut self) -> Result<Token> {
        let (line, col) = (self.line, self.col);
        self.iter.next();
        self.col += 1;
        let (start, _) = self.peek();
        loop {
            let (offset, ch) = self.peek();
            let col = self.col + (offset - start) as u16;
            match ch {
                '"' | '#' | '\x00' => {
                    break;
                }
                '\\' => {
                    self.iter.next();
                    let (_, ch) = self.peek();
                    self.iter.next();
                    match ch {
                        // json escape sequence
                        '"' | '\\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' => (),
                        'u' => {
                            for _i in 0..4 {
                                let (offset, ch) = self.peek();
                                let col = self.col + (offset - start) as u16;
                                if !ch.is_ascii_hexdigit() {
                                    return Err(self.source.error(
                                        line,
                                        col,
                                        "invalid hex escape sequence",
                                    ));
                                }
                                self.iter.next();
                            }
                        }
                        _ => return Err(self.source.error(line, col, "invalid escape sequence")),
                    }
                }
                _ => {
                    // check for valid json chars
                    let col = self.col + (offset - start) as u16;
                    if !('\u{0020}'..='\u{10FFFF}').contains(&ch) {
                        return Err(self.source.error(line, col, "invalid character in string"));
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
        self.col += (end - start) as u16;

        // Ensure that the string is parsable in Rust.
        match serde_json::from_str::<String>(&self.source.contents()[start - 1..end]) {
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

        Ok(Token(
            TokenKind::String,
            Span {
                source: self.source.clone(),
                line,
                col: col + 1,
                start: start as u16,
                end: end as u16 - 1,
            },
        ))
    }

    fn skip_ws(&mut self) -> Result<()> {
        // Only the 4 json whitespace characters are recognized.
        // https://www.crockford.com/mckeeman.html.
        // Additionally, comments are also skipped.
        // A tab is considered 4 space characters.
        'outer: loop {
            match self.peek().1 {
                ' ' => self.col += 1,
                '\t' => self.col += 4,
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
                    self.line += 1;
                }
                '#' => {
                    self.iter.next();
                    loop {
                        match self.peek().1 {
                            '\n' | '\x00' => continue 'outer,
                            _ => self.iter.next(),
                        };
                    }
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
        let col = self.col;

        match chr {
	    // Special case for - followed by digit which is a
	    // negative json number.
	    // . followed by digit is invalid number.
	    '-' | '.' if self.peekahead(1).1.is_ascii_digit() => {
		self.read_number()
	    }
	    // grouping characters
	    '{' | '}' | '[' | ']' | '(' | ')' |
	    // arith operator
	    '+' | '-' | '*' | '/' | '%' |
	    // bin operator
	    '&' | '|' |
	    // separators
	    ',' | ';' | '.' => {
		self.col += 1;
		self.iter.next();
		Ok(Token(TokenKind::Symbol, Span {
		    source: self.source.clone(),
		    line: self.line,
		    col,
		    start: start as u16,
		    end: start as u16 + 1,
		}))
	    }
	    ':' => {
		self.col += 1;
		self.iter.next();
		let mut end = start as u16 + 1;
		if self.peek().1 == '=' {
		    self.col += 1;
		    self.iter.next();
		    end += 1;
		}
		Ok(Token(TokenKind::Symbol, Span {
		    source: self.source.clone(),
		    line: self.line,
		    col,
		    start: start as u16,
		    end
		}))
	    }
	    // < <= > >= = ==
	    '<' | '>' | '=' => {
		self.col += 1;
		self.iter.next();
		if self.peek().1 == '=' {
		    self.col += 1;
		    self.iter.next();
		};
		Ok(Token(TokenKind::Symbol, Span {
		    source: self.source.clone(),
		    line: self.line,
		    col,
		    start: start as u16,
		    end: self.peek().0 as u16,
		}))
	    }
	    '!' if self.peekahead(1).1 == '=' => {
		self.col += 2;
		self.iter.next();
		self.iter.next();
		Ok(Token(TokenKind::Symbol, Span {
		    source: self.source.clone(),
		    line: self.line,
		    col,
		    start: start as u16,
		    end: self.peek().0 as u16,
		}))
	    }
	    '"' => self.read_string(),
	    '`' => self.read_raw_string(),
	    '\x00' => Ok(Token(TokenKind::Eof, Span {
		source: self.source.clone(),
		line:self.line,
		col,
		start: start as u16,
		end: start as u16
	    })),
	    _ if chr.is_ascii_digit() => self.read_number(),
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
			self.col += 1;
			ident.1.end += 1;
		    }
		}
		Ok(ident)
	    }
	    _ => Err(self.source.error(self.line, self.col, "invalid character"))
	}
    }
}
