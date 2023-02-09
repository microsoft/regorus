// Copyright (c) Rego-Rs Authors.
// Licensed under the Apache 2.0 license.

use core::fmt::{Debug, Formatter};
use core::iter::Peekable;
use core::str::CharIndices;

use crate::value::Value;
use anyhow::{anyhow, bail, Result};

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Source<'source> {
    pub file: &'source str,
    pub contents: &'source str,
    pub lines: Vec<&'source str>,
}

impl<'source> Source<'source> {
    pub fn message(&self, line: u16, col: u16, kind: &str, msg: &str) -> String {
        if line as usize > self.lines.len() {
            return format!("{}: invalid line {} specified", self.file, line);
        }

        let line_str = format!("{}", line);
        let line_num_width = line_str.len() + 1;
        let col_spaces = col as usize - 1;

        format!(
            "\n-->{}:{}:{}\n{:<line_num_width$}|\n\
		{:<line_num_width$}| {}\n\
		{:<line_num_width$}| {:<col_spaces$}^\n\
		{}: {}",
            self.file,
            line,
            col,
            "",
            line,
            self.lines[line as usize - 1],
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

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Span<'source> {
    pub source: &'source Source<'source>,
    pub line: u16,
    pub col: u16,
    pub start: u16,
    pub end: u16,
}

impl<'source> Span<'source> {
    pub fn text(&self) -> &'source str {
        &self.source.contents[self.start as usize..self.end as usize]
    }
}

impl<'source> Debug for Span<'source> {
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Token<'source>(pub TokenKind, pub Span<'source>);

#[derive(Clone)]
pub struct Lexer<'source> {
    source: &'source Source<'source>,
    iter: Peekable<CharIndices<'source>>,
    line: u16,
    col: u16,
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source Source<'source>) -> Self {
        Self {
            source,
            iter: source.contents.char_indices().peekable(),
            line: 1,
            col: 1,
        }
    }

    fn peek(&mut self) -> (usize, char) {
        match self.iter.peek() {
            Some((index, chr)) => (*index, *chr),
            _ => (self.source.contents.len(), '\x00'),
        }
    }

    fn peekahead(&mut self, n: usize) -> (usize, char) {
        match self.iter.clone().nth(n) {
            Some((index, chr)) => (index, chr),
            _ => (self.source.contents.len(), '\x00'),
        }
    }

    fn read_ident(&mut self) -> Result<Token<'source>> {
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
                source: self.source,
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
    fn read_number(&mut self) -> Result<Token<'source>> {
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
        match serde_json::from_str::<'source, Value>(&self.source.contents[start..end]) {
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
                source: self.source,
                line: self.line,
                col,
                start: start as u16,
                end: end as u16,
            },
        ))
    }

    fn read_raw_string(&mut self) -> Result<Token<'source>> {
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
                source: self.source,
                line,
                col,
                start: start as u16,
                end: end as u16 - 1,
            },
        ))
    }

    fn read_string(&mut self) -> Result<Token<'source>> {
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
        match serde_json::from_str::<'source, String>(&self.source.contents[start - 1..end]) {
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
                source: self.source,
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

    pub fn next_token(&mut self) -> Result<Token<'source>> {
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
	    '+' | '-' | '*' | '/' |
	    // bin operator
	    '&' | '|' |
	    // separators
	    ',' | ';' | '.' => {
		self.col += 1;
		self.iter.next();
		Ok(Token(TokenKind::Symbol, Span {
		    source: self.source,
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
		    source: self.source,
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
		    source: self.source,
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
		    source: self.source,
		    line: self.line,
		    col,
		    start: start as u16,
		    end: self.peek().0 as u16,
		}))
	    }
	    '"' => self.read_string(),
	    '`' => self.read_raw_string(),
	    '\x00' => Ok(Token(TokenKind::Eof, Span {
		source: self.source,
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
