// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![allow(
    clippy::arithmetic_side_effects,
    clippy::indexing_slicing,
    clippy::shadow_unrelated,
    clippy::missing_const_for_fn,
    clippy::semicolon_if_nothing_returned,
    clippy::unused_self,
    clippy::print_stderr,
    clippy::as_conversions,
    clippy::unused_trait_names,
    clippy::pattern_type_mismatch
)]
#![allow(missing_debug_implementations)] // parser types are internal

use crate::ast::*;
use crate::lexer::*;
use crate::number::*;
use crate::value::*;
use crate::*;

use crate::utils::limits::PolicyLengthConfig;
use alloc::collections::{BTreeMap, BTreeSet};
use core::num::NonZeroU32;
use core::str::FromStr;

use anyhow::{anyhow, bail, Result};

#[inline]
fn check_memory_limit() -> Result<()> {
    crate::utils::limits::check_memory_limit_if_needed().map_err(|err| anyhow!(err))
}

#[derive(Clone, Debug)]
pub struct ParserContext {
    rego_v1: bool,
    future_keywords: BTreeSet<String>,
    policy_length_config: PolicyLengthConfig,
}

impl ParserContext {
    pub(crate) fn create_rule_selector_source(&self, selector: &str) -> Result<Source> {
        Source::from_contents_with_limits(
            "<rule-root>".to_string(),
            selector.to_string(),
            self.policy_length_config.max_file_bytes,
            self.policy_length_config.max_lines,
        )
    }

    pub(crate) fn parse_rule_selector(
        &self,
        source: &Source,
        selector: &str,
    ) -> Result<Vec<String>> {
        let mut parser = Parser::new_with_max_col(source, Some(self.policy_length_config.max_col))?;
        parser.rego_v1 = self.rego_v1;
        parser.future_keywords = self
            .future_keywords
            .iter()
            .map(|keyword| (keyword.clone(), None))
            .collect();
        parser.parse_rule_selector(selector)
    }
}

#[derive(Clone)]
pub struct Parser<'source> {
    source: Source,
    lexer: Lexer<'source>,
    tok: Token,
    line: u32,
    end: u32,
    future_keywords: BTreeMap<String, Option<Span>>,
    rego_v1: bool,

    // Tracks current expression/comprehension/query nesting to enforce a recursion limit.
    expr_depth: usize,
    max_expr_depth: usize,
    expr_depth_overflow: bool,
    negated_binding_rejected: bool,

    // The index of the last expression that was parsed.
    eidx: u32,
    // The index of the last statement that was parsed.
    sidx: u32,
    // The index of the last query that was parsed.
    qidx: u32,
}

const FUTURE_KEYWORDS: [&str; 4] = ["contains", "every", "if", "in"];
const DEFAULT_MAX_EXPR_DEPTH: usize = Expr::MAX_DEPTH;

impl<'source> Parser<'source> {
    pub(crate) const MAX_PATH_COMPONENTS: usize = DEFAULT_MAX_EXPR_DEPTH;

    pub fn new(source: &'source Source) -> Result<Self> {
        Self::new_with_max_col(source, None)
    }

    fn new_with_max_col(source: &'source Source, max_col: Option<NonZeroU32>) -> Result<Self> {
        let mut lexer = Lexer::new(source);
        if let Some(max_col) = max_col {
            lexer.set_max_col(max_col);
        }
        Self::from_lexer(source, lexer)
    }

    fn from_lexer(source: &'source Source, mut lexer: Lexer<'source>) -> Result<Self> {
        let tok = lexer.next_token()?;
        Ok(Self {
            source: source.clone(),
            lexer,
            tok,
            line: 0,
            end: 0,
            future_keywords: BTreeMap::new(),
            rego_v1: false,
            expr_depth: 0,
            max_expr_depth: DEFAULT_MAX_EXPR_DEPTH,
            expr_depth_overflow: false,
            negated_binding_rejected: false,
            eidx: 0,
            sidx: 0,
            qidx: 0,
        })
    }

    fn next_eidx(&mut self) -> u32 {
        let eidx = self.eidx;
        self.eidx += 1;
        eidx
    }

    fn next_sidx(&mut self) -> u32 {
        let sidx = self.sidx;
        self.sidx += 1;
        sidx
    }

    fn next_qidx(&mut self) -> u32 {
        let qidx = self.qidx;
        self.qidx += 1;
        qidx
    }

    pub fn enable_rego_v1(&mut self) -> Result<()> {
        self.turn_on_rego_v1(&None)
    }

    pub(crate) fn snapshot_context(
        &self,
        policy_length_config: PolicyLengthConfig,
    ) -> ParserContext {
        ParserContext {
            rego_v1: self.rego_v1,
            future_keywords: self.future_keywords.keys().cloned().collect(),
            policy_length_config,
        }
    }

    fn turn_on_rego_v1(&mut self, span: &Option<Span>) -> Result<()> {
        self.rego_v1 = true;
        for kw in FUTURE_KEYWORDS {
            self.set_future_keyword(kw, span)?;
        }
        Ok(())
    }

    pub fn token_text(&self) -> &str {
        match self.tok.0 {
            TokenKind::String | TokenKind::RawString => "",
            _ => self.tok.1.text(),
        }
    }

    pub fn next_token(&mut self) -> Result<()> {
        self.line = self.tok.1.line;
        self.end = self.tok.1.end;
        self.tok = self.lexer.next_token()?;
        Ok(())
    }

    fn with_expr_depth<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        let entry_depth = self.expr_depth;
        if entry_depth >= self.max_expr_depth {
            self.expr_depth_overflow = true;
            bail!(self.tok.1.error(&format!(
                "expression nesting too deep (>{})",
                self.max_expr_depth
            )));
        }

        self.expr_depth = entry_depth.saturating_add(1);
        let res = f(self);
        let balanced = self.expr_depth == entry_depth.saturating_add(1);
        self.expr_depth = entry_depth;
        if !balanced {
            bail!("internal error: expression depth imbalance");
        }
        res
    }

    fn check_expr_depth(&mut self, expr: &Expr) -> Result<()> {
        let result = expr.check_depth();
        if result.is_err() {
            self.expr_depth_overflow = true;
        }
        result
    }

    fn is_terminal_parse_error(&self, error: &anyhow::Error) -> bool {
        self.expr_depth_overflow
            || self.negated_binding_rejected
            || error
                .downcast_ref::<crate::utils::limits::LimitError>()
                .is_some()
    }

    fn expect(&mut self, text: &str, context: &str) -> Result<()> {
        if self.token_text() == text {
            self.next_token()
        } else {
            let msg = format!("expecting `{text}` {context}");
            Err(self.source.error(self.tok.1.line, self.tok.1.col, &msg))
        }
    }

    fn is_imported_future_keyword(&self, kw: &str) -> bool {
        self.future_keywords.contains_key(kw)
    }

    pub fn warn_future_keyword(&self) {
        #[cfg(feature = "std")]
        {
            let kw = self.token_text();
            let msg = format!(
                "`{kw}` will be treated as identifier due to missing `import future.keywords.{kw}`"
            );

            std::eprintln!(
                "{}",
                self.source
                    .message(self.tok.1.line, self.tok.1.col, "warning", &msg)
            );
        }
    }

    pub fn set_future_keyword(&mut self, kw: &str, span: &Option<Span>) -> Result<()> {
        match (span, self.future_keywords.get(kw)) {
            (Some(span), Some(Some(s))) if self.rego_v1 => Err(self.source.error(
                span.line,
                span.col,
                format!(
                    "this import shadows previous import of `{kw}` defined at:{}",
                    s.message("", "this import is shadowed.")
                )
                .as_str(),
            )),
            _ => {
                self.future_keywords.insert(kw.to_string(), span.clone());
                if kw == "every" && !self.rego_v1 {
                    //rego.v1 explicitly adds each keyword.
                    self.future_keywords.insert("in".to_string(), span.clone());
                }
                Ok(())
            }
        }
    }

    pub fn set_max_col(&mut self, max_col: NonZeroU32) {
        self.lexer.set_max_col(max_col);
    }

    pub fn get_path_ref_components_into(refr: &Ref<Expr>, comps: &mut Vec<Span>) -> Result<()> {
        enum ComponentAction<'a> {
            Visit(&'a Expr),
            Append(&'a Span),
        }

        let mut pending = alloc::vec![ComponentAction::Visit(refr.as_ref())];
        while let Some(action) = pending.pop() {
            match action {
                ComponentAction::Visit(expression) => match expression {
                    Expr::RefDot { refr, field, .. } => {
                        pending.push(ComponentAction::Append(&field.0));
                        pending.push(ComponentAction::Visit(refr.as_ref()));
                    }
                    Expr::RefBrack { refr, index, .. } => {
                        pending.push(ComponentAction::Visit(index.as_ref()));
                        pending.push(ComponentAction::Visit(refr.as_ref()));
                    }
                    Expr::Var { span, .. }
                    | Expr::String { span, .. }
                    | Expr::Bool { span, .. }
                    | Expr::Null { span, .. } => comps.push(span.clone()),
                    Expr::Number { span, value, .. } => {
                        // Ensure that the span will be the serialized representation.
                        if span.text() == value.to_json_str()? {
                            comps.push(span.clone());
                        } else {
                            bail!(expression.span().error("not a valid ref"));
                        }
                    }
                    _ => bail!(expression.span().error("not a valid ref")),
                },
                ComponentAction::Append(span) => comps.push(span.clone()),
            }
            check_memory_limit()?;
        }
        Ok(())
    }

    pub fn get_path_ref_components(refr: &Ref<Expr>) -> Result<Vec<Span>> {
        let mut comps = vec![];
        Self::get_path_ref_components_into(refr, &mut comps)?;
        Ok(comps)
    }

    pub(crate) fn get_static_string_path_components(refr: &Expr) -> Result<Vec<String>> {
        fn collect(refr: &Expr, components: &mut Vec<String>) -> Result<()> {
            match refr {
                Expr::Var { span, .. } => components.push(span.text().to_string()),
                Expr::RefDot { refr, field, .. } => {
                    collect(refr, components)?;
                    components.push(field.0.text().to_string());
                }
                Expr::RefBrack { refr, index, .. } => {
                    collect(refr, components)?;
                    if let Expr::String { value, .. } = index.as_ref() {
                        components.push(value.as_string()?.as_ref().to_string());
                    } else {
                        bail!(refr.span().error("not a static string path"));
                    }
                }
                _ => bail!(refr.span().error("not a static string path")),
            }
            Ok(())
        }

        let mut components = Vec::new();
        collect(refr, &mut components)?;
        Ok(components)
    }

    pub(crate) fn parse_static_path_components(
        path: &str,
        max_components: usize,
    ) -> Result<Vec<String>> {
        let max_col = path
            .len()
            .checked_add(1)
            .and_then(|max_col| u32::try_from(max_col).ok())
            .and_then(NonZeroU32::new)
            .ok_or_else(|| anyhow!("path exceeds maximum supported length"))?;
        let source = Source::from_contents("entrypoint.rego".to_string(), path.to_string())?;
        let mut parser = Parser::<'_>::new_with_max_col(&source, Some(max_col))?;
        let mut components = Vec::new();

        let root = parser.parse_var()?;
        Self::push_static_path_component(&mut components, root.text().to_string(), max_components)?;

        loop {
            match parser.token_text() {
                "." | "[" if parser.tok.1.start != parser.end => {
                    bail!(
                        "{}",
                        parser.source.error(
                            parser.tok.1.line,
                            parser.tok.1.col.saturating_sub(1),
                            format!("invalid whitespace before {}", parser.token_text()).as_str()
                        )
                    );
                }
                "." => {
                    let separator = parser.tok.1.start;
                    parser.next_token()?;
                    let field = parser.parse_ref_field()?;
                    if field.start != separator.saturating_add(1) {
                        bail!(
                            "{}",
                            parser.source.error(
                                field.line,
                                field.col.saturating_sub(1),
                                "invalid whitespace between . and identifier"
                            )
                        );
                    }
                    Self::push_static_path_component(
                        &mut components,
                        field.text().to_string(),
                        max_components,
                    )?;
                }
                "[" => {
                    parser.next_token()?;
                    if parser.tok.0 != TokenKind::String {
                        bail!(parser.tok.1.error("expected string"));
                    }
                    let index = parser.parse_scalar_or_var()?;
                    parser.expect("]", "while parsing bracketed reference")?;
                    let Expr::String { ref value, .. } = index else {
                        bail!("internal error: static path component is not a string");
                    };
                    Self::push_static_path_component(
                        &mut components,
                        value.as_string()?.as_ref().to_string(),
                        max_components,
                    )?;
                }
                _ => break,
            }
        }
        if parser.tok.0 != TokenKind::Eof {
            bail!(parser.tok.1.error("expecting EOF"));
        }
        Ok(components)
    }

    fn push_static_path_component(
        components: &mut Vec<String>,
        component: String,
        max_components: usize,
    ) -> Result<()> {
        if components.len() >= max_components {
            bail!("path exceeds maximum supported component count of {max_components}");
        }
        components.push(component);
        check_memory_limit()?;
        Ok(())
    }

    fn check_path_component_limit(&self, current_count: usize) -> Result<()> {
        if current_count >= Self::MAX_PATH_COMPONENTS {
            let message = alloc::format!(
                "path exceeds maximum depth of {} components",
                Self::MAX_PATH_COMPONENTS
            );
            bail!("{}", self.tok.1.error(&message));
        }
        Ok(())
    }

    fn handle_import_future_keywords(&mut self, comps: &[Span]) -> Result<bool> {
        if comps.len() >= 2 && comps[0].text() == "future" && comps[1].text() == "keywords" {
            match comps.len().saturating_sub(2) {
                1 if comps.len() >= 3 => {
                    self.set_future_keyword(comps[2].text(), &Some(comps[2].clone()))?
                }
                0 => {
                    let span = &comps[1];
                    for kw in FUTURE_KEYWORDS.iter() {
                        self.set_future_keyword(kw, &Some(span.clone()))?;
                    }
                }
                _ if comps.len() >= 4 => {
                    let s = &comps[3];
                    return Err(self.source.error(
                        s.line,
                        s.col.saturating_sub(1),
                        "invalid future keyword",
                    ));
                }
                _ => {
                    let s = &comps[1];
                    return Err(self.source.error(s.line, s.col, "invalid future keyword"));
                }
            }
            Ok(true)
        } else if !comps.is_empty() && comps[0].text() == "future" {
            let s = &comps[0];
            Err(self
                .source
                .error(s.line, s.col, "invalid import, must be `future.keywords`"))
        } else {
            Ok(false)
        }
    }

    pub fn parse_future_keyword(
        &mut self,
        kw: &str,
        is_optional: bool,
        context: &str,
    ) -> Result<()> {
        if self.token_text() == kw {
            match &self.future_keywords.get(kw) {
                Some(_) => self.next_token(),
                None => {
                    self.warn_future_keyword();
                    Ok(())
                }
            }
        } else if !is_optional {
            // Required future keyword is missing.
            self.expect(kw, context)
        } else {
            // Keyword is optional.
            Ok(())
        }
    }

    fn is_keyword(&self, ident: &str) -> bool {
        matches!(
            ident,
            "as" | "default"
                | "else"
                | "false"
                | "import"
                | "package"
                | "not"
                | "null"
                | "some"
                | "true"
                | "with"
        )
    }

    fn parse_ident(&mut self) -> Result<Span> {
        let span = self.tok.1.clone();
        match self.tok.0 {
            TokenKind::Ident if self.is_keyword(span.text()) => Err(self.source.error(
                self.tok.1.line,
                self.tok.1.col,
                &format!("unexpected keyword `{}`", span.text()),
            )),
            TokenKind::Ident => {
                self.next_token()?;
                Ok(span)
            }
            _ => Err(self
                .source
                .error(self.tok.1.line, self.tok.1.col, "expecting identifier")),
        }
    }

    fn parse_var(&mut self) -> Result<Span> {
        let span = self.tok.1.clone();
        match self.tok.0 {
            TokenKind::Ident
                if self.is_keyword(span.text())
                    || (self.is_imported_future_keyword(span.text())
		    // contains can be the name of a builtin even when a keyword
		    && span.text() != "contains") =>
            {
                Err(self.source.error(
                    self.tok.1.line,
                    self.tok.1.col,
                    &format!("unexpected keyword `{}`", span.text()),
                ))
            }
            TokenKind::Ident => {
                self.next_token()?;
                Ok(span)
            }
            _ => Err(self
                .source
                .error(self.tok.1.line, self.tok.1.col, "expecting identifier")),
        }
    }

    /// Parse a field name after `.` in a ref expression.
    ///
    /// Unlike [`Self::parse_var`] and [`Self::parse_ident`], this method accepts **any**
    /// `TokenKind::Ident` token, including reserved keywords (e.g. `as`, `default`, `else`,
    /// `false`, `if`, `import`, `in`, `not`, `null`, `package`, `some`, `true`, `with`).
    ///
    /// The position immediately after `.` is unambiguously a field name, so there is no
    /// syntactic ambiguity with statement-level keywords. This matches OPA's
    /// `keywords_in_refs` capability, which is enabled by default in standard OPA builds.
    ///
    /// # Example
    /// ```rego
    /// allow if { input.v0.package.format == "npm" }  # `package` is a keyword but valid here
    /// ```
    fn parse_ref_field(&mut self) -> Result<Span> {
        let span = self.tok.1.clone();
        match self.tok.0 {
            TokenKind::Ident => {
                self.next_token()?;
                Ok(span)
            }
            _ => Err(self
                .source
                .error(self.tok.1.line, self.tok.1.col, "expecting identifier")),
        }
    }

    fn read_number(&mut self, span: Span) -> Result<Expr> {
        match Number::from_str(span.text()) {
            Ok(v) => Ok(Expr::Number {
                span,
                value: Value::Number(v),
                eidx: self.next_eidx(),
            }),
            Err(_) => bail!(span.error("could not parse number")),
        }
    }

    fn parse_scalar_or_var(&mut self) -> Result<Expr> {
        let span = self.tok.1.clone();
        let node = match &self.tok.0 {
            TokenKind::Number => self.read_number(span)?,
            TokenKind::String => {
                let v = match serde_json::from_str::<Value>(format!("\"{}\"", span.text()).as_str())
                {
                    Ok(v) => v,
                    Err(e) => bail!(span.error(format!("invalid string literal. {e}").as_str())),
                };
                Expr::String {
                    span,
                    value: v,
                    eidx: self.next_eidx(),
                }
            }
            TokenKind::RawString => {
                let v = Value::from(span.text().to_string());
                Expr::RawString {
                    span,
                    value: v,
                    eidx: self.next_eidx(),
                }
            }
            TokenKind::Ident => match self.token_text() {
                "null" => Expr::Null {
                    span,
                    value: Value::Null,
                    eidx: self.next_eidx(),
                },
                "true" => Expr::Bool {
                    span,
                    value: Value::from(true),
                    eidx: self.next_eidx(),
                },
                "false" => Expr::Bool {
                    span,
                    value: Value::from(false),
                    eidx: self.next_eidx(),
                },
                _ => {
                    let ident = self.parse_var()?;
                    let value = Value::from(ident.text());
                    return Ok(Expr::Var {
                        span: ident,
                        value,
                        eidx: self.next_eidx(),
                    });
                }
            },
            _ => {
                return Err(self.source.error(
                    self.tok.1.line,
                    self.tok.1.col,
                    "expecting expression",
                ))
            }
        };
        self.next_token()?;
        Ok(node)
    }

    fn has_ref_separator(&self, separators: &[&str]) -> Result<bool> {
        let mut lexer = self.lexer.clone();
        let mut token = self.tok.clone();
        let mut nesting = 0_usize;
        let mut previous_end = token.1.start;
        let mut operand = true;
        let mut unary = false;
        let mut field = false;
        let mut suffix = true;
        let mut possible_fcn = false;
        loop {
            check_memory_limit()?;
            if token.0 == TokenKind::Eof {
                return Ok(false);
            }
            let text = match token.0 {
                TokenKind::String | TokenKind::RawString => "",
                _ => token.1.text(),
            };
            if nesting != 0 {
                match text {
                    "[" | "{" | "(" | "set(" => nesting = nesting.saturating_add(1),
                    "]" | "}" | ")" => nesting = nesting.saturating_sub(1),
                    _ => {}
                }
            } else if field {
                field = false;
            } else if operand {
                // Unary terms consume a complete in-expression, even across newlines.
                if text == "-" {
                    unary = true;
                } else {
                    operand = false;
                    suffix = text != "(";
                    possible_fcn = token.0 == TokenKind::Ident
                        && !matches!(text, "null" | "true" | "false" | "set(");
                    if matches!(text, "[" | "{" | "(" | "set(") {
                        nesting = 1;
                    }
                }
            } else if separators.contains(&text) && !(unary && text == "|") {
                return Ok(true);
            } else {
                match text {
                    "." if suffix && token.1.start == previous_end => field = true,
                    "[" if suffix && token.1.start == previous_end => {
                        // Only quoted-string indices (including parenthesized) can name functions.
                        if possible_fcn {
                            let mut probe = lexer.clone();
                            let mut parens = 0_usize;
                            loop {
                                check_memory_limit()?;
                                let next = probe.next_token()?;
                                if !matches!(next.0, TokenKind::String | TokenKind::RawString)
                                    && next.1.text() == "("
                                {
                                    parens = parens.saturating_add(1);
                                } else {
                                    possible_fcn = next.0 == TokenKind::String;
                                    break;
                                }
                            }
                            while possible_fcn && parens > 0 {
                                check_memory_limit()?;
                                let next = probe.next_token()?;
                                possible_fcn =
                                    !matches!(next.0, TokenKind::String | TokenKind::RawString)
                                        && next.1.text() == ")";
                                parens = parens.saturating_sub(1);
                            }
                            if possible_fcn {
                                let next = probe.next_token()?;
                                possible_fcn =
                                    !matches!(next.0, TokenKind::String | TokenKind::RawString)
                                        && next.1.text() == "]";
                            }
                        }
                        nesting = 1;
                    }
                    "(" if suffix && possible_fcn => {
                        nesting = 1;
                        possible_fcn = false;
                    }
                    "*" | "/" | "%" | "+" | "-" | "&" | "|" | "<" | "<=" | "==" | ">=" | ">"
                    | "!="
                        if unary =>
                    {
                        operand = true
                    }
                    "in" if unary && self.future_keywords.contains_key("in") => operand = true,
                    _ if unary && token.0 == TokenKind::Number && text.starts_with('-') => {
                        possible_fcn = false;
                        suffix = true;
                    }
                    _ => return Ok(false),
                }
            }
            previous_end = token.1.end;
            token = lexer.next_token()?;
        }
    }

    fn parse_compr(&mut self, delim: &str) -> Result<(Expr, Query)> {
        // Avoid reparsing nested literals at each speculative comprehension level.
        if !self.has_ref_separator(&["|"])? {
            bail!("internal error: not a compr");
        }
        // Save the state.
        let state = self.clone();
        let mut span = self.tok.1.clone();

        // Parse the first expression as a ref.
        let term = match self.parse_ref() {
            Ok(e) if self.token_text() == "|" => e,
            Err(err) if self.is_terminal_parse_error(&err) => return Err(err),
            _ => {
                // Not a comprehension. Restore state.
                *self = state;
                bail!("internal error: not a compr");
            }
        };

        let query_span = self.tok.1.clone();
        self.next_token()?;
        let pos = self.end;
        match self.parse_query(query_span, delim) {
            Ok(query) => {
                span.end = self.end;
                Ok((term, query))
            }
            Err(err) if self.end == pos => {
                if self.is_terminal_parse_error(&err) {
                    return Err(err);
                }

                // No progress was made in parsing the query.
                // Restore state and try parsing as set, array or object.
                *self = state;
                bail!("internal error: not a compr");
            }
            Err(err) => Err(err),
        }
    }

    fn parse_compr_or_array(&mut self) -> Result<Expr> {
        // Save the state.
        let mut span = self.tok.1.clone();
        self.expect("[", "while parsing array comprehension or array")?;

        let pos = self.end;
        match self.parse_compr("]") {
            Ok((term, query)) => {
                span.end = self.end;
                Ok(Expr::ArrayCompr {
                    span,
                    term: Ref::new(term),
                    query: Ref::new(query),
                    eidx: self.next_eidx(),
                })
            }
            Err(err) if self.end == pos => {
                if self.is_terminal_parse_error(&err) {
                    return Err(err);
                }
                // No progress was made in parsing comprehension.
                // Parse as array.
                let mut items = vec![];
                if self.token_text() != "]" {
                    items.push(Ref::new(self.parse_in_expr()?));
                    // Guard array literal growth against allocator limits.
                    check_memory_limit()?;
                    while self.token_text() == "," {
                        self.next_token()?;
                        match self.token_text() {
                            "]" => break,
                            "" if self.tok.0 == TokenKind::Eof => break,
                            _ => {
                                items.push(Ref::new(self.parse_in_expr()?));
                                // Guard array literal growth against allocator limits.
                                check_memory_limit()?;
                            }
                        }
                    }
                }
                self.expect("]", "while parsing array")?;
                span.end = self.end;
                Ok(Expr::Array {
                    span,
                    items,
                    eidx: self.next_eidx(),
                })
            }
            Err(err) => Err(err),
        }
    }

    fn parse_compr_set_or_object(&mut self) -> Result<Expr> {
        let mut span = self.tok.1.clone();
        self.expect("{", "while parsing set, object or comprehension")?;

        let pos = self.end;
        match self.parse_compr("}") {
            Ok((term, query)) => {
                span.end = self.end;
                return Ok(Expr::SetCompr {
                    span,
                    term: Ref::new(term),
                    query: Ref::new(query),
                    eidx: self.next_eidx(),
                });
            }
            Err(err) if self.end != pos => {
                if self.is_terminal_parse_error(&err) {
                    return Err(err);
                }
                // Some progress was made parsing the set comprehension.
                // Report errors.
                return Err(err);
            }
            Err(err) => {
                if self.is_terminal_parse_error(&err) {
                    return Err(err);
                }
            }
        }

        // It could be a set, object or object comprehension.
        // In all the cases, the first expression must parse successfully.
        if self.token_text() == "}" {
            self.next_token()?;
            span.end = self.end;
            return Ok(Expr::Object {
                span,
                fields: vec![],
                eidx: self.next_eidx(),
            });
        }

        let mut item_span = self.tok.1.clone();
        let first = self.parse_in_expr()?;

        if self.token_text() != ":" {
            // Parse as set.
            let mut items = vec![Ref::new(first)];
            // Guard set literal growth against allocator limits.
            check_memory_limit()?;
            while self.token_text() == "," {
                self.next_token()?;
                match self.token_text() {
                    "}" => break,
                    "" if self.tok.0 == TokenKind::Eof => break,
                    _ => {
                        items.push(Ref::new(self.parse_in_expr()?));
                        // Guard set literal growth against allocator limits.
                        check_memory_limit()?;
                    }
                }
            }
            self.expect("}", "while parsing set")?;
            span.end = self.end;
            return Ok(Expr::Set {
                span,
                items,
                eidx: self.next_eidx(),
            });
        }

        // Parse as object.
        self.next_token()?;

        let pos = self.end;
        match self.parse_compr("}") {
            Ok((term, query)) => {
                span.end = self.end;
                return Ok(Expr::ObjectCompr {
                    span,
                    key: Ref::new(first),
                    value: Ref::new(term),
                    query: Ref::new(query),
                    eidx: self.next_eidx(),
                });
            }
            Err(err) if self.end != pos => {
                if self.is_terminal_parse_error(&err) {
                    return Err(err);
                }
                // Some progress was made parsing the object comprehension.
                // Report errors.
                return Err(err);
            }
            Err(err) => {
                if self.is_terminal_parse_error(&err) {
                    return Err(err);
                }
            }
        }

        // Parse object
        let mut items = vec![];

        let value = self.parse_in_expr()?;
        item_span.end = self.end;
        items.push((item_span, Ref::new(first), Ref::new(value)));
        // Guard object literal growth against allocator limits.
        check_memory_limit()?;

        while self.token_text() == "," {
            self.next_token()?;
            let mut item_span = self.tok.1.clone();
            let key = match self.token_text() {
                "}" => break,
                "" if self.tok.0 == TokenKind::Eof => break,
                _ => self.parse_in_expr()?,
            };

            self.expect(":", "while parsing object item")?;
            let value = self.parse_in_expr()?;
            item_span.end = self.end;

            items.push((item_span, Ref::new(key), Ref::new(value)));
            // Guard object literal growth against allocator limits.
            check_memory_limit()?;
        }

        self.expect("}", "while parsing object")?;
        span.end = self.end;

        Ok(Expr::Object {
            span,
            fields: items,
            eidx: self.next_eidx(),
        })
    }

    fn parse_empty_set(&mut self) -> Result<Expr> {
        let mut span = self.tok.1.clone();
        self.expect("set(", "while parsing empty set")?;
        let close_end = self.tok.1.end;
        self.expect(")", "while parsing empty set")?;
        span.end = close_end;
        Ok(Expr::Set {
            span,
            items: vec![],
            eidx: self.next_eidx(),
        })
    }

    fn parse_parens_expr(&mut self) -> Result<Expr> {
        self.next_token()?;
        let expr = self.parse_expr()?;
        self.expect(")", "while parsing parenthesized expression")?;
        //TODO: if needed introduce a parens-expr node or adjust expr's span.
        Ok(expr)
    }

    fn parse_unary_expr(&mut self) -> Result<Expr> {
        let mut span = self.tok.1.clone();
        self.next_token()?;
        let expr = self.parse_in_expr()?;
        span.end = self.end;
        Ok(Expr::UnaryExpr {
            span,
            expr: Ref::new(expr),
            eidx: self.next_eidx(),
        })
    }

    fn parse_ref(&mut self) -> Result<Expr> {
        self.with_expr_depth(|this| {
            let expr = this.parse_ref_inner()?;
            this.check_expr_depth(&expr)?;
            Ok(expr)
        })
    }

    fn parse_ref_inner(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut term = match self.token_text() {
            "[" if self.tok.0 == TokenKind::Symbol => self.parse_compr_or_array()?,
            "{" => self.parse_compr_set_or_object()?,
            "set(" => self.parse_empty_set()?,
            "(" => return self.parse_parens_expr(),
            "-" => return self.parse_unary_expr(),
            _ => self.parse_scalar_or_var()?,
        };

        let mut possible_fcn = true;
        let mut expr = &term;
        while possible_fcn {
            match expr {
                Expr::Var { .. } => break,
                Expr::RefDot { refr, .. } => expr = refr,
                Expr::RefBrack { refr, index, .. } => {
                    expr = refr;
                    possible_fcn = matches!(index.as_ref(), Expr::String { .. });
                }
                _ => {
                    possible_fcn = false;
                }
            }
        }
        matches!(&term, Expr::Var { .. });

        loop {
            self.check_expr_depth(&term)?;
            let mut span = self.tok.1.clone();
            let sep_pos = span.start;
            span.start = start;
            match self.token_text() {
                "." | "[" if self.tok.1.start != self.end => {
                    if self.line != self.tok.1.line {
                        // Newline encountered. This could be a separate
                        // literal.
                        break;
                    }
                    bail!(
                        "{}",
                        self.source.error(
                            self.tok.1.line,
                            self.tok.1.col,
                            format!("invalid whitespace before {}", self.token_text()).as_str()
                        )
                    );
                }
                "." => {
                    // Read identifier. Keywords are allowed as field names in
                    // dot-notation refs (e.g. `input.package.name`).
                    self.next_token()?;
                    let field = self.parse_ref_field()?;
                    span.end = self.end;

                    // Disallow any whitespace between . and identifier.
                    if field.start != sep_pos + 1 {
                        bail!(
                            "{}",
                            self.source.error(
                                field.line,
                                field.col - 1,
                                "invalid whitespace between . and identifier"
                            )
                        );
                    }
                    let fieldv = Value::from(field.text());
                    term = Expr::RefDot {
                        span,
                        refr: Ref::new(term),
                        field: (field, fieldv),
                        eidx: self.next_eidx(),
                    };
                }
                "[" => {
                    self.next_token()?;
                    let index = self.parse_in_expr()?;

                    // If the index is a string, the ref could be path to a function.
                    possible_fcn = possible_fcn && matches!(&index, Expr::String { .. });

                    self.expect("]", "while parsing bracketed reference")?;
                    span.end = self.end;

                    term = Expr::RefBrack {
                        span,
                        refr: Ref::new(term),
                        index: Ref::new(index),
                        eidx: self.next_eidx(),
                    };
                }
                "(" if possible_fcn => {
                    self.next_token()?;
                    let mut args = vec![];
                    if self.token_text() != ")" {
                        args.push(Ref::new(self.parse_in_expr()?));
                        // Guard call argument list against allocator limits.
                        check_memory_limit()?;
                        while self.token_text() == "," {
                            self.next_token()?;
                            match self.token_text() {
                                ")" => break,
                                "" if self.tok.0 == TokenKind::Eof => break,
                                _ => {
                                    args.push(Ref::new(self.parse_in_expr()?));
                                    // Guard call argument list against allocator limits.
                                    check_memory_limit()?;
                                }
                            }
                        }
                    }
                    self.expect(")", "while parsing call expr")?;
                    span.end = self.end;
                    term = Expr::Call {
                        span,
                        fcn: Ref::new(term),
                        params: args,
                        eidx: self.next_eidx(),
                    };

                    // The expression can no longer be a function after the call.
                    possible_fcn = false;
                }
                _ => break,
            }
        }

        Ok(term)
    }

    fn parse_term(&mut self) -> Result<Expr> {
        self.parse_ref()
    }

    fn parse_mul_div_mod_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_term()?;

        loop {
            self.check_expr_depth(&expr)?;
            let mut span = self.tok.1.clone();
            span.start = start;
            let op = match self.token_text() {
                "*" => ArithOp::Mul,
                "/" => ArithOp::Div,
                "%" => ArithOp::Mod,
                _ => return Ok(expr),
            };
            self.next_token()?;
            let right = self.parse_term()?;
            span.end = self.end;
            expr = Expr::ArithExpr {
                span,
                op,
                lhs: Ref::new(expr),
                rhs: Ref::new(right),
                eidx: self.next_eidx(),
            };
        }
    }

    fn parse_arith_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_mul_div_mod_expr()?;

        loop {
            self.check_expr_depth(&expr)?;
            let mut span = self.tok.1.clone();
            span.start = start;
            let op = match self.token_text() {
                "+" => ArithOp::Add,
                "-" => ArithOp::Sub,
                n if n.starts_with('-') && self.tok.0 == TokenKind::Number => ArithOp::Sub,
                _ => return Ok(expr),
            };
            let right = if self.token_text().len() > 1 {
                // Treat the - as a separate token
                let mut rhs_span = self.tok.1.clone();
                rhs_span.start += 1;
                rhs_span.col += 1;

                self.next_token()?;
                self.read_number(rhs_span)?
            } else {
                self.next_token()?;
                self.parse_mul_div_mod_expr()?
            };
            span.end = self.end;
            expr = Expr::ArithExpr {
                span,
                op,
                lhs: Ref::new(expr),
                rhs: Ref::new(right),
                eidx: self.next_eidx(),
            };
        }
    }

    fn parse_set_intersection_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_arith_expr()?;

        while self.token_text() == "&" {
            let mut span = self.tok.1.clone();
            span.start = start;
            self.next_token()?;
            let right = self.parse_arith_expr()?;
            span.end = self.end;
            expr = Expr::BinExpr {
                span,
                op: BinOp::Intersection,
                lhs: Ref::new(expr),
                rhs: Ref::new(right),
                eidx: self.next_eidx(),
            };
            self.check_expr_depth(&expr)?;
        }
        Ok(expr)
    }

    fn parse_set_union_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_set_intersection_expr()?;

        while self.token_text() == "|" {
            let mut span = self.tok.1.clone();
            span.start = start;
            self.next_token()?;
            let right = self.parse_set_intersection_expr()?;
            span.end = self.end;
            expr = Expr::BinExpr {
                span,
                op: BinOp::Union,
                lhs: Ref::new(expr),
                rhs: Ref::new(right),
                eidx: self.next_eidx(),
            };
            self.check_expr_depth(&expr)?;
        }
        Ok(expr)
    }

    fn parse_bool_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_set_union_expr()?;
        loop {
            let mut span = self.tok.1.clone();
            span.start = start;
            let op = match self.token_text() {
                "<" => BoolOp::Lt,
                "<=" => BoolOp::Le,
                "==" => BoolOp::Eq,
                ">=" => BoolOp::Ge,
                ">" => BoolOp::Gt,
                "!=" => BoolOp::Ne,
                _ => break,
            };
            self.next_token()?;
            let right = self.parse_set_union_expr()?;
            span.end = self.end;
            expr = Expr::BoolExpr {
                span,
                op,
                lhs: Ref::new(expr),
                rhs: Ref::new(right),
                eidx: self.next_eidx(),
            };
            self.check_expr_depth(&expr)?;
        }
        Ok(expr)
    }

    fn parse_membership_tail(
        &mut self,
        start: u32,
        mut expr1: Expr,
        mut expr2: Option<Expr>,
    ) -> Result<Expr> {
        loop {
            let mut span = self.tok.1.clone();
            span.start = start;
            self.parse_future_keyword("in", false, "while parsing membership expression")?;
            let expr3 = self.parse_bool_expr()?;
            span.end = self.end;
            let (key, value) = match expr2 {
                Some(e) => (Some(Ref::new(expr1)), Ref::new(e)),
                None => (None, Ref::new(expr1)),
            };
            expr1 = Expr::Membership {
                span,
                key,
                value,
                collection: Ref::new(expr3),
                eidx: self.next_eidx(),
            };
            self.check_expr_depth(&expr1)?;
            expr2 = None;

            if self.token_text() != "in" {
                break;
            }
        }

        Ok(expr1)
    }

    fn parse_in_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_bool_expr()?;

        while self.token_text() == "in" && self.future_keywords.contains_key("in") {
            expr = self.parse_membership_tail(start, expr, None)?;
        }

        Ok(expr)
    }

    pub fn parse_expr(&mut self) -> Result<Expr> {
        #[cfg(feature = "rego-extensions")]
        {
            self.parse_or_expr()
        }

        #[cfg(not(feature = "rego-extensions"))]
        {
            self.parse_membership_expr()
        }
    }

    #[cfg(feature = "rego-extensions")]
    pub fn parse_or_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_membership_expr()?;
        while self.token_text() == "or" {
            let mut span = self.tok.1.clone();
            span.start = start;
            self.next_token()?;
            let rhs = self.parse_membership_expr()?;
            expr = Expr::OrExpr {
                span,
                lhs: Ref::new(expr),
                rhs: Ref::new(rhs),
                eidx: self.next_eidx(),
            };
            self.check_expr_depth(&expr)?;
        }
        Ok(expr)
    }

    pub fn parse_membership_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_bool_expr()?;

        if self.token_text() == "," {
            self.next_token()?;
            let value = self.parse_bool_expr()?;
            expr = self.parse_membership_tail(start, expr, Some(value))?;
        }

        while self.token_text() == "in" && self.is_imported_future_keyword("in") {
            expr = self.parse_membership_tail(start, expr, None)?;
        }

        Ok(expr)
    }

    pub fn parse_assign_expr(&mut self) -> Result<Expr> {
        // Bare comprehension bodies must not be recursively parsed again on fallback.
        if !self.has_ref_separator(&["=", ":="])? {
            return self.parse_expr();
        }
        let state = self.clone();
        let start = self.tok.1.start;
        let expr = self.parse_ref()?;

        let mut span = self.tok.1.clone();
        span.start = start;
        let op = match self.token_text() {
            "=" => AssignOp::Eq,
            ":=" if self.rego_v1 => {
                if let Expr::Var { span: v, .. } = &expr {
                    if v.text() == "input" {
                        bail!(span.error("input cannot be shadowed"));
                    }
                    if v.text() == "data" {
                        bail!(span.error("data cannot be shadowed"));
                    }
                }
                AssignOp::ColEq
            }
            ":=" => AssignOp::ColEq,
            _ => {
                *self = state;
                return self.parse_expr();
            }
        };

        self.next_token()?;
        let right = self.parse_expr()?;
        span.end = self.end;
        let expr = Expr::AssignExpr {
            span,
            op,
            lhs: Ref::new(expr),
            rhs: Ref::new(right),
            eidx: self.next_eidx(),
        };
        self.check_expr_depth(&expr)?;
        Ok(expr)
    }

    fn parse_with_modifiers(&mut self) -> Result<Vec<WithModifier>> {
        let mut modifiers = vec![];
        while self.token_text() == "with" {
            let mut span = self.tok.1.clone();
            self.next_token()?;
            let refr = self.parse_path_ref()?;
            self.expect("as", "while parsing with-modifier expression")?;
            let r#as = self.parse_in_expr()?;
            span.end = self.end;
            modifiers.push(WithModifier {
                span,
                refr: Ref::new(refr),
                r#as: Ref::new(r#as),
            });
            // Guard with-modifier list against allocator limits.
            check_memory_limit()?;
        }
        Ok(modifiers)
    }

    fn parse_every_stmt(&mut self) -> Result<Literal> {
        let mut span = self.tok.1.clone();
        let context = "Failed to parse `every` statement.";
        self.parse_future_keyword("every", false, context)?;

        let ident = self.parse_var()?;
        let (key, value) = match self.token_text() {
            "," => {
                self.next_token()?;
                match self.parse_var() {
                    Ok(v) => (Some(ident), v),
                    Err(e) => {
                        return Err(self.source.error(
                            span.line,
                            span.col,
                            format!("Failed to parse `every` statement.\n{e}").as_str(),
                        ))
                    }
                }
            }
            _ => (None, ident),
        };

        self.parse_future_keyword("in", false, context)?;
        let domain = Ref::new(self.parse_bool_expr()?);
        let query_span = self.tok.1.clone();
        self.expect("{", context)?;
        let query = Ref::new(self.parse_query(query_span, "}")?);
        span.end = self.end;

        Ok(Literal::Every {
            span,
            key,
            value,
            domain,
            query,
        })
    }

    fn parse_some_stmt(&mut self) -> Result<Literal> {
        let mut span = self.tok.1.clone();
        self.expect("some", "while parsing some-decl")?;

        // parse any vars.
        let first_var = self.tok.1.clone();
        let first_ref = Ref::new(self.parse_ref()?);
        let mut vars = vec![first_var];
        let mut refs = vec![first_ref];
        // Guard some-statement bindings against allocator limits.
        check_memory_limit()?;

        while self.token_text() == "," {
            self.next_token()?;
            let mut span = self.tok.1.clone();
            refs.push(Ref::new(self.parse_ref()?));
            span.end = self.end;
            vars.push(span);
            // Guard some-statement bindings against allocator limits.
            check_memory_limit()?;
        }

        if self.token_text() != "in" || !self.is_imported_future_keyword("in") {
            if self.token_text() == "in" {
                self.warn_future_keyword();
            }
            // All the refs must be identifiers
            for (idx, ref_expr) in refs.iter().enumerate() {
                let span = &vars[idx];
                match ref_expr.as_ref() {
                    Expr::Var { .. } => (),
                    _ => {
                        return Err(anyhow!(
                            "{}:{}:{} error: encountered `{}` while expecting identifier",
                            span.source.file(),
                            span.line,
                            span.col,
                            span.text()
                        ));
                    }
                }
            }

            span.end = self.end;
            // Since exprs are discarded, adjust the expression index counter (saturating to avoid underflow).
            self.eidx = self.eidx.saturating_sub(vars.len() as u32);
            return Ok(Literal::SomeVars { span, vars });
        }

        if refs.len() >= 3 {
            // Too many identifiers before `in`.
            if let Some(span) = vars.get(2).or_else(|| vars.last()) {
                return Err(anyhow!(
                    "{}:{}:{} error: encountered `{}` while expecting `in`",
                    span.source.file(),
                    span.line,
                    span.col,
                    span.text()
                ));
            }
            return Err(anyhow!(
                "invalid some-decl: expected `in` after variable names"
            ));
        }

        let (key, value) = match refs.len() {
            2 => (Some(refs[0].clone()), refs[1].clone()),
            1 => (None, refs[0].clone()),
            _ => {
                // We always parse at least one identifier before `in`; guard defensively.
                // parse_ident rejects `in` when no vars are present, so this is effectively unreachable.
                return Err(anyhow!(
                    "invalid some-decl: expected variable names before `in`"
                ));
            }
        };

        self.parse_future_keyword("in", false, "while parsing some-decl")?;
        let collection = Ref::new(self.parse_bool_expr()?); // TODO: check this
        Ok(Literal::SomeIn {
            span,
            key,
            value,
            collection,
        })
    }

    fn parse_literal(&mut self) -> Result<Literal> {
        match self.token_text() {
            "some" => return self.parse_some_stmt(),
            "every" => {
                if self.future_keywords.contains_key("every") {
                    return self.parse_every_stmt();
                }
                self.warn_future_keyword();
            }
            _ => (),
        }
        let mut span = self.tok.1.clone();
        let not_expr = if self.token_text() == "not" {
            self.next_token()?;
            true
        } else {
            false
        };

        let expr = Ref::new(self.parse_assign_expr()?);
        span.end = self.end;
        if not_expr {
            if matches!(expr.as_ref(), Expr::AssignExpr { .. }) {
                self.negated_binding_rejected = true;
                bail!(span.error(
                    "negated assignment or unification is not supported; use == for negated equality"
                ));
            }
            Ok(Literal::NotExpr { span, expr })
        } else {
            Ok(Literal::Expr { span, expr })
        }
    }

    pub fn parse_literal_stmt(&mut self) -> Result<LiteralStmt> {
        let mut span = self.tok.1.clone();
        let literal = self.parse_literal()?;
        let with_mods = self.parse_with_modifiers()?;
        span.end = self.end;

        Ok(LiteralStmt {
            span,
            literal,
            with_mods,
            sidx: self.next_sidx(),
        })
    }

    fn parse_query(&mut self, span: Span, end_delim: &str) -> Result<Query> {
        self.with_expr_depth(|this| {
            let query = this.parse_query_inner(span, end_delim)?;
            let result = query.check_depth();
            if result.is_err() {
                this.expr_depth_overflow = true;
            }
            result?;
            Ok(query)
        })
    }

    fn parse_query_inner(&mut self, mut span: Span, end_delim: &str) -> Result<Query> {
        let state = self.clone();
        let is_definite_query = matches!(self.token_text(), "some" | "every" | "not");

        // TODO: empty query?
        let mut literals = vec![];

        let stmt = match self.parse_literal_stmt() {
            Ok(_) if self.token_text() == ":" => {
                // This is likely an object comprehension.
                // Restore the state and return.
                *self = state;
                bail!("try parsing as comprehension");
            }
            Ok(stmt) if self.token_text() == end_delim => {
                // Treat { 1 | 1 } as a comprehension instead of a
                // set of 1 element.
                if let Literal::Expr { expr: e, .. } = &stmt.literal {
                    if matches!(
                        e.as_ref(),
                        Expr::BinExpr {
                            op: BinOp::Union,
                            ..
                        }
                    ) {
                        *self = state;
                        bail!("try parse as comprehension");
                    }
                }
                stmt
            }
            Ok(stmt) => stmt,
            Err(e) if self.is_terminal_parse_error(&e) => return Err(e),
            Err(e) if is_definite_query => return Err(e),
            Err(e) if matches!(self.token_text(), "=" | ":=") => return Err(e),
            Err(_) => {
                // There was error parsing the first literal
                // Restore the state and return.
                *self = state;
                bail!(span.error(format!("expecting {end_delim}").as_str()));
            }
        };

        if self.token_text() == "," {
            // This is likely an array or set.
            // Restore the state.
            *self = state;
            return Err(anyhow!("encountered , when expecting {}", end_delim));
        }

        literals.push(stmt);
        // Guard query literal accumulation against allocator limits.
        check_memory_limit()?;

        loop {
            match self.token_text() {
                t if t == end_delim => break,
                "" if self.tok.0 == TokenKind::Eof => break,
                ";" => self.next_token()?,
                _ => {
                    // Next literal must be on a new line.
                    if self.line == self.tok.1.line {
                        break;
                    }
                }
            }
            let stmt = self.parse_literal_stmt()?;
            literals.push(stmt);
            // Guard query literal accumulation against allocator limits.
            check_memory_limit()?;
        }

        if !end_delim.is_empty() {
            self.expect(end_delim, "while parsing query")?;
        }
        span.end = self.end;
        Ok(Query {
            span,
            stmts: literals,
            qidx: self.next_qidx(),
        })
    }

    pub fn parse_rule_assign(&mut self) -> Result<Option<RuleAssign>> {
        let mut span = self.tok.1.clone();

        let op = match self.token_text() {
            "=" => {
                self.next_token()?;
                AssignOp::Eq
            }
            ":=" => {
                self.next_token()?;
                AssignOp::ColEq
            }
            _ => return Ok(None),
        };

        let expr = Ref::new(self.parse_expr()?);
        span.end = self.end;
        Ok(Some(RuleAssign {
            span,
            op,
            value: expr,
        }))
    }

    fn span_and_value(s: Span) -> (Span, Value) {
        let v = Value::from(s.text());
        (s, v)
    }

    fn parse_path_ref(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let var = self.parse_var()?;
        let mut component_count = 1;

        let (span, value) = Self::span_and_value(var);
        let mut refr = Expr::Var {
            span,
            value,
            eidx: self.next_eidx(),
        };
        loop {
            let mut span = self.tok.1.clone();
            let sep_pos = span.start;
            span.start = start;
            match self.token_text() {
                "." | "[" if self.tok.1.start != self.end => {
                    bail!(
                        "{}",
                        self.source.error(
                            self.tok.1.line,
                            self.tok.1.col - 1,
                            format!("invalid whitespace before {}", self.token_text()).as_str()
                        )
                    );
                }
                "." => {
                    self.check_path_component_limit(component_count)?;
                    component_count = component_count.saturating_add(1);
                    // Read identifier. Keywords are allowed as field names in
                    // dot-notation refs (e.g. `import data.my.package`).
                    self.next_token()?;
                    let field = self.parse_ref_field()?;
                    span.end = self.end;

                    // Disallow any whitespace between . and identifier.
                    if field.start != sep_pos + 1 {
                        bail!(
                            "{}",
                            self.source.error(
                                field.line,
                                field.col - 1,
                                "invalid whitespace between . and identifier"
                            )
                        );
                    }
                    refr = Expr::RefDot {
                        span,
                        refr: Ref::new(refr),
                        field: Self::span_and_value(field),
                        eidx: self.next_eidx(),
                    };
                }
                "[" => {
                    self.check_path_component_limit(component_count)?;
                    component_count = component_count.saturating_add(1);
                    self.next_token()?;
                    let index = match &self.tok.0 {
                        TokenKind::String => self.parse_scalar_or_var()?,
                        _ => {
                            return Err(self.source.error(
                                self.tok.1.line,
                                self.tok.1.col,
                                "expected string",
                            ));
                        }
                    };
                    self.expect("]", "while parsing bracketed reference")?;
                    span.end = self.end;
                    refr = Expr::RefBrack {
                        span,
                        refr: Ref::new(refr),
                        index: Ref::new(index),
                        eidx: self.next_eidx(),
                    };
                }
                _ => break,
            }
        }

        Ok(refr)
    }

    fn parse_rule_ref(&mut self) -> Result<Expr> {
        self.parse_rule_ref_with_limit(true)
    }

    fn parse_rule_ref_with_limit(&mut self, limit_height: bool) -> Result<Expr> {
        let start = self.tok.1.start;
        let span = self.tok.1.clone();

        let mut term = if self.tok.0 == TokenKind::Ident {
            let v = self.parse_var()?;
            if self.rego_v1 {
                if v.text() == "input" {
                    bail!(span.error("input cannot be shadowed"));
                }
                if v.text() == "data" {
                    bail!(span.error("data cannot be shadowed"));
                }
            }
            let (span, value) = Self::span_and_value(v);
            Expr::Var {
                span,
                value,
                eidx: self.next_eidx(),
            }
        } else {
            return Err(self.source.error(
                span.line,
                span.col,
                "expecting identifier. Failed to parse rule-ref.",
            ));
        };

        loop {
            if limit_height {
                self.check_expr_depth(&term)?;
            }
            let mut span = self.tok.1.clone();
            span.start = start;
            match self.token_text() {
                // . and [ must not have any space between the previous token.
                "." | "[" if self.tok.1.start != self.end => {
                    bail!(
                        "{}",
                        self.source.error(
                            self.tok.1.line,
                            self.tok.1.col - 1,
                            format!("invalid whitespace before {}", self.token_text()).as_str()
                        )
                    );
                }
                "." => {
                    let sep_pos = self.tok.1.start;
                    self.next_token()?;
                    // Keywords are allowed as field names in dot-notation refs.
                    let field = self.parse_ref_field()?;
                    span.end = self.end;

                    // Disallow any whitespace between . and identifier.
                    if field.start != sep_pos + 1 {
                        bail!(
                            "{}",
                            self.source.error(
                                field.line,
                                field.col - 1,
                                "invalid whitespace between . and identifier"
                            )
                        );
                    }
                    term = Expr::RefDot {
                        span,
                        refr: Ref::new(term),
                        field: Self::span_and_value(field),
                        eidx: self.next_eidx(),
                    };
                }
                "[" => {
                    self.next_token()?;
                    let index = self.parse_expr()?;
                    span.end = self.end;
                    self.expect("]", "while parsing bracketed reference")?;
                    term = Expr::RefBrack {
                        span,
                        refr: Ref::new(term),
                        index: Ref::new(index),
                        eidx: self.next_eidx(),
                    };
                }
                _ => break,
            }
        }

        Ok(term)
    }

    fn parse_rule_selector(&mut self, selector: &str) -> Result<Vec<String>> {
        let expression = self.parse_rule_ref_with_limit(false)?;
        if self.tok.0 != TokenKind::Eof {
            return Err(self.tok.1.error("expecting EOF"));
        }

        if !matches!(&expression, Expr::Var { .. } | Expr::RefDot { .. }) {
            bail!("expected a rule-root selector");
        }
        let span = expression.span();
        if span.start != 0 || span.text() != selector {
            bail!("rule-root selector must match its complete input");
        }

        let mut components = Vec::new();
        let mut expression = &expression;
        loop {
            match expression {
                Expr::Var { span, .. } => {
                    components.push(span.text().to_string());
                    check_memory_limit()?;
                    break;
                }
                Expr::RefDot { refr, field, .. } => {
                    components.push(field.0.text().to_string());
                    check_memory_limit()?;
                    expression = refr.as_ref();
                }
                _ => bail!("expected a rule-root selector"),
            }
        }
        components.reverse();
        Ok(components)
    }

    pub fn parse_rule_head(&mut self) -> Result<RuleHead> {
        let mut span = self.tok.1.clone();

        let rule_ref = Ref::new(self.parse_rule_ref()?);
        match self.token_text() {
            "(" => {
                self.next_token()?;
                let mut args = vec![];
                if self.token_text() != ")" {
                    args.push(Ref::new(self.parse_term()?));
                    // Guard rule head arguments against allocator limits.
                    check_memory_limit()?;
                    while self.token_text() == "," {
                        self.next_token()?;
                        match self.token_text() {
                            ")" => break,
                            "" if self.tok.0 == TokenKind::Eof => break,
                            _ => {
                                args.push(Ref::new(self.parse_term()?));
                                // Guard rule head arguments against allocator limits.
                                check_memory_limit()?;
                            }
                        }
                    }
                }
                self.expect(")", "while parsing function rule args")?;
                let assign = self.parse_rule_assign()?;

                span.end = self.end;
                Ok(RuleHead::Func {
                    span,
                    refr: rule_ref,
                    args,
                    assign,
                })
            }
            "contains" => {
                self.next_token()?;
                let key = Ref::new(self.parse_expr()?);
                span.end = self.end;
                Ok(RuleHead::Set {
                    span,
                    refr: rule_ref,
                    key: Some(key),
                })
            }
            _ => {
                let assign = self.parse_rule_assign()?;
                span.end = self.end;

                // Determine whether to create a set or a compr
                let is_set_follower = !self.is_keyword(self.token_text())
                    && !self.is_imported_future_keyword(self.token_text());
                if assign.is_none() && is_set_follower {
                    match rule_ref.as_ref() {
                        Expr::RefBrack { refr, index, .. }
                            if matches!(refr.as_ref(), Expr::Var { .. }) =>
                        {
                            // Adjust the expression counter since we are discarding the RefBrack expression.
                            self.eidx -= 1;
                            return Ok(RuleHead::Set {
                                span,
                                refr: refr.clone(),
                                key: Some(index.clone()),
                            });
                        }
                        Expr::RefDot { refr, .. } if matches!(refr.as_ref(), Expr::Var { .. }) => {
                            return Ok(RuleHead::Set {
                                span,
                                refr: rule_ref,
                                key: None,
                            });
                        }
                        _ => (),
                    }
                }

                // Default to a compr rule.
                Ok(RuleHead::Compr {
                    span,
                    refr: rule_ref,
                    assign,
                })
            }
        }
    }

    pub fn if_is_keyword(&self) -> bool {
        self.future_keywords.contains_key("if")
    }

    pub fn parse_query_or_literal_stmt(&mut self) -> Result<Query> {
        let state = self.clone();
        let mut span = self.tok.1.clone();

        if self.token_text() == "{" {
            self.next_token()?;
            let pos = self.end;
            match self.parse_query(span.clone(), "}") {
                Ok(query) => return Ok(query),
                Err(e) if self.is_terminal_parse_error(&e) => return Err(e),
                Err(e) if pos != self.end => {
                    // Error encountered while parsing query.
                    return Err(e);
                }
                _ => (),
            }
        }

        // Restore state.
        *self = state;
        let stmts = vec![self.parse_literal_stmt()?];
        span.end = self.end;
        let query = Query {
            span,
            stmts,
            qidx: self.next_qidx(),
        };
        query.check_depth()?;
        Ok(query)
    }

    pub fn parse_rule_bodies(&mut self) -> Result<Vec<RuleBody>> {
        let mut span = self.tok.1.clone();
        let mut bodies = vec![];

        let assign = None;
        let has_query = match self.token_text() {
            "if" if self.if_is_keyword() => {
                self.next_token()?;
                let query = Ref::new(self.parse_query_or_literal_stmt()?);
                span.end = self.end;
                bodies.push(RuleBody {
                    span,
                    assign,
                    is_else: false,
                    query,
                });
                // Guard rule body accumulation against allocator limits.
                check_memory_limit()?;
                true
            }
            "if" => {
                self.warn_future_keyword();
                false
            }
            "{" => {
                if self.rego_v1 {
                    bail!(span.error("`if` keyword is required before rule body"));
                }
                self.next_token()?;
                let query = Ref::new(self.parse_query(span.clone(), "}")?);
                span.end = self.end;
                bodies.push(RuleBody {
                    span,
                    assign,
                    is_else: false,
                    query,
                });
                // Guard rule body accumulation against allocator limits.
                check_memory_limit()?;
                true
            }
            _ => false,
        };

        match self.token_text() {
            "{" if has_query => self.parse_query_blocks(&mut bodies)?,
            "else" if has_query => self.parse_else_blocks(&mut bodies)?,
            _ => (),
        }

        Ok(bodies)
    }

    pub fn parse_query_blocks(&mut self, bodies: &mut Vec<RuleBody>) -> Result<()> {
        while self.token_text() == "{" {
            let mut span = self.tok.1.clone();
            self.next_token()?;
            let query = Ref::new(self.parse_query(span.clone(), "}")?);
            span.end = self.end;
            bodies.push(RuleBody {
                span,
                assign: None,
                is_else: false,
                query,
            });
            // Guard rule body accumulation against allocator limits.
            check_memory_limit()?;
        }
        Ok(())
    }

    pub fn parse_else_blocks(&mut self, bodies: &mut Vec<RuleBody>) -> Result<()> {
        loop {
            let mut span = self.tok.1.clone();

            match self.token_text() {
                "{" => {
                    return Err(self.source.error(
                        self.tok.1.line,
                        self.tok.1.col,
                        "expected `else` keyword",
                    ))
                }
                "else" => self.next_token()?,
                _ => break,
            }

            let assign = self.parse_rule_assign()?;

            match self.token_text() {
                "if" if self.if_is_keyword() => {
                    self.next_token()?;
                    let query = Ref::new(self.parse_query_or_literal_stmt()?);
                    span.end = self.end;
                    bodies.push(RuleBody {
                        span,
                        assign,
                        is_else: true,
                        query,
                    });
                    // Guard rule body accumulation against allocator limits.
                    check_memory_limit()?;
                }
                "{" => {
                    if self.rego_v1 {
                        bail!(span.error("`if` keyword is required before rule body"));
                    }
                    self.next_token()?;
                    let query = Ref::new(self.parse_query(span.clone(), "}")?);
                    span.end = self.end;
                    bodies.push(RuleBody {
                        span,
                        assign,
                        is_else: true,
                        query,
                    });
                    // Guard rule body accumulation against allocator limits.
                    check_memory_limit()?;
                }
                _ if assign.is_none() => {
                    if self.token_text() == "if" {
                        self.warn_future_keyword();
                    }
                    return Err(self.source.error(
                        self.tok.1.line,
                        self.tok.1.col,
                        "expected assignment or query after `else`",
                    ));
                }
                _ => {
                    let mut query_span = span.clone();
                    query_span.end = query_span.start;
                    let query = Ref::new(Query {
                        span: query_span,
                        stmts: vec![],
                        qidx: self.next_qidx(),
                    });
                    span.end = self.end;
                    bodies.push(RuleBody {
                        span,
                        assign,
                        is_else: true,
                        query,
                    });
                    // Guard rule body accumulation against allocator limits.
                    check_memory_limit()?;
                    break;
                }
            }
        }
        Ok(())
    }

    pub fn parse_default_rule(&mut self) -> Result<Rule> {
        let mut span = self.tok.1.clone();
        self.expect("default", "while parsing default rule")?;
        let rule_ref = Ref::new(self.parse_rule_ref()?);

        let mut args = vec![];
        if self.token_text() == "(" {
            self.next_token()?;
            if self.token_text() != ")" {
                loop {
                    let arg = self.parse_ident()?;
                    if arg.text() != "_" && args.iter().any(|a: &Span| *a.text() == *arg.text()) {
                        bail!(arg.error("repeating parameter name"));
                    }
                    args.push(arg);
                    // Guard default rule parameters against allocator limits.
                    check_memory_limit()?;
                    if self.token_text() == ")" || self.tok.0 == TokenKind::Eof {
                        break;
                    }
                    self.expect(",", "while parsing default rule parameters")?;
                }
            }
            self.expect(")", "while parsing default rule parameters")?;
        }

        let op = match self.token_text() {
            "=" => AssignOp::Eq,
            ":=" => AssignOp::ColEq,
            _ => {
                self.expect(":=", "while parsing default rule")?;
                // Should never reach here.
                AssignOp::Eq
            }
        };
        self.next_token()?;

        // todo: Rego errors for binary expressions here, but they are
        // somehow valid in a comprehension
        let value = Ref::new(self.parse_term()?);
        span.end = self.end;
        Ok(Rule::Default {
            span,
            refr: rule_ref,
            args: args
                .into_iter()
                .map(|a| {
                    let (span, value) = Self::span_and_value(a);
                    Ref::new(Expr::Var {
                        span,
                        value,
                        eidx: self.next_eidx(),
                    })
                })
                .collect(),
            op,
            value,
        })
    }

    pub fn parse_rule(&mut self) -> Result<Rule> {
        let pos = self.end;
        match self.parse_default_rule() {
            Ok(r) => return Ok(r),
            Err(e) if pos != self.end => return Err(e),
            _ => (),
        }

        let mut span = self.tok.1.clone();
        let head = self.parse_rule_head()?;
        let bodies = self.parse_rule_bodies()?;
        span.end = self.end;

        if let RuleHead::Set { .. } = &head {
            if let Some(RuleBody { span, .. }) = bodies.get(1) {
                bail!(span.error("else cannot be used with set rules"));
            }
        }

        if self.rego_v1 && bodies.is_empty() {
            match &head {
                RuleHead::Compr { assign, .. } | RuleHead::Func { assign, .. }
                    if assign.is_none() =>
                {
                    bail!(span.error("rule must have a body or assignment"));
                }
                RuleHead::Set { refr, key, .. } if key.is_none() => {
                    if Self::get_path_ref_components(refr)?.len() == 2 {
                        bail!(span.error("`contains` keyword is required for partial set rules"));
                    } else {
                        bail!(span.error("rule must have a body or assignment"));
                    }
                }
                _ => (),
            }
        }

        Ok(Rule::Spec { span, head, bodies })
    }

    pub fn parse_package(&mut self) -> Result<Package> {
        let mut span = self.tok.1.clone();
        self.expect("package", "Missing package declaration.")?;
        let name = self.parse_path_ref()?;
        span.end = self.end;
        Ok(Package {
            span,
            refr: Ref::new(name),
        })
    }

    fn check_and_add_import(&self, import: Import, imports: &mut Vec<Import>) -> Result<()> {
        let ref_comps = Self::get_path_ref_components(&import.refr)?;
        let comps: Vec<&str> = ref_comps.iter().map(|s| s.text()).collect();

        if comps.len() >= 2 && comps[0] == "future" && comps[1] == "keywords" {
            imports.push(import);
            // Guard import accumulation against allocator limits.
            check_memory_limit()?;
            return Ok(());
        }

        for imp in imports.iter() {
            let imp_comps = Self::get_path_ref_components(&imp.refr)?;
            let imp_comps: Vec<&str> = imp_comps.iter().map(|s| s.text()).collect();

            let shadow = match (&imp.r#as, &import.r#as) {
                (Some(i1), Some(i2)) if i1.text() == i2.text() => true,
                (None, None) if imp_comps == comps => true,
                _ => false,
            };

            if shadow {
                return Err(self.source.error(
                    import.span.line,
                    import.span.col,
                    format!(
                        "import shadows following import defined earlier:{}",
                        self.source.message(
                            imp.span.line,
                            imp.span.col,
                            "",
                            "this import is shadowed"
                        )
                    )
                    .as_str(),
                ));
            }
        }

        imports.push(import);
        // Guard import accumulation against allocator limits.
        check_memory_limit()?;
        Ok(())
    }

    fn parse_imports(&mut self) -> Result<Vec<Import>> {
        let mut imports = vec![];
        while self.token_text() == "import" {
            let mut span = self.tok.1.clone();
            self.next_token()?;
            let refr = Ref::new(self.parse_path_ref()?);

            let comps = Self::get_path_ref_components(&refr)?;
            span.end = self.end;
            if !matches!(comps[0].text(), "data" | "future" | "input" | "rego") {
                return Err(self.source.error(
                    comps[0].line,
                    comps[0].col,
                    "import path must begin with one of: {data, future, input, rego}",
                ));
            }

            let is_future_kw =
                if comps.len() == 2 && comps[0].text() == "rego" && comps[1].text() == "v1" {
                    self.turn_on_rego_v1(&Some(span.clone()))?;
                    true
                } else {
                    self.handle_import_future_keywords(&comps)?
                };

            let var = if self.token_text() == "as" {
                if is_future_kw {
                    return Err(self.source.error(
                        self.tok.1.line,
                        self.tok.1.col,
                        "`future` imports cannot be aliased",
                    ));
                }

                self.next_token()?;
                let var = self.parse_var()?;
                if var.text() == "_" {
                    return Err(self.source.error(
                        var.line,
                        var.col,
                        "`_` cannot be used as alias",
                    ));
                }
                Some(var)
            } else {
                None
            };
            span.end = self.end;

            // TODO: interpreter must check that all the imports are used.
            // future.keywords don't have to be used.
            self.check_and_add_import(
                Import {
                    span,
                    refr,
                    r#as: var,
                },
                &mut imports,
            )?;
        }

        Ok(imports)
    }

    fn parse_string_literal(&mut self) -> Result<String> {
        if self.tok.0 != TokenKind::String {
            bail!(self.tok.1.error("expected string literal"));
        }

        let string_span = self.tok.1.clone();
        let target_value =
            match serde_json::from_str::<Value>(format!("\"{}\"", string_span.text()).as_str()) {
                Ok(v) => v,
                Err(e) => {
                    bail!(string_span.error(&format!("invalid string literal: {}", e)));
                }
            };

        self.next_token()?;

        match target_value.as_string() {
            Ok(s) => Ok(s.as_ref().to_string()),
            Err(_) => {
                bail!(string_span.error("invalid string value"));
            }
        }
    }

    fn parse_target_rule(&mut self) -> Result<Option<String>> {
        if self.tok.0 == TokenKind::Ident && self.token_text() == "__target__" {
            // Parse __target__
            self.next_token()?;

            // Expect := operator
            if self.token_text() != ":=" {
                bail!(self.tok.1.error("expected ':=' after __target__"));
            }
            self.next_token()?;

            // Parse the target name string using the helper function
            let target_string = self.parse_string_literal()?;

            Ok(Some(target_string))
        } else {
            Ok(None)
        }
    }

    pub fn parse(&mut self) -> Result<Module> {
        let package = self.parse_package()?;
        let imports = self.parse_imports()?;

        let target = self.parse_target_rule()?;
        if target.is_some() {
            self.rego_v1 = true;
        }

        let mut policy = vec![];
        while self.tok.0 != TokenKind::Eof {
            policy.push(Ref::new(self.parse_rule()?));
            // Guard policy rule accumulation against allocator limits.
            check_memory_limit()?;
            if self.token_text() == "__target__" {
                bail!(self
                    .tok
                    .1
                    .error("__target__ must be defined before any rules"));
            }
        }

        let m = Module {
            package,
            imports,
            target,
            policy,
            rego_v1: self.rego_v1,
            num_expressions: self.eidx,
            num_statements: self.sidx,
            num_queries: self.qidx,
        };

        #[cfg(debug_assertions)]
        {
            indexchecker::IndexChecker::default().check_module(&m)?;
        }
        Ok(m)
    }

    pub fn parse_user_query(&mut self) -> Result<Ref<Query>> {
        let span = self.tok.1.clone();
        let query = Ref::new(self.parse_query(span, "")?);
        if self.tok.0 != TokenKind::Eof {
            bail!(self.tok.1.error("expecting EOF"));
        }
        Ok(query)
    }

    pub fn num_expressions(&self) -> u32 {
        self.eidx
    }
    pub fn num_statements(&self) -> u32 {
        self.sidx
    }
    pub fn num_queries(&self) -> u32 {
        self.qidx
    }
}

#[cfg(test)]
mod lookahead_tests {
    #![allow(clippy::panic_in_result_fn)]

    use super::*;
    use core::sync::atomic::Ordering;

    fn query_work(text: String) -> Result<usize> {
        let source = Source::from_contents("work.rego".to_string(), text)?;
        let mut parser = Parser::new(&source)?;
        parser.enable_rego_v1()?;
        let count = parser.lexer.token_count.clone();
        parser.parse_query_or_literal_stmt()?;
        assert_eq!(parser.tok.0, TokenKind::Eof);
        assert_eq!(parser.expr_depth, 0);
        Ok(count.load(Ordering::Relaxed))
    }

    #[test]
    fn nested_comprehension_work_is_not_exponential() -> Result<()> {
        let mut bounded = true;
        for open in ["[0 | ", "{0 | ", "{\"k\": 0 | "] {
            let close = if open.starts_with('[') { "]" } else { "}" };
            let mut previous = 0;
            for depth in [10, 12, 14] {
                let text = format!("{}true{}", open.repeat(depth), close.repeat(depth));
                #[cfg(feature = "std")]
                let start = std::time::Instant::now();
                let work = query_work(text)?;
                #[cfg(feature = "std")]
                std::eprintln!(
                    "head={open} depth={depth}: {work} lexer calls, {} us",
                    start.elapsed().as_micros()
                );
                if previous != 0 {
                    // Iterative lookahead may rescan enclosing tokens, but not reparse bodies.
                    bounded &= work < previous * 2;
                }
                previous = work;
            }
        }
        assert!(bounded, "adding two levels must not double parser work");
        Ok(())
    }

    #[test]
    fn shallow_statement_lookahead_work_is_linear() -> Result<()> {
        for statement in ["\"ok\"\n", "`ok`\n", "[1]\n", "(true)\n"] {
            let mut previous = 0;
            for width in [1024, 2048, 4096, 8192] {
                let text = format!("{{\n{}}}", statement.repeat(width));
                let bytes = text.len();
                let work = query_work(text)?;
                assert!(
                    work < bytes * 20,
                    "{statement:?}: {work} calls for {bytes} bytes"
                );
                if previous != 0 {
                    assert!(work <= previous * 2, "{statement:?}: {previous} -> {work}");
                }
                previous = work;
            }
        }
        Ok(())
    }

    #[test]
    fn lookahead_preserves_tokens_and_reference_boundaries() -> Result<()> {
        for (text, comprehension, assignment) in [
            ("[[1], 2]", false, false),
            ("[1 | true]", false, false),
            ("[1] | true]", true, false),
            ("{\"|\": 1} | true}", true, false),
            ("`|` | true}", true, false),
            ("set( # comment\n) | true}", true, false),
            ("f(\n[1]\n)[0]\n:= 1", false, true),
            ("x\n:= 1", false, true),
            ("true\nx := 1", false, false),
            ("\"a\"\n\"b\" = x", false, false),
            ("`a`\n`b` = x", false, false),
            ("[1]\n[2] = x", false, false),
            ("(true)\n(true) = x", false, false),
            ("f\n(1) = x", false, true),
            ("f[\"x\"]\n(1) = x", false, true),
            ("f[(\"x\")]\n(1) = x", false, true),
            ("f[(\"x\")](1) | true]", true, false),
            ("f[1]\n(1) = x", false, false),
            ("f().g\n(1) = x", false, false),
            ("-\n1 = -1", false, true),
            ("- 1\n+\n2 = -3", false, true),
            ("- 1 | 2 = -3", false, true),
            ("- 1\nin [1] = false", false, true),
            ("- 1\n-2 = -3", false, true),
            ("- (1)\n[1] = x", false, false),
        ] {
            let source = Source::from_contents("probe.rego".to_string(), text.to_string())?;
            let mut parser = Parser::new(&source)?;
            parser.enable_rego_v1()?;
            let position = (parser.tok.1.start, parser.line, parser.end, parser.eidx);
            assert_eq!(parser.has_ref_separator(&["|"])?, comprehension, "{text}");
            assert_eq!(
                parser.has_ref_separator(&["=", ":="])?,
                assignment,
                "{text}"
            );
            assert_eq!(
                (parser.tok.1.start, parser.line, parser.end, parser.eidx),
                position
            );
            parser.parse_ref()?;
            assert_eq!(
                matches!(parser.token_text(), "=" | ":="),
                assignment,
                "{text}"
            );
        }
        Ok(())
    }

    #[test]
    fn assignment_lookahead_matches_reference_parser() -> Result<()> {
        for term in [
            "x",
            "f[\"x\"]",
            "f[(\"x\")]",
            "f[1]",
            "(x)",
            "[1]",
            "{\"x\":1}",
            "- x",
            "- (x)",
            "- [1]",
            "set()",
            "f().x",
        ] {
            for tail in [
                " = 1",
                "\n= 1",
                "[1] = 1",
                "\n[1] = 1",
                "(1) = 1",
                "\n(1) = 1",
                ".x = 1",
                "\n.x = 1",
                " + 1 = 1",
                "\n+1 = 1",
                " | 1 = 1",
                "\nin [1] = 1",
                "\ntrue = 1",
            ] {
                let text = format!("{term}{tail}");
                let source = Source::from_contents("boundaries.rego".to_string(), text.clone())?;
                let mut parser = Parser::new(&source)?;
                parser.enable_rego_v1()?;
                let lookahead = parser.has_ref_separator(&["=", ":="])?;
                if parser.parse_ref().is_ok() {
                    assert_eq!(
                        lookahead,
                        matches!(parser.token_text(), "=" | ":="),
                        "{text}"
                    );
                }
            }
        }
        Ok(())
    }

    #[test]
    fn multiline_unary_unification_remains_one_statement() -> Result<()> {
        for text in [
            "-\n1 = -1",
            "- # operand on next line\n1 = -1",
            "- 1\n+\n2 = -3",
            "- 1 | 2 = -3",
            "- 1\nin [1] = false",
            "- 1\n-2 = -3",
        ] {
            let source = Source::from_contents("unary.rego".to_string(), text.to_string())?;
            let mut parser = Parser::new(&source)?;
            parser.enable_rego_v1()?;
            let query = parser.parse_user_query()?;
            assert_eq!(query.stmts.len(), 1, "{text}");
            assert!(matches!(
                &query.stmts[0].literal,
                Literal::Expr { expr, .. }
                    if matches!(expr.as_ref(), Expr::AssignExpr { op: AssignOp::Eq, .. })
            ));
            assert_eq!(parser.tok.0, TokenKind::Eof);
        }
        Ok(())
    }

    #[test]
    fn depth_errors_survive_lookahead_and_fallback() -> Result<()> {
        for text in [
            "[[[1]]]",
            "count(count(count(1)))",
            "{1: {1: {1: 1}}}",
            "{{{1}}}",
            "input[input[input[1]]]",
            "- - - 1",
            "(((1)))",
            "[[[1 | true] | true] | true]",
        ] {
            for entry in 0..3 {
                let source = Source::from_contents("nesting.rego".to_string(), text.to_string())?;
                let mut parser = Parser::new(&source)?;
                parser.max_expr_depth = 3;
                let result = match entry {
                    0 => parser.parse_expr(),
                    1 => parser.parse_in_expr(),
                    _ => parser.parse_ref(),
                };
                let error = result.err().ok_or_else(|| anyhow!("accepted {text}"))?;
                assert!(error
                    .to_string()
                    .contains("expression nesting too deep (>3)"));
                assert_eq!(parser.expr_depth, 0);
                assert!(parser.expr_depth_overflow);
            }
        }
        for text in [
            "every x in [1] { every y in [1] { every z in [1] { true } } }",
            "[1 | [[[1]]]]",
            "{1: [1 | [[[1]]]]}",
        ] {
            let source = Source::from_contents("body.rego".to_string(), text.to_string())?;
            let mut parser = Parser::new(&source)?;
            parser.enable_rego_v1()?;
            parser.max_expr_depth = 3;
            let error = parser
                .parse_user_query()
                .err()
                .ok_or_else(|| anyhow!("accepted {text}"))?;
            assert!(
                error
                    .to_string()
                    .contains("expression nesting too deep (>3)"),
                "{error}"
            );
            assert_eq!(parser.expr_depth, 0);
        }
        Ok(())
    }

    #[test]
    fn sibling_terms_and_failed_probes_do_not_consume_depth() -> Result<()> {
        for text in [
            "[[1], [2], [3], [4]]",
            "{1: [1], 2: [2], 3: [3]}",
            "{[1], [2], [3]}",
            "f([1], [2], [3])",
            "[1 + 2, 3 * 4]",
            "[1 | true]",
            "{1: 2 | true}",
        ] {
            let source = Source::from_contents("width.rego".to_string(), text.to_string())?;
            let mut parser = Parser::new(&source)?;
            parser.max_expr_depth = 3;
            parser.parse_expr()?;
            assert_eq!(parser.expr_depth, 0);
            assert!(!parser.expr_depth_overflow);
            assert_eq!(parser.tok.0, TokenKind::Eof);
        }
        Ok(())
    }

    #[test]
    fn nesting_scope_restores_depth_on_all_result_exits() -> Result<()> {
        let source = Source::from_contents("scope.rego".to_string(), "1".to_string())?;
        let mut parser = Parser::new(&source)?;
        parser.expr_depth = 1;
        parser.with_expr_depth(|_| Ok(()))?;
        assert_eq!(parser.expr_depth, 1);

        let failure: Result<()> = parser.with_expr_depth(|_| bail!("syntax error"));
        assert!(failure.is_err());
        assert_eq!(parser.expr_depth, 1);

        let imbalance = parser.with_expr_depth(|this| {
            this.expr_depth = 0;
            Ok(())
        });
        assert!(imbalance.is_err());
        assert_eq!(parser.expr_depth, 1);

        parser.max_expr_depth = 1;
        let overflow = parser.with_expr_depth(|_| Ok(()));
        assert!(overflow.is_err());
        assert_eq!(parser.expr_depth, 1);
        Ok(())
    }

    #[test]
    fn nesting_budget_covers_rule_heads_bindings_and_modifiers() -> Result<()> {
        for text in [
            "package p\nr := [[[1]]]",
            "package p\nf([[[x]]]) := 1",
            "package p\ndefault f(x) := [[[1]]]",
            "package p\nr[[[[1]]]] := 1",
            "package p\nr if { [[[x]]] := input }",
            "package p\nr if { some x in [[[1]]] }",
            "package p\nr if { true with input as [[[1]]] }",
            "package p\nr if { every x in [[[1]]] { true } }",
        ] {
            let source = Source::from_contents("contexts.rego".to_string(), text.to_string())?;
            let mut parser = Parser::new(&source)?;
            parser.enable_rego_v1()?;
            parser.max_expr_depth = 3;
            let error = parser
                .parse()
                .err()
                .ok_or_else(|| anyhow!("accepted {text}"))?;
            assert!(
                error
                    .to_string()
                    .contains("expression nesting too deep (>3)"),
                "{text}: {error}"
            );
            assert_eq!(parser.expr_depth, 0);
        }
        Ok(())
    }

    #[test]
    fn nesting_scope_preserves_typed_resource_errors() -> Result<()> {
        let source = Source::from_contents("resource.rego".to_string(), "1".to_string())?;
        let mut parser = Parser::new(&source)?;
        let limit = crate::utils::limits::LimitError::MemoryLimitExceeded { usage: 2, limit: 1 };
        let result: Result<()> = parser.with_expr_depth(|_| Err(anyhow!(limit)));
        let error = result
            .err()
            .ok_or_else(|| anyhow!("resource failure was lost"))?;
        assert_eq!(
            error.downcast_ref::<crate::utils::limits::LimitError>(),
            Some(&limit)
        );
        assert!(parser.is_terminal_parse_error(&error));
        assert_eq!(parser.expr_depth, 0);
        assert!(!parser.expr_depth_overflow);
        Ok(())
    }
}

#[cfg(test)]
mod iterative_path_tests {
    #![allow(clippy::panic_in_result_fn)]

    use super::*;
    use anyhow::Result;

    #[test]
    fn path_components_preserve_bracket_order_and_numeric_validation() -> Result<()> {
        let source =
            Source::from_contents("path.rego".to_string(), "root[\"key\"][1]".to_string())?;
        let mut parser = Parser::new(&source)?;
        let reference = Ref::new(parser.parse_rule_ref()?);
        let components = Parser::get_path_ref_components(&reference)?;
        let component_text = components
            .iter()
            .map(|component| component.text())
            .collect::<Vec<_>>();

        assert_eq!(component_text, alloc::vec!["root", "key", "1"]);

        let invalid_source =
            Source::from_contents("invalid-number.rego".to_string(), "root01".to_string())?;
        let root = Ref::new(Expr::Var {
            span: Span {
                source: invalid_source.clone(),
                line: 1,
                col: 1,
                start: 0,
                end: 4,
            },
            value: Value::from("root"),
            eidx: 0,
        });
        let invalid_number = Ref::new(Expr::Number {
            span: Span {
                source: invalid_source.clone(),
                line: 1,
                col: 5,
                start: 4,
                end: 6,
            },
            value: Value::from(1_i64),
            eidx: 0,
        });
        let invalid_reference = Ref::new(Expr::RefBrack {
            span: Span {
                source: invalid_source,
                line: 1,
                col: 1,
                start: 0,
                end: 6,
            },
            refr: root,
            index: invalid_number,
            eidx: 0,
        });
        let error = Parser::get_path_ref_components(&invalid_reference)
            .err()
            .ok_or_else(|| anyhow::anyhow!("non-canonical numeric references must fail"))?;
        assert!(error.to_string().contains("not a valid ref"));

        Ok(())
    }
}
