// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::lexer::*;
use crate::number::*;
use crate::value::*;
use crate::*;

use alloc::collections::BTreeMap;
use core::str::FromStr;

use anyhow::{anyhow, bail, Result};

#[derive(Clone)]
pub struct Parser<'source> {
    source: Source,
    lexer: Lexer<'source>,
    tok: Token,
    line: u32,
    end: u32,
    future_keywords: BTreeMap<String, Option<Span>>,
    rego_v1: bool,
}

const FUTURE_KEYWORDS: [&str; 4] = ["contains", "every", "if", "in"];

impl<'source> Parser<'source> {
    pub fn new(source: &'source Source) -> Result<Self> {
        let mut lexer = Lexer::new(source);
        let tok = lexer.next_token()?;
        Ok(Self {
            source: source.clone(),
            lexer,
            tok,
            line: 0,
            end: 0,
            future_keywords: BTreeMap::new(),
            rego_v1: false,
        })
    }

    pub fn enable_rego_v1(&mut self) -> Result<()> {
        self.turn_on_rego_v1(&None)
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
            TokenKind::Symbol | TokenKind::Number | TokenKind::Ident | TokenKind::Eof => {
                self.tok.1.text()
            }
            TokenKind::String | TokenKind::RawString => "",
        }
    }

    pub fn next_token(&mut self) -> Result<()> {
        self.line = self.tok.1.line;
        self.end = self.tok.1.end;
        self.tok = self.lexer.next_token()?;
        Ok(())
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

            std::println!(
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

    pub fn get_path_ref_components_into(refr: &Ref<Expr>, comps: &mut Vec<Span>) -> Result<()> {
        match refr.as_ref() {
            Expr::RefDot { refr, field, .. } => {
                Self::get_path_ref_components_into(refr, comps)?;
                comps.push(field.0.clone());
            }
            Expr::RefBrack { refr, index, .. } => {
                Self::get_path_ref_components_into(refr, comps)?;
                Self::get_path_ref_components_into(index, comps)?;
            }
            Expr::Var(v) => comps.push(v.0.clone()),
            Expr::String(s) => comps.push(s.0.clone()),
            Expr::True(s) | Expr::False(s) | Expr::Null(s) => comps.push(s.clone()),
            Expr::Number(s) => {
                // Ensure that the span will be the serialized representation.
                if *s.0.text() == s.1.to_json_str()? {
                    comps.push(s.0.clone());
                } else {
                    bail!(refr.span().error("not a valid ref"));
                }
            }

            _ => bail!(refr.span().error("not a valid ref")),
        }
        Ok(())
    }

    pub fn get_path_ref_components(refr: &Ref<Expr>) -> Result<Vec<Span>> {
        let mut comps = vec![];
        Self::get_path_ref_components_into(refr, &mut comps)?;
        Ok(comps)
    }

    fn handle_import_future_keywords(&mut self, comps: &[Span]) -> Result<bool> {
        if comps.len() >= 2 && comps[0].text() == "future" && comps[1].text() == "keywords" {
            match comps.len() - 2 {
                1 => self.set_future_keyword(comps[2].text(), &Some(comps[2].clone()))?,
                0 => {
                    let span = &comps[1];
                    for kw in FUTURE_KEYWORDS.iter() {
                        self.set_future_keyword(kw, &Some(span.clone()))?;
                    }
                }
                _ => {
                    let s = &comps[3];
                    return Err(self
                        .source
                        .error(s.line, s.col - 1, "invalid future keyword"));
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

    fn read_number(span: Span) -> Result<Expr> {
        match Number::from_str(span.text()) {
            Ok(v) => Ok(Expr::Number((span, Value::Number(v)))),
            Err(_) => bail!(span.error("could not parse number")),
        }
    }

    fn parse_scalar_or_var(&mut self) -> Result<Expr> {
        let span = self.tok.1.clone();
        let node = match &self.tok.0 {
            TokenKind::Number => Self::read_number(span)?,
            TokenKind::String => {
                let v = match serde_json::from_str::<Value>(format!("\"{}\"", span.text()).as_str())
                {
                    Ok(v) => v,
                    Err(e) => bail!(span.error(format!("invalid string literal. {e}").as_str())),
                };
                Expr::String((span, v))
            }
            TokenKind::RawString => {
                let v = Value::from(span.text().to_string());
                Expr::RawString((span, v))
            }
            TokenKind::Ident => match self.token_text() {
                "null" => Expr::Null(span),
                "true" => Expr::True(span),
                "false" => Expr::False(span),
                _ => {
                    let ident = self.parse_var()?;
                    let v = Value::from(ident.text());
                    return Ok(Expr::Var((ident, v)));
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

    fn parse_compr(&mut self, delim: &str) -> Result<(Expr, Query)> {
        // Save the state.
        let state = self.clone();
        let mut span = self.tok.1.clone();

        // Parse the first expression as a ref.
        let term = match self.parse_ref() {
            Ok(e) if self.token_text() == "|" => e,
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
            Err(_) if self.end == pos => {
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
                })
            }
            Err(_) if self.end == pos => {
                // No progress was made in parsing comprehension.
                // Parse as array.
                let mut items = vec![];
                if self.token_text() != "]" {
                    items.push(Ref::new(self.parse_in_expr()?));
                    while self.token_text() == "," {
                        self.next_token()?;
                        match self.token_text() {
                            "]" => break,
                            "" if self.tok.0 == TokenKind::Eof => break,
                            _ => items.push(Ref::new(self.parse_in_expr()?)),
                        }
                    }
                }
                self.expect("]", "while parsing array")?;
                span.end = self.end;
                Ok(Expr::Array { span, items })
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
                });
            }
            Err(err) if self.end != pos => {
                // Some progress was made parsing the set comprehension.
                // Report errors.
                return Err(err);
            }
            _ => (),
        }

        // It could be a set, object or object comprehension.
        // In all the cases, the first expression must parse successfully.
        if self.token_text() == "}" {
            self.next_token()?;
            span.end = self.end;
            return Ok(Expr::Object {
                span,
                fields: vec![],
            });
        }

        let mut item_span = self.tok.1.clone();
        let first = self.parse_in_expr()?;

        if self.token_text() != ":" {
            // Parse as set.
            let mut items = vec![Ref::new(first)];
            while self.token_text() == "," {
                self.next_token()?;
                match self.token_text() {
                    "}" => break,
                    "" if self.tok.0 == TokenKind::Eof => break,
                    _ => items.push(Ref::new(self.parse_in_expr()?)),
                }
            }
            self.expect("}", "while parsing set")?;
            span.end = self.end;
            return Ok(Expr::Set { span, items });
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
                });
            }
            Err(err) if self.end != pos => {
                // Some progress was made parsing the object comprehension.
                // Report errors.
                return Err(err);
            }
            _ => (),
        }

        // Parse object
        let mut items = vec![];

        let value = self.parse_in_expr()?;
        item_span.end = self.end;
        items.push((item_span, Ref::new(first), Ref::new(value)));

        while self.token_text() == "," {
            self.next_token()?;
            let item_start = self.tok.1.start;
            let key = match self.token_text() {
                "}" => break,
                "" if self.tok.0 == TokenKind::Eof => break,
                _ => self.parse_in_expr()?,
            };

            let mut item_span = self.tok.1.clone();
            span.start = item_start;
            self.expect(":", "while parsing object item")?;
            let value = self.parse_in_expr()?;
            item_span.end = self.end;

            items.push((item_span, Ref::new(key), Ref::new(value)));
        }

        self.expect("}", "while parsing object")?;
        span.end = self.end;

        Ok(Expr::Object {
            span,
            fields: items,
        })
    }

    fn parse_empty_set(&mut self) -> Result<Expr> {
        let mut span = self.tok.1.clone();
        self.expect("set(", "while parsing empty set")?;
        self.expect(")", "while parsing empty set")?;
        span.end = self.tok.1.end;
        Ok(Expr::Set {
            span,
            items: vec![],
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
        })
    }

    fn parse_ref(&mut self) -> Result<Expr> {
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
                Expr::Var(_) => break,
                Expr::RefDot { refr, .. } => expr = refr,
                Expr::RefBrack { refr, index, .. } => {
                    expr = refr;
                    possible_fcn = matches!(index.as_ref(), Expr::String(_));
                }
                _ => {
                    possible_fcn = false;
                }
            }
        }
        matches!(&term, Expr::Var(_));

        loop {
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
                    // Read identifier.
                    self.next_token()?;
                    let field = self.parse_var()?;
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
                    };
                }
                "[" => {
                    self.next_token()?;
                    let index = self.parse_in_expr()?;

                    // If the index is a string, the ref could be path to a function.
                    possible_fcn = possible_fcn && matches!(&index, Expr::String(_));

                    self.expect("]", "while parsing bracketed reference")?;
                    span.end = self.end;

                    term = Expr::RefBrack {
                        span,
                        refr: Ref::new(term),
                        index: Ref::new(index),
                    };
                }
                "(" if possible_fcn => {
                    self.next_token()?;
                    let mut args = vec![];
                    if self.token_text() != ")" {
                        args.push(Ref::new(self.parse_in_expr()?));
                        while self.token_text() == "," {
                            self.next_token()?;
                            match self.token_text() {
                                ")" => break,
                                "" if self.tok.0 == TokenKind::Eof => break,
                                _ => args.push(Ref::new(self.parse_in_expr()?)),
                            }
                        }
                    }
                    self.expect(")", "while parsing call expr")?;
                    span.end = self.end;
                    term = Expr::Call {
                        span,
                        fcn: Ref::new(term),
                        params: args,
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
            };
        }
    }

    fn parse_arith_expr(&mut self) -> Result<Expr> {
        let start = self.tok.1.start;
        let mut expr = self.parse_mul_div_mod_expr()?;

        loop {
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
                Self::read_number(rhs_span)?
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
            };
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
            };
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
            };
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
            };
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
        return self.parse_or_expr();

        #[cfg(not(feature = "rego-extensions"))]
        return self.parse_membership_expr();
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
            };
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
        let state = self.clone();
        let start = self.tok.1.start;
        let expr = self.parse_ref()?;

        let mut span = self.tok.1.clone();
        span.start = start;
        let op = match self.token_text() {
            "=" => AssignOp::Eq,
            ":=" if self.rego_v1 => {
                if let Expr::Var(v) = &expr {
                    if v.0.text() == "input" {
                        bail!(span.error("input cannot be shadowed"));
                    }
                    if v.0.text() == "data" {
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
        Ok(Expr::AssignExpr {
            span,
            op,
            lhs: Ref::new(expr),
            rhs: Ref::new(right),
        })
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
        let mut vars = vec![self.tok.1.clone()];
        let mut refs = vec![Ref::new(self.parse_ref()?)];

        while self.token_text() == "," {
            self.next_token()?;
            let mut span = self.tok.1.clone();
            refs.push(Ref::new(self.parse_ref()?));
            span.end = self.end;
            vars.push(span);
        }

        if self.token_text() != "in" || !self.is_imported_future_keyword("in") {
            if self.token_text() == "in" {
                self.warn_future_keyword();
            }
            // All the refs must be identifiers
            for (idx, ref_expr) in refs.iter().enumerate() {
                let span = &vars[idx];
                match ref_expr.as_ref() {
                    Expr::Var(_) => (),
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
            return Ok(Literal::SomeVars { span, vars });
        }

        let (key, value) = match refs.len() {
            2 => (Some(refs[0].clone()), refs[1].clone()),
            1 => (None, refs[0].clone()),
            _ => {
                let span = &vars[2];
                return Err(anyhow!(
                    "{}:{}:{} error: encountered `{}` while expecting `in`",
                    span.source.file(),
                    span.line,
                    span.col,
                    span.text()
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
        })
    }

    fn parse_query(&mut self, mut span: Span, end_delim: &str) -> Result<Query> {
        let state = self.clone();
        let is_definite_query = matches!(self.token_text(), "some" | "every");

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
        }

        if !end_delim.is_empty() {
            self.expect(end_delim, "while parsing query")?;
        }
        span.end = self.end;
        Ok(Query {
            span,
            stmts: literals,
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

        let mut refr = Expr::Var(Self::span_and_value(var));
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
                    // Read identifier.
                    self.next_token()?;
                    let field = self.parse_ident()?;
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
                    };
                }
                "[" => {
                    self.next_token()?;
                    let index = match &self.tok.0 {
                        TokenKind::String => Expr::String(Self::span_and_value(self.tok.1.clone())),
                        _ => {
                            return Err(self.source.error(
                                self.tok.1.line,
                                self.tok.1.col,
                                "expected string",
                            ));
                        }
                    };
                    self.next_token()?;
                    self.expect("]", "while parsing bracketed reference")?;
                    span.end = self.end;
                    refr = Expr::RefBrack {
                        span,
                        refr: Ref::new(refr),
                        index: Ref::new(index),
                    };
                }
                _ => break,
            }
        }

        Ok(refr)
    }

    fn parse_rule_ref(&mut self) -> Result<Expr> {
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
            Expr::Var(Self::span_and_value(v))
        } else {
            return Err(self.source.error(
                span.line,
                span.col,
                "expecting identifier. Failed to parse rule-ref.",
            ));
        };

        loop {
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
                    let field = self.parse_var()?;
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
                    };
                }
                _ => break,
            }
        }

        Ok(term)
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
                    while self.token_text() == "," {
                        self.next_token()?;
                        match self.token_text() {
                            ")" => break,
                            "" if self.tok.0 == TokenKind::Eof => break,
                            _ => args.push(Ref::new(self.parse_term()?)),
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
                            if matches!(refr.as_ref(), Expr::Var(_)) =>
                        {
                            return Ok(RuleHead::Set {
                                span,
                                refr: refr.clone(),
                                key: Some(index.clone()),
                            });
                        }
                        Expr::RefDot { refr, .. } if matches!(refr.as_ref(), Expr::Var(_)) => {
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
        Ok(Query { span, stmts })
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
                    query,
                });
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
                    query,
                });
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
                query,
            });
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
                        query,
                    });
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
                        query,
                    });
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
                    });
                    span.end = self.end;
                    bodies.push(RuleBody {
                        span,
                        assign,
                        query,
                    });
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
                .map(|a| Ref::new(Expr::Var(Self::span_and_value(a))))
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

    pub fn parse(&mut self) -> Result<Module> {
        let package = self.parse_package()?;
        let imports = self.parse_imports()?;

        let mut policy = vec![];
        while self.tok.0 != TokenKind::Eof {
            policy.push(Ref::new(self.parse_rule()?));
        }

        Ok(Module {
            package,
            imports,
            policy,
            rego_v1: self.rego_v1,
        })
    }

    pub fn parse_user_query(&mut self) -> Result<Ref<Query>> {
        let span = self.tok.1.clone();
        let query = Ref::new(self.parse_query(span, "")?);
        if self.tok.0 != TokenKind::Eof {
            bail!(self.tok.1.error("expecting EOF"));
        }
        Ok(query)
    }
}
