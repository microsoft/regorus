// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::lexer::*;
use std::collections::BTreeMap;

use anyhow::{anyhow, bail, Result};

#[derive(Clone)]
pub struct Parser<'source> {
    source: &'source Source<'source>,
    lexer: Lexer<'source>,
    tok: Token<'source>,
    line: u16,
    end: u16,
    future_keywords: BTreeMap<&'source str, Span<'source>>,
    in_default_value: bool,
}

const FUTURE_KEYWORDS: [&str; 4] = ["contains", "every", "if", "in"];

impl<'source> Parser<'source> {
    pub fn new(source: &'source Source<'source>) -> Result<Self> {
        let mut lexer = Lexer::new(source);
        let tok = lexer.next_token()?;
        Ok(Self {
            source,
            lexer,
            tok,
            line: 0,
            end: 0,
            future_keywords: BTreeMap::new(),
            in_default_value: false,
        })
    }

    pub fn next_token(&mut self) -> Result<()> {
        self.line = self.tok.1.line;
        self.end = self.tok.1.end;
        self.tok = self.lexer.next_token()?;
        Ok(())
    }

    fn expect(&mut self, text: &str, context: &str) -> Result<()> {
        if self.tok.1.text() == text {
            self.next_token()
        } else {
            let msg = format!("expecting `{text}` {context}");
            Err(self.source.error(self.tok.1.line, self.tok.1.col, &msg))
        }
    }

    fn is_imported_future_keyword(&self, kw: &str) -> bool {
        self.future_keywords.get(kw).is_some()
    }

    pub fn warn_future_keyword(&self) {
        let kw = self.tok.1.text();
        let msg = format!(
            "`{kw}` will be treated as identifier due to missing `import future.keywords.{kw}`"
        );
        println!(
            "{}",
            self.source
                .message(self.tok.1.line, self.tok.1.col, "warning", &msg)
        );
    }

    pub fn set_future_keyword(&mut self, kw: &'source str, span: &Span<'source>) -> Result<()> {
        match &self.future_keywords.get(kw) {
            Some(s) => Err(self.source.error(
                span.line,
                span.col,
                format!(
                    "this import shadows previous import of `{kw}` defined at:{}",
                    self.source
                        .message(s.line, s.col, "", "this import is shadowed.")
                )
                .as_str(),
            )),
            None => {
                self.future_keywords.insert(kw, span.clone());
                Ok(())
            }
        }
    }

    pub fn get_path_ref_components_into(
        refr: &Expr<'source>,
        comps: &mut Vec<Span<'source>>,
    ) -> Result<()> {
        match refr {
            Expr::RefDot { refr, field, .. } => {
                Self::get_path_ref_components_into(refr, comps)?;
                comps.push(field.clone());
            }
            Expr::RefBrack { refr, index, .. } => {
                Self::get_path_ref_components_into(refr, comps)?;
                Self::get_path_ref_components_into(index, comps)?;
            }
            Expr::Var(v) => comps.push(v.clone()),
            Expr::String(s) => comps.push(s.clone()),
            _ => bail!("not a simple ref"),
        }
        Ok(())
    }

    pub fn get_path_ref_components(refr: &Expr<'source>) -> Result<Vec<Span<'source>>> {
        let mut comps = vec![];
        Self::get_path_ref_components_into(refr, &mut comps)?;
        Ok(comps)
    }

    fn handle_import_future_keywords(&mut self, comps: &Vec<Span<'source>>) -> Result<bool> {
        if comps.len() >= 2 && comps[0].text() == "future" && comps[1].text() == "keywords" {
            match comps.len() - 2 {
                1 => self.set_future_keyword(comps[2].text(), &comps[2])?,
                0 => {
                    let span = &comps[1];
                    for kw in FUTURE_KEYWORDS.iter() {
                        self.set_future_keyword(kw, span)?;
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
        if self.tok.1.text() == kw {
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

    fn is_keyword(&self, ident: &'source str) -> bool {
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

    fn parse_ident(&mut self) -> Result<Span<'source>> {
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

    fn parse_var(&mut self) -> Result<Span<'source>> {
        let span = self.tok.1.clone();
        match self.tok.0 {
            TokenKind::Ident
                if self.is_keyword(span.text()) || self.is_imported_future_keyword(span.text()) =>
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

    fn parse_scalar_or_var(&mut self) -> Result<Expr<'source>> {
        let span = self.tok.1.clone();
        let node = match &self.tok.0 {
            TokenKind::Number => Expr::Number(span),
            TokenKind::String => Expr::String(span),
            TokenKind::RawString => Expr::RawString(span),
            TokenKind::Ident => match self.tok.1.text() {
                "null" => Expr::Null(span),
                "true" => Expr::True(span),
                "false" => Expr::False(span),
                _ => return Ok(Expr::Var(self.parse_var()?)),
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

    fn parse_compr(&mut self, delim: &str) -> Result<(Expr<'source>, Query<'source>)> {
        // Save the state.
        let state = self.clone();
        let mut span = self.tok.1.clone();

        // Parse the first expression as a ref.
        let term = match self.parse_ref() {
            Ok(e) if self.tok.1.text() == "|" => e,
            _ => {
                // Not a comprehension. Restore state.
                *self = state;
                bail!("internal - not a compr");
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
                bail!("internal - not a compr");
            }
            Err(err) => Err(err),
        }
    }

    fn parse_compr_or_array(&mut self) -> Result<Expr<'source>> {
        // Save the state.
        let mut span = self.tok.1.clone();
        self.expect("[", "while parsing array comprehension or array")?;

        let pos = self.end;
        match self.parse_compr("]") {
            Ok((term, query)) => {
                span.end = self.end;
                Ok(Expr::ArrayCompr {
                    span,
                    term: Box::new(term),
                    query,
                })
            }
            Err(_) if self.end == pos => {
                // No progress was made in parsing comprehension.
                // Parse as array.
                let mut items = vec![];
                if self.tok.1.text() != "]" {
                    items.push(self.parse_in_expr()?);
                    while self.tok.1.text() == "," {
                        self.next_token()?;
                        match self.tok.1.text() {
                            "]" => break,
                            "" if self.tok.0 == TokenKind::Eof => break,
                            _ => items.push(self.parse_in_expr()?),
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

    fn parse_compr_set_or_object(&mut self) -> Result<Expr<'source>> {
        let mut span = self.tok.1.clone();
        self.expect("{", "while parsing set, object or comprehension")?;

        let pos = self.end;
        match self.parse_compr("}") {
            Ok((term, query)) => {
                span.end = self.end;
                return Ok(Expr::SetCompr {
                    span,
                    term: Box::new(term),
                    query,
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
        // In all the cases, the first expressoin must parse successfully.
        if self.tok.1.text() == "}" {
            self.next_token()?;
            span.end = self.end;
            return Ok(Expr::Object {
                span,
                fields: vec![],
            });
        }

        let mut item_span = self.tok.1.clone();
        let first = self.parse_in_expr()?;

        if self.tok.1.text() != ":" {
            // Parse as set.
            let mut items = vec![first];
            while self.tok.1.text() == "," {
                self.next_token()?;
                match self.tok.1.text() {
                    "}" => break,
                    "" if self.tok.0 == TokenKind::Eof => break,
                    _ => items.push(self.parse_in_expr()?),
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
                    key: Box::new(first),
                    value: Box::new(term),
                    query,
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
        items.push((item_span, first, value));

        while self.tok.1.text() == "," {
            self.next_token()?;
            let item_start = self.tok.1.start;
            let key = match self.tok.1.text() {
                "}" => break,
                "" if self.tok.0 == TokenKind::Eof => break,
                _ => self.parse_in_expr()?,
            };

            let mut item_span = self.tok.1.clone();
            span.start = item_start;
            self.expect(":", "while parsing object item")?;
            let value = self.parse_in_expr()?;
            item_span.end = self.end;

            items.push((item_span, key, value));
        }

        self.expect("}", "while parsing object")?;
        span.end = self.end;

        Ok(Expr::Object {
            span,
            fields: items,
        })
    }

    fn parse_empty_set(&mut self) -> Result<Expr<'source>> {
        let mut span = self.tok.1.clone();
        self.expect("set(", "while parsing empty set")?;
        self.expect(")", "while parsing empty set")?;
        span.end = self.tok.1.end;
        Ok(Expr::Set {
            span,
            items: vec![],
        })
    }

    fn parse_parens_expr(&mut self) -> Result<Expr<'source>> {
        self.next_token()?;
        let expr = self.parse_membership_expr()?;
        self.expect(")", "while parsing parenthesized expression")?;
        //TODO: if needed introduce a parens-expr node or adjust expr's span.
        Ok(expr)
    }

    fn parse_unary_expr(&mut self) -> Result<Expr<'source>> {
        let mut span = self.tok.1.clone();
        self.next_token()?;
        let expr = self.parse_in_expr()?;
        span.end = self.end;
        Ok(Expr::UnaryExpr {
            span,
            expr: Box::new(expr),
        })
    }

    fn parse_ref(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut term = match self.tok.1.text() {
            "[" => self.parse_compr_or_array()?,
            "{" => self.parse_compr_set_or_object()?,
            "set(" => self.parse_empty_set()?,
            "(" => return self.parse_parens_expr(),
            "-" => return self.parse_unary_expr(),
            _ => self.parse_scalar_or_var()?,
        };

        let mut possible_fcn = matches!(&term, Expr::Var(_));

        loop {
            let mut span = self.tok.1.clone();
            let sep_pos = span.start;
            span.start = start;
            match self.tok.1.text() {
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
                            format!("invalid whitespace before {}", self.tok.1.text()).as_str()
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
                    term = Expr::RefDot {
                        span,
                        refr: Box::new(term),
                        field,
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
                        refr: Box::new(term),
                        index: Box::new(index),
                    };
                }
                "(" if possible_fcn => {
                    self.next_token()?;
                    let mut args = vec![self.parse_in_expr()?];
                    while self.tok.1.text() == "," {
                        self.next_token()?;
                        match self.tok.1.text() {
                            ")" => break,
                            "" if self.tok.0 == TokenKind::Eof => break,
                            _ => args.push(self.parse_in_expr()?),
                        }
                    }
                    self.expect(")", "while parsing call expr")?;
                    span.end = self.end;
                    term = Expr::Call {
                        span,
                        fcn: Box::new(term),
                        params: args,
                    };

                    // The expression can no longer be a function after the call.
                    possible_fcn = false;
                }
                _ => break,
            }
        }

        if self.in_default_value {
            if let Some((kind, span)) = match &term {
                Expr::Var(v) => Some(("var", v)),
                Expr::RefDot { span, .. } => Some(("ref", span)),
                Expr::Call { span, .. } => Some(("call", span)),
                Expr::RefBrack { span, .. } => Some(("ref", span)),
                _ => None,
            } {
                return Err(self.source.error(
                    span.line,
                    span.col,
                    format!("invalid {kind} in default value").as_str(),
                ));
            }
        }

        Ok(term)
    }

    fn parse_term(&mut self) -> Result<Expr<'source>> {
        self.parse_ref()
    }

    fn parse_mul_div_expr(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut expr = self.parse_term()?;

        loop {
            let mut span = self.tok.1.clone();
            span.start = start;
            let op = match self.tok.1.text() {
                "*" => ArithOp::Mul,
                "/" => ArithOp::Div,
                _ => return Ok(expr),
            };
            self.next_token()?;
            let right = self.parse_term()?;
            span.end = self.end;
            expr = Expr::ArithExpr {
                span,
                op,
                lhs: Box::new(expr),
                rhs: Box::new(right),
            };
        }
    }

    fn parse_arith_expr(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut expr = self.parse_mul_div_expr()?;

        loop {
            let mut span = self.tok.1.clone();
            span.start = start;
            let op = match self.tok.1.text() {
                "+" => ArithOp::Add,
                "-" => ArithOp::Sub,
                _ => return Ok(expr),
            };
            self.next_token()?;
            let right = self.parse_mul_div_expr()?;
            span.end = self.end;
            expr = Expr::ArithExpr {
                span,
                op,
                lhs: Box::new(expr),
                rhs: Box::new(right),
            };
        }
    }

    fn parse_and_expr(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut expr = self.parse_arith_expr()?;

        while self.tok.1.text() == "&" {
            let mut span = self.tok.1.clone();
            span.start = start;
            self.next_token()?;
            let right = self.parse_arith_expr()?;
            span.end = self.end;
            expr = Expr::BinExpr {
                span,
                op: BinOp::And,
                lhs: Box::new(expr),
                rhs: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_or_expr(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut expr = self.parse_and_expr()?;

        while self.tok.1.text() == "|" {
            let mut span = self.tok.1.clone();
            span.start = start;
            self.next_token()?;
            let right = self.parse_and_expr()?;
            span.end = self.end;
            expr = Expr::BinExpr {
                span,
                op: BinOp::Or,
                lhs: Box::new(expr),
                rhs: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_bool_expr(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut expr = self.parse_or_expr()?;
        loop {
            let mut span = self.tok.1.clone();
            span.start = start;
            let op = match self.tok.1.text() {
                "<" => BoolOp::Lt,
                "<=" => BoolOp::Le,
                "==" => BoolOp::Eq,
                ">=" => BoolOp::Ge,
                ">" => BoolOp::Gt,
                "!=" => BoolOp::Ne,
                _ => break,
            };
            self.next_token()?;
            let right = self.parse_or_expr()?;
            span.end = self.end;
            expr = Expr::BoolExpr {
                span,
                op,
                lhs: Box::new(expr),
                rhs: Box::new(right),
            };
        }
        Ok(expr)
    }

    fn parse_membership_tail(
        &mut self,
        start: u16,
        mut expr1: Expr<'source>,
        mut expr2: Option<Expr<'source>>,
    ) -> Result<Expr<'source>> {
        loop {
            let mut span = self.tok.1.clone();
            span.start = start;
            self.parse_future_keyword("in", false, "while parsing membership expression")?;
            let expr3 = self.parse_bool_expr()?;
            span.end = self.end;
            expr1 = Expr::Membership {
                span,
                key: Box::new(expr1),
                value: Box::new(expr2),
                collection: Box::new(expr3),
            };
            expr2 = None;

            if self.tok.1.text() != "in" {
                break;
            }
        }

        Ok(expr1)
    }

    fn parse_in_expr(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut expr = self.parse_bool_expr()?;

        while self.tok.1.text() == "in" {
            expr = self.parse_membership_tail(start, expr, None)?;
        }

        Ok(expr)
    }

    pub fn parse_membership_expr(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let mut expr = self.parse_bool_expr()?;

        if self.tok.1.text() == "," {
            self.next_token()?;
            let value = self.parse_bool_expr()?;
            expr = self.parse_membership_tail(start, expr, Some(value))?;
        }

        while self.tok.1.text() == "in" {
            expr = self.parse_membership_tail(start, expr, None)?;
        }

        Ok(expr)
    }

    fn parse_assign_expr(&mut self) -> Result<Expr<'source>> {
        let state = self.clone();
        let start = self.tok.1.start;
        let expr = self.parse_ref()?;

        let mut span = self.tok.1.clone();
        span.start = start;
        let op = match self.tok.1.text() {
            "=" => AssignOp::Eq,
            ":=" => AssignOp::ColEq,
            _ => {
                *self = state;
                return self.parse_membership_expr();
            }
        };

        self.next_token()?;
        let right = self.parse_membership_expr()?;
        span.end = self.end;
        Ok(Expr::AssignExpr {
            span,
            op,
            lhs: Box::new(expr),
            rhs: Box::new(right),
        })
    }

    fn parse_with_modifiers(&mut self) -> Result<Vec<WithModifier<'source>>> {
        let mut modifiers = vec![];
        while self.tok.1.text() == "with" {
            let mut span = self.tok.1.clone();
            self.next_token()?;
            let refr = self.parse_path_ref()?;
            self.expect("as", "while parsing with-modifier expression")?;
            let r#as = self.parse_in_expr()?;
            span.end = self.end;
            modifiers.push(WithModifier { span, refr, r#as });
        }
        Ok(modifiers)
    }

    fn parse_every_stmt(&mut self) -> Result<Literal<'source>> {
        let mut span = self.tok.1.clone();
        let context = "Failed to parse `every` statement.";
        self.parse_future_keyword("every", false, context)?;

        let key = self.parse_var()?;
        let value = match self.tok.1.text() {
            "," => {
                self.next_token()?;
                match self.parse_var() {
                    Ok(v) => Some(v),
                    Err(e) => {
                        return Err(self.source.error(
                            span.line,
                            span.col,
                            format!("Failed to parse `every` statement.\n{e}").as_str(),
                        ))
                    }
                }
            }
            _ => None,
        };

        self.parse_future_keyword("in", false, context)?;
        let domain = self.parse_bool_expr()?;
        let query_span = self.tok.1.clone();
        self.expect("{", context)?;
        let query = self.parse_query(query_span, "}")?;
        span.end = self.end;

        Ok(Literal::Every {
            span,
            key,
            value,
            domain,
            query,
        })
    }

    fn parse_some_stmt(&mut self) -> Result<Literal<'source>> {
        let mut span = self.tok.1.clone();
        self.expect("some", "while parsing some-decl")?;

        // parse any vars.
        let mut vars = vec![self.tok.1.clone()];
        let mut refs = vec![self.parse_ref()?];

        while self.tok.1.text() == "," {
            self.next_token()?;
            let mut span = self.tok.1.clone();
            refs.push(self.parse_ref()?);
            span.end = self.end;
            vars.push(span);
        }

        if self.tok.1.text() != "in" || self.future_keywords.get("in").is_none() {
            if self.tok.1.text() == "in" {
                self.warn_future_keyword();
            }
            // All the refs must be identifiers
            for (idx, ref_expr) in refs.iter().enumerate() {
                let span = &vars[idx];
                match ref_expr {
                    Expr::Var(_) => (),
                    _ => {
                        return Err(anyhow!(
                            "{}:{}:{} error: encountered `{}` while expecting identifier",
                            span.source.file,
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
            2 => (refs[0].clone(), Some(refs[1].clone())),
            1 => (refs[0].clone(), None),
            _ => {
                let span = &vars[2];
                return Err(anyhow!(
                    "{}:{}:{} error: encountered `{}` while expecting `in`",
                    span.source.file,
                    span.line,
                    span.col,
                    span.text()
                ));
            }
        };

        self.parse_future_keyword("in", false, "while parsing some-decl")?;
        let collection = self.parse_bool_expr()?; // TODO: check this
        Ok(Literal::SomeIn {
            span,
            key,
            value,
            collection,
        })
    }

    fn parse_literal(&mut self) -> Result<Literal<'source>> {
        match self.tok.1.text() {
            "some" => return self.parse_some_stmt(),
            "every" => {
                if self.future_keywords.get("every").is_some() {
                    return self.parse_every_stmt();
                }
                self.warn_future_keyword();
            }
            _ => (),
        }
        let mut span = self.tok.1.clone();
        let not_expr = if self.tok.1.text() == "not" {
            self.next_token()?;
            true
        } else {
            false
        };

        let expr = self.parse_assign_expr()?;
        span.end = self.end;
        if not_expr {
            Ok(Literal::NotExpr { span, expr })
        } else {
            Ok(Literal::Expr { span, expr })
        }
    }

    pub fn parse_literal_stmt(&mut self) -> Result<LiteralStmt<'source>> {
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

    pub fn parse_query(
        &mut self,
        mut span: Span<'source>,
        end_delim: &str,
    ) -> Result<Query<'source>> {
        let state = self.clone();
        let _is_definite_query = matches!(self.tok.1.text(), "some" | "every");

        // TODO: empty query?
        let mut literals = vec![];

        let stmt = match self.parse_literal_stmt() {
            Ok(stmt) => stmt,
            Err(e) if _is_definite_query => return Err(e),
            _ => {
                // There was error parsing the first literal
                // Restore the state and return.
                *self = state;
                return Err(anyhow!("encountered , when expecting {}", end_delim));
            }
        };

        if self.tok.1.text() == "," {
            // This is likely an array or set.
            // Restore the state.
            *self = state;
            return Err(anyhow!("encountered , when expecting {}", end_delim));
        }

        literals.push(stmt);

        loop {
            match self.tok.1.text() {
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

        self.expect(end_delim, "while parsing query")?;
        span.end = self.end;
        Ok(Query {
            span,
            stmts: literals,
        })
    }

    pub fn parse_rule_assign(&mut self) -> Result<Option<RuleAssign<'source>>> {
        let mut span = self.tok.1.clone();

        let op = match self.tok.1.text() {
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

        let expr = self.parse_membership_expr()?;
        span.end = self.end;
        Ok(Some(RuleAssign {
            span,
            op,
            value: expr,
        }))
    }

    fn parse_path_ref(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let var = self.parse_var()?;

        let mut refr = Expr::Var(var);
        loop {
            let mut span = self.tok.1.clone();
            let sep_pos = span.start;
            span.start = start;
            match self.tok.1.text() {
                "." | "[" if self.tok.1.start != self.end => {
                    bail!(
                        "{}",
                        self.source.error(
                            self.tok.1.line,
                            self.tok.1.col - 1,
                            format!("invalid whitespace before {}", self.tok.1.text()).as_str()
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
                        refr: Box::new(refr),
                        field,
                    };
                }
                "[" => {
                    self.next_token()?;
                    let index = match &self.tok.0 {
                        TokenKind::String => Expr::String(self.tok.1.clone()),
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
                        refr: Box::new(refr),
                        index: Box::new(index),
                    };
                }
                _ => break,
            }
        }

        Ok(refr)
    }

    fn check_rule_ref(&self, mut refr: &Expr) -> Result<()> {
        // Only the last term can be non-string
        loop {
            refr = match refr {
                Expr::RefDot { refr, .. } => refr,
                Expr::RefBrack { span, refr, index } => {
                    if !matches!(index.as_ref(), Expr::String(_)) {
                        return Err(self.source.error(
                            span.line,
                            span.col,
                            "only the final ref term can be non-string",
                        ));
                    }
                    refr
                }
                Expr::Var(_) => return Ok(()),
                _ => bail!("internal error: not a valid ref"),
            };
        }
    }

    fn parse_rule_ref(&mut self) -> Result<Expr<'source>> {
        let start = self.tok.1.start;
        let span = self.tok.1.clone();

        let mut term = if self.tok.0 == TokenKind::Ident {
            Expr::Var(self.parse_var()?)
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
            match self.tok.1.text() {
                // . and [ must not have any space between the previous token.
                "." | "[" if self.tok.1.start != self.end => {
                    bail!(
                        "{}",
                        self.source.error(
                            self.tok.1.line,
                            self.tok.1.col - 1,
                            format!("invalid whitespace before {}", self.tok.1.text()).as_str()
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
                        refr: Box::new(term),
                        field,
                    };
                }
                "[" => {
                    self.next_token()?;
                    let index = self.parse_membership_expr()?;
                    span.end = self.end;
                    self.expect("]", "while parsing bracketed reference")?;
                    term = Expr::RefBrack {
                        span,
                        refr: Box::new(term),
                        index: Box::new(index),
                    };
                }
                _ => break,
            }
        }

        Ok(term)
    }

    pub fn parse_rule_head(&mut self) -> Result<RuleHead<'source>> {
        let mut span = self.tok.1.clone();

        let rule_ref = self.parse_rule_ref()?;
        match self.tok.1.text() {
            "(" => {
                self.check_rule_ref(&rule_ref)?;
                self.next_token()?;
                let mut args = vec![self.parse_term()?];
                while self.tok.1.text() == "," {
                    self.next_token()?;
                    match self.tok.1.text() {
                        ")" => break,
                        "" if self.tok.0 == TokenKind::Eof => break,
                        _ => args.push(self.parse_term()?),
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
                self.check_rule_ref(&rule_ref)?;
                self.next_token()?;
                let key = self.parse_membership_expr()?;
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

                // Ensure that only the last term can be non-string.
                match &rule_ref {
                    Expr::RefBrack { refr, .. } => self.check_rule_ref(refr)?,
                    Expr::RefDot { refr, .. } => self.check_rule_ref(refr)?,
                    _ => (),
                }

                // Determine whether to create a set or a compr
                let is_set_follower = !self.is_keyword(self.tok.1.text())
                    && !self.is_imported_future_keyword(self.tok.1.text());
                if assign.is_none() && is_set_follower {
                    match &rule_ref {
                        Expr::RefBrack { refr, index, .. }
                            if matches!(refr.as_ref(), Expr::Var(_)) =>
                        {
                            return Ok(RuleHead::Set {
                                span,
                                refr: refr.as_ref().clone(),
                                key: Some(index.as_ref().clone()),
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
        self.future_keywords.get("if").is_some()
    }

    pub fn parse_query_or_literal_stmt(&mut self) -> Result<Query<'source>> {
        let state = self.clone();
        let mut span = self.tok.1.clone();

        if self.tok.1.text() == "{" {
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

    pub fn parse_rule_bodies(&mut self) -> Result<Vec<RuleBody<'source>>> {
        let mut span = self.tok.1.clone();
        let mut bodies = vec![];

        let assign = None;
        let has_query = match self.tok.1.text() {
            "if" if self.if_is_keyword() => {
                self.next_token()?;
                let query = self.parse_query_or_literal_stmt()?;
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
                self.next_token()?;
                let query = self.parse_query(span.clone(), "}")?;
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

        match self.tok.1.text() {
            "{" if has_query => self.parse_query_blocks(&mut bodies)?,
            "else" if has_query => self.parse_else_blocks(&mut bodies)?,
            _ => (),
        }

        Ok(bodies)
    }

    pub fn parse_query_blocks(&mut self, bodies: &mut Vec<RuleBody<'source>>) -> Result<()> {
        while self.tok.1.text() == "{" {
            let mut span = self.tok.1.clone();
            self.next_token()?;
            let query = self.parse_query(span.clone(), "}")?;
            span.end = self.end;
            bodies.push(RuleBody {
                span,
                assign: None,
                query,
            });
        }
        Ok(())
    }

    pub fn parse_else_blocks(&mut self, bodies: &mut Vec<RuleBody<'source>>) -> Result<()> {
        loop {
            let mut span = self.tok.1.clone();

            match self.tok.1.text() {
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

            match self.tok.1.text() {
                "if" if self.if_is_keyword() => {
                    self.next_token()?;
                    let query = self.parse_query_or_literal_stmt()?;
                    span.end = self.end;
                    bodies.push(RuleBody {
                        span,
                        assign,
                        query,
                    });
                }
                "{" => {
                    self.next_token()?;
                    let query = self.parse_query(span.clone(), "}")?;
                    span.end = self.end;
                    bodies.push(RuleBody {
                        span,
                        assign,
                        query,
                    });
                }
                _ if assign.is_none() => {
                    if self.tok.1.text() == "if" {
                        self.warn_future_keyword();
                    }
                    return Err(self.source.error(
                        self.tok.1.line,
                        self.tok.1.col,
                        "expected assignment or query after `else`",
                    ));
                }
                _ => break,
            }
        }
        Ok(())
    }

    pub fn parse_default_rule(&mut self) -> Result<Rule<'source>> {
        let mut span = self.tok.1.clone();
        self.expect("default", "while parsing default rule")?;
        let rule_ref = self.parse_rule_ref()?;

        let op = match self.tok.1.text() {
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
        self.in_default_value = true;
        let value = self.parse_term()?;
        self.in_default_value = false;
        span.end = self.end;
        Ok(Rule::Default {
            span,
            refr: rule_ref,
            op,
            value,
        })
    }

    pub fn parse_rule(&mut self) -> Result<Rule<'source>> {
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
        Ok(Rule::Spec { span, head, bodies })
    }

    fn parse_package(&mut self) -> Result<Package<'source>> {
        let mut span = self.tok.1.clone();
        self.expect("package", "Missing package declaration.")?;
        let name = self.parse_path_ref()?;
        span.end = self.end;
        Ok(Package { span, refr: name })
    }

    fn check_and_add_import(
        &self,
        import: Import<'source>,
        imports: &mut Vec<Import<'source>>,
    ) -> Result<()> {
        let comps: Vec<&str> = Self::get_path_ref_components(&import.refr)?
            .iter()
            .map(|s| s.text())
            .collect();

        for imp in imports.iter() {
            let imp_comps: Vec<&str> = Self::get_path_ref_components(&imp.refr)?
                .iter()
                .map(|s| s.text())
                .collect();

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

    fn parse_imports(&mut self) -> Result<Vec<Import<'source>>> {
        let mut imports = vec![];
        while self.tok.1.text() == "import" {
            let mut span = self.tok.1.clone();
            self.next_token()?;
            let refr = self.parse_path_ref()?;

            let comps = Self::get_path_ref_components(&refr)?;
            if !matches!(comps[0].text(), "data" | "future" | "input") {
                return Err(self.source.error(
                    comps[0].line,
                    comps[0].col,
                    "import path must begin with one of: {data, future, input}",
                ));
            }

            let is_future_kw = self.handle_import_future_keywords(&comps)?;

            let var = if self.tok.1.text() == "as" {
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

    pub fn parse(&mut self) -> Result<Module<'source>> {
        let package = self.parse_package()?;
        let imports = self.parse_imports()?;

        let mut policy = vec![];
        while self.tok.0 != TokenKind::Eof {
            policy.push(self.parse_rule()?);
        }

        Ok(Module {
            package,
            imports,
            policy,
        })
    }
}
