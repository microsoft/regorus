// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::*;
use crate::{schema::*, target::Target};

use alloc::collections::BTreeMap;
use anyhow::{bail, Result};

pub struct Config {
    input: Schema,
    target: Rc<Target>,
}

#[derive(Debug)]
struct Context {
    //key: Option<Ref<Expr>>,
    value: Option<Ref<Expr>>,
    inferred_schema: Option<Schema>,
}

pub struct TypeCheck {
    rules: Map<String, Vec<Ref<Rule>>>,
    config: Rc<Config>,

    // Inference.
    //rule_types: Map<String, Type>,
    contexts: Vec<Context>,
    bindings: Map<String, Schema>,
}

impl TypeCheck {
    pub fn new(rules: Map<String, Vec<Ref<Rule>>>, config: Rc<Config>) -> Self {
        Self {
            rules,
            config,
            // rule_types: Map::default(),
            contexts: Vec::default(),
            bindings: Map::default(),
        }
    }

    fn check_chained_ref_dot_or_brack(&mut self, mut expr: &Expr) -> Result<Schema> {
        // Collect a chaing of '.field' or '["field"]'
        let mut path = vec![];
        loop {
            match expr {
                // Stop path collection upon encountering the leading variable.
                Expr::Var { span, .. } => {
                    path.push(span.clone());
                    path.reverse();
                    let v = path[0].text();
                    let mut schema = if v == "input" {
                        self.config.input.clone()
                    } else if v == "data" {
                        unimplemented!("indexing into data");
                    } else {
                        match self.bindings.get(v) {
                            Some(t) => t.clone(),
                            _ => {
                                bail!(path[0].error("no type determined"));
                            }
                        }
                    };

                    for p in &path[1..] {
                        schema = schema
                            .get_property(p.text())
                            .map_err(|e| p.error(&e.to_string()))?;
                    }
                    return Ok(schema);
                }
                // Accumulate chained . field accesses.
                Expr::RefDot { refr, field, .. } => {
                    expr = refr.as_ref();
                    path.push(field.0.clone());
                }
                Expr::RefBrack { refr, index, .. } => match index.as_ref() {
                    // refr["field"] is the same as refr.field
                    Expr::String { span, .. } => {
                        expr = refr.as_ref();
                        path.push(span.clone());
                    }
                    // Handle other forms of refr.
                    // Note, we have the choice to evaluate a non-string index
                    _ => {
                        unimplemented!("other forms of indexing");
                    }
                },
                _ => {
                    unimplemented!("complex indexing. E.g: into function call")
                }
            }
        }
    }

    fn primitive_schema(simple_type: SimpleType) -> Schema {
        Schema {
            type_: Some(Type::One(simple_type)),
            ..Schema::default()
        }
    }

    fn check_expr(&mut self, expr: &Expr) -> Result<Schema> {
        match expr {
            Expr::String { .. } | Expr::RawString { .. } => {
                Ok(Self::primitive_schema(SimpleType::String))
            }
            // TODO: Int vs number
            Expr::Number { .. } => Ok(Self::primitive_schema(SimpleType::Number)),
            Expr::Bool { .. } => Ok(Self::primitive_schema(SimpleType::Boolean)),
            Expr::Null { .. } => Ok(Self::primitive_schema(SimpleType::Null)),
            /*            Expr::Array { items, .. } => {
                let mut item_type = Type::Undefined;
                for item in items {
                    let t = self.check_expr(item)?;
                    if item_type == Type::Undefined {
                        item_type = t;
                    } else if t != item_type {
                        bail!(item.span().error(
                                    &format!("heterogenous array detected. Element has type {item_type:?}. Array has type {t:?}")));
                    }
                }
                Ok(Type::Array {
                    item_type: Box::new(item_type),
                })
            }
            Expr::Set { items, .. } => {
                let mut item_type = Type::Undefined;
                for item in items {
                    let t = self.check_expr(item)?;
                    if item_type == Type::Undefined {
                        item_type = t;
                    } else if t != item_type {
                        bail!(item.span().error(
                                    &format!("heterogenous array detected. Element has type {item_type:?}. Set has type {t:?}")));
                    }
                }
                Ok(Type::Set {
                    item_type: Box::new(item_type),
                })
            }
            Expr::Object { fields, .. } => {
                let mut inferred_fields = BTreeMap::default();
                for (_, key, value) in fields {
                    let key_schema = self.check_expr(key)?;
                    let value_schema = self.check_expr(value)?;
            if let Some(Type::One(SimpleType::String)) = &key_type {
            } else {
                        bail!(key
                            .span()
                            .error(&format!("non string key type. Key has type {key_type:?}")));
                    }

                    match key.as_ref() {
                        Expr::String { value, .. } | Expr::RawString { value, .. } => {
                            if let Value::String(s) = &value {
                                inferred_fields.insert(s.to_string(), value_schema);
                            }
                        }
                        _ => unimplemented!(),
                    }
                }
                Ok(
                    fields: Rc::new(inferred_fields),
                })
            }
            Expr::UnaryExpr { span, expr, .. } => {
                let t = self.check_expr(expr)?;
                if t != Type::Number {
                    bail!(span.error(&format!(
                        "unary minus requires Number operand. Operand has {t:?} type."
                    )))
                }
                Ok(t)
            }

            Expr::BinExpr { span, lhs, rhs, .. } => {
                let lhs_t = self.check_expr(lhs)?;
                let rhs_t = self.check_expr(rhs)?;
                if lhs_t != rhs_t {
                    bail!(span.error(&format!("Operand type mismatch. {lhs_t:?} != {rhs_t:?}.")))
                }
                match lhs_t {
                    Type::Set { .. } => Ok(rhs_t),
                    _ => bail!(
                        span.error(&format!("Operand type must be set. Got {rhs_t:?} instead"))
                    ),
                }
            }

            Expr::BoolExpr { span, lhs, rhs, .. } => {
                let lhs_t = self.check_expr(lhs)?;
                let rhs_t = self.check_expr(rhs)?;
                if lhs_t != rhs_t {
                    bail!(span.error(&format!("Operand type mismatch. {lhs_t:?} != {rhs_t:?}.")))
                }
                // TODO: Should we limit types here
                match &lhs_t {
                    Type::String | Type::Number => Ok(Type::Bool),
                    _ => {
                        bail!(span.error(&format!("type must be string or number. Got {lhs_t:?}")))
                    }
                }
            }
            Expr::ArithExpr {
                span, op, lhs, rhs, ..
            } => {
                let lhs_t = self.check_expr(lhs)?;
                let rhs_t = self.check_expr(rhs)?;
                if lhs_t != rhs_t {
                    bail!(span.error(&format!("Operand type mismatch. {lhs_t:?} != {rhs_t:?}.")))
                }
                if let Type::Set { .. } = &lhs_t {
                    if op != &ArithOp::Sub {
                        bail!(span.error("Only - is supported for set operands."))
                    }
                } else if lhs_t != Type::Number {
                    bail!(span.error(&format!(
                        "Arithmetic can only be done on numbers. Got {lhs_t:?}"
                    )));
                }

                Ok(Type::Number)
            }
            Expr::RefDot { .. } | Expr::RefBrack { .. } | Expr::Var { .. } => {
                self.check_chained_ref_dot_or_brack(expr)
            }
            Expr::Membership {
                span,
                key,
                value,
                collection,
                ..
            } => {
                let col_type = self.check_expr(collection)?;
                let val_type = self.check_expr(value)?;
                if key.is_some() {
                    unimplemented!("key membership");
                }
                match &col_type {
                    Type::Array { item_type, .. } | Type::Set { item_type, .. }
                        if item_type.as_ref() != &val_type =>
                    {
                        bail!(span.error(&format!("Operand type mismatch. Collection has type {col_type:?}. Element has type {val_type:?}")))
                    }
                    Type::Array { .. } | Type::Set { .. } => Ok(Type::Bool),
                    _ => unimplemented!(),
                }
            }

            Expr::AssignExpr { lhs, rhs, .. } => {
                if let Expr::Var { span: lhs, .. } = lhs.as_ref() {
                    // TODO: = vs :=
                    let t = self.check_expr(rhs)?;
                    self.bindings.insert(lhs.text().to_string(), t.clone());
                    Ok(t)
                } else {
                    unimplemented!("complex assignment");
                }
            }*/
            _ => unimplemented!(),
        }
    }

    fn check_stmt(&mut self, stmt: &LiteralStmt) -> Result<()> {
        // TODO: with mod
        match &stmt.literal {
            Literal::Expr { expr, .. } => self.check_expr(expr)?,
            Literal::NotExpr { expr, .. } => self.check_expr(expr)?,
            _ => unimplemented!(),
        };
        Ok(())
    }

    fn check_query(&mut self, query: &Query) -> Result<()> {
        // TODO: Correct order.
        for stmt in &query.stmts {
            self.check_stmt(stmt)?;
        }

        // TODO: avoid unwrap.
        let mut ctx = self.contexts.pop().unwrap();
        if let Some(value) = &ctx.value {
            let vt = self.check_expr(value)?;
            if let Some(pvt) = &ctx.inferred_schema {
                if pvt != &vt {
                    bail!(value
                        .span()
                        .error(&format!("Multiple types inferred. {pvt:?} and {vt:?}")));
                }
            } else {
                ctx.inferred_schema = Some(vt);
            }
        }

        self.contexts.push(ctx);
        Ok(())
    }

    fn check_rule_body(&mut self, name: &String, body: &RuleBody) -> Result<()> {
        self.check_query(&body.query)?;
        let ctx = self.contexts.last().unwrap();
        let it = ctx
            .inferred_schema
            .clone()
            .unwrap_or(Self::primitive_schema(SimpleType::Boolean));

        if let Some(t) = self.config.target.effects.get(name) {
            if t != &it {
                bail!(body.span.error(&format!(
                    "Rule must produce {t:?}. It produces {it:?} instead.",
                )));
            }
        } else {
            std::eprintln!("no type specified in target for {name}");
        }
        Ok(())
    }

    fn check_rule(&mut self, name: &String, rule: &Ref<Rule>) -> Result<Schema> {
        let contexts = core::mem::take(&mut self.contexts);
        let bindings = core::mem::take(&mut self.bindings);

        match rule.as_ref() {
            Rule::Spec { head, bodies, .. } => {
                let (_, mut assign) = match &head {
                    RuleHead::Compr { refr, assign, .. } => (refr.clone(), assign),
                    _ => unimplemented!(),
                };

                for body in bodies {
                    if body.assign.is_some() {
                        assign = &body.assign;
                    }
                    let rule_rhs = assign.as_ref().map(|assign| assign.value.clone());

                    self.contexts.clear();
                    self.contexts.push(Context {
                        // rule_lhs: rule_lhs.clone(),
                        // key: None,
                        value: rule_rhs.clone(),
                        inferred_schema: None,
                    });
                    self.check_rule_body(name, body)?;
                }
            }
            _ => unimplemented!(),
        }

        self.contexts = contexts;
        self.bindings = bindings;
        Ok(Schema::default())
    }

    fn check_rules(&mut self, name: &String, rules: &[Ref<Rule>]) -> Result<()> {
        for rule in rules {
            let _t = self.check_rule(name, rule)?;
            // TODO: Recursion.
            // TODO: Rule heads with vars
        }

        Ok(())
    }

    pub fn check(&mut self) -> Result<()> {
        for (name, rules) in self.rules.clone().iter() {
            self.check_rules(name, rules)?;
        }
        Ok(())
    }
}
