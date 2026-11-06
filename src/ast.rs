// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::lexer::*;
use crate::value::Value;
use crate::*;

use core::{cmp, fmt, ops::Deref};

#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum BinOp {
    Intersection,
    Union,
}

#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum BoolOp {
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Ne,
}

#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum AssignOp {
    Eq,
    ColEq,
}

#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct NodeRef<T> {
    #[cfg_attr(feature = "ast", serde(flatten))]
    r: Rc<T>,
}

impl<T> Clone for NodeRef<T> {
    fn clone(&self) -> Self {
        Self { r: self.r.clone() }
    }
}

impl<T: fmt::Debug> fmt::Debug for NodeRef<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.r.as_ref().fmt(f)
    }
}

impl<T> cmp::PartialEq for NodeRef<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::as_ptr(&self.r).eq(&Rc::as_ptr(&other.r))
    }
}

impl<T> cmp::Eq for NodeRef<T> {}

impl<T> cmp::Ord for NodeRef<T> {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        Rc::as_ptr(&self.r).cmp(&Rc::as_ptr(&other.r))
    }
}

impl<T> cmp::PartialOrd for NodeRef<T> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Deref for NodeRef<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.r
    }
}

impl<T> AsRef<T> for NodeRef<T> {
    fn as_ref(&self) -> &T {
        self.deref()
    }
}

impl<T> NodeRef<T> {
    pub fn new(t: T) -> Self {
        Self { r: Rc::new(t) }
    }

    fn into_inner(self) -> Option<T> {
        Rc::into_inner(self.r)
    }
}

pub type Ref<T> = NodeRef<T>;

// Keep the field order shared by the enum and its checked diagnostic/serde entry points.
macro_rules! define_expr {
    ($( $(#[$attribute:meta])* $variant:ident { $( $field:ident: $ty:ty, )* }, )*) => {
        pub enum Expr {
            $( $(#[$attribute])* $variant { $( $field: $ty, )* }, )*
        }

        impl fmt::Debug for Expr {
            fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                if let Err(error) = self.check_depth() {
                    return write!(formatter, "<Expr cannot be formatted: {error}>");
                }
                match *self {
                    $( $(#[$attribute])* Self::$variant { $( ref $field, )* } => {
                        formatter.debug_struct(stringify!($variant))
                            $(.field(stringify!($field), $field))*
                            .finish()
                    }, )*
                }
            }
        }

        #[cfg(feature = "ast")]
        impl serde::Serialize for Expr {
            fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                self.check_depth().map_err(<S::Error as serde::ser::Error>::custom)?;
                let variants = [$( $(#[$attribute])* stringify!($variant), )*];
                match *self {
                    $( $(#[$attribute])* Self::$variant { $( ref $field, )* } => {
                        let index = variants.iter().position(|name| *name == stringify!($variant))
                            .and_then(|index| u32::try_from(index).ok())
                            .ok_or_else(|| <S::Error as serde::ser::Error>::custom("invalid expression variant"))?;
                        let mut node = serializer.serialize_struct_variant(
                            "Expr", index, stringify!($variant), [$(stringify!($field)),*].len()
                        )?;
                        $(serde::ser::SerializeStructVariant::serialize_field(
                            &mut node, stringify!($field), $field
                        )?;)*
                        serde::ser::SerializeStructVariant::end(node)
                    }, )*
                }
            }
        }
    };
}

define_expr! {
    // Simple items that only have a span as content.
    String {
        span: Span,
        value: Value,
        eidx: u32,
    },

    RawString {
        span: Span,
        value: Value,
        eidx: u32,
    },

    Number {
        span: Span,
        value: Value,
        eidx: u32,
    },

    Bool {
        span: Span,
        value: Value,
        eidx: u32,
    },

    Null {
        span: Span,
        value: Value,
        eidx: u32,
    },

    Var {
        span: Span,
        value: Value,
        eidx: u32,
    },

    // array
    Array {
        span: Span,
        items: Vec<Ref<Expr>>,
        eidx: u32,
    },

    // set
    Set {
        span: Span,
        items: Vec<Ref<Expr>>,
        eidx: u32,
    },

    Object {
        span: Span,
        fields: Vec<(Span, Ref<Expr>, Ref<Expr>)>,
        eidx: u32,
    },

    // Comprehensions
    ArrayCompr {
        span: Span,
        term: Ref<Expr>,
        query: Ref<Query>,
        eidx: u32,
    },

    SetCompr {
        span: Span,
        term: Ref<Expr>,
        query: Ref<Query>,
        eidx: u32,
    },

    ObjectCompr {
        span: Span,
        key: Ref<Expr>,
        value: Ref<Expr>,
        query: Ref<Query>,
        eidx: u32,
    },

    Call {
        span: Span,
        fcn: Ref<Expr>,
        params: Vec<Ref<Expr>>,
        eidx: u32,
    },

    UnaryExpr {
        span: Span,
        expr: Ref<Expr>,
        eidx: u32,
    },

    // ref
    RefDot {
        span: Span,
        refr: Ref<Expr>,
        field: (Span, Value),
        eidx: u32,
    },

    RefBrack {
        span: Span,
        refr: Ref<Expr>,
        index: Ref<Expr>,
        eidx: u32,
    },

    // Infix expressions
    BinExpr {
        span: Span,
        op: BinOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
        eidx: u32,
    },

    BoolExpr {
        span: Span,
        op: BoolOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
        eidx: u32,
    },

    ArithExpr {
        span: Span,
        op: ArithOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
        eidx: u32,
    },

    AssignExpr {
        span: Span,
        op: AssignOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
        eidx: u32,
    },

    Membership {
        span: Span,
        key: Option<Ref<Expr>>,
        value: Ref<Expr>,
        collection: Ref<Expr>,
        eidx: u32,
    },

    #[cfg(feature = "rego-extensions")]
    OrExpr {
        span: Span,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
        eidx: u32,
    },
}

impl Expr {
    pub(crate) const MAX_DEPTH: usize = 32;

    pub(crate) fn check_depth(&self) -> anyhow::Result<()> {
        check_ast_depth(AstNode::Expr(self))
    }

    fn detach_children(&mut self, pending: &mut Vec<OwnedAstNode>) {
        fn expression(child: &mut Ref<Expr>, pending: &mut Vec<OwnedAstNode>) {
            let placeholder = Ref::new(Expr::Null {
                span: child.span().clone(),
                value: Value::Null,
                eidx: 0,
            });
            pending.push(OwnedAstNode::Expr(core::mem::replace(child, placeholder)));
        }
        fn query(child: &mut Ref<Query>, pending: &mut Vec<OwnedAstNode>) {
            let placeholder = Ref::new(Query {
                span: child.span.clone(),
                stmts: Vec::new(),
                qidx: 0,
            });
            pending.push(OwnedAstNode::Query(core::mem::replace(child, placeholder)));
        }
        match *self {
            Self::Array { ref mut items, .. } | Self::Set { ref mut items, .. } => {
                pending.extend(core::mem::take(items).into_iter().map(OwnedAstNode::Expr));
            }
            Self::Object { ref mut fields, .. } => {
                for (_, key, value) in core::mem::take(fields) {
                    pending.push(OwnedAstNode::Expr(key));
                    pending.push(OwnedAstNode::Expr(value));
                }
            }
            Self::Call {
                ref mut fcn,
                ref mut params,
                ..
            } => {
                expression(fcn, pending);
                pending.extend(core::mem::take(params).into_iter().map(OwnedAstNode::Expr));
            }
            Self::UnaryExpr { ref mut expr, .. } => expression(expr, pending),
            Self::RefDot { ref mut refr, .. } => expression(refr, pending),
            Self::RefBrack {
                ref mut refr,
                ref mut index,
                ..
            } => {
                expression(refr, pending);
                expression(index, pending);
            }
            Self::BinExpr {
                ref mut lhs,
                ref mut rhs,
                ..
            }
            | Self::BoolExpr {
                ref mut lhs,
                ref mut rhs,
                ..
            }
            | Self::ArithExpr {
                ref mut lhs,
                ref mut rhs,
                ..
            }
            | Self::AssignExpr {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                expression(lhs, pending);
                expression(rhs, pending);
            }
            #[cfg(feature = "rego-extensions")]
            Self::OrExpr {
                ref mut lhs,
                ref mut rhs,
                ..
            } => {
                expression(lhs, pending);
                expression(rhs, pending);
            }
            Self::Membership {
                ref mut key,
                ref mut value,
                ref mut collection,
                ..
            } => {
                if let Some(key) = key.take() {
                    pending.push(OwnedAstNode::Expr(key));
                }
                expression(value, pending);
                expression(collection, pending);
            }
            Self::ArrayCompr {
                ref mut term,
                query: ref mut child_query,
                ..
            }
            | Self::SetCompr {
                ref mut term,
                query: ref mut child_query,
                ..
            } => {
                expression(term, pending);
                query(child_query, pending);
            }
            Self::ObjectCompr {
                ref mut key,
                ref mut value,
                query: ref mut child_query,
                ..
            } => {
                expression(key, pending);
                expression(value, pending);
                query(child_query, pending);
            }
            _ => {}
        }
    }
}

enum AstNode<'a> {
    Expr(&'a Expr),
    Query(&'a Query),
}

fn check_ast_depth(root: AstNode<'_>) -> anyhow::Result<()> {
    let mut pending = alloc::vec![(root, 1_usize)];
    while let Some((node, depth)) = pending.pop() {
        let span = match node {
            AstNode::Expr(expr) => expr.span(),
            AstNode::Query(query) => &query.span,
        };
        if depth > Expr::MAX_DEPTH {
            anyhow::bail!(span.error("expression nesting too deep (>32)"));
        }
        let next = depth.saturating_add(1);
        match node {
            AstNode::Expr(expr) => {
                let mut expression = |child| pending.push((AstNode::Expr(child), next));
                match *expr {
                    Expr::Array { ref items, .. } | Expr::Set { ref items, .. } => {
                        for item in items {
                            expression(item);
                        }
                    }
                    Expr::Object { ref fields, .. } => {
                        for field in fields {
                            expression(&field.1);
                            expression(&field.2);
                        }
                    }
                    Expr::Call {
                        ref fcn,
                        ref params,
                        ..
                    } => {
                        expression(fcn);
                        for param in params {
                            expression(param);
                        }
                    }
                    Expr::UnaryExpr { ref expr, .. } => expression(expr),
                    Expr::RefDot { ref refr, .. } => expression(refr),
                    Expr::RefBrack {
                        ref refr,
                        ref index,
                        ..
                    } => {
                        expression(refr);
                        expression(index);
                    }
                    Expr::BinExpr {
                        ref lhs, ref rhs, ..
                    }
                    | Expr::BoolExpr {
                        ref lhs, ref rhs, ..
                    }
                    | Expr::ArithExpr {
                        ref lhs, ref rhs, ..
                    }
                    | Expr::AssignExpr {
                        ref lhs, ref rhs, ..
                    } => {
                        expression(lhs);
                        expression(rhs);
                    }
                    #[cfg(feature = "rego-extensions")]
                    Expr::OrExpr {
                        ref lhs, ref rhs, ..
                    } => {
                        expression(lhs);
                        expression(rhs);
                    }
                    Expr::Membership {
                        ref key,
                        ref value,
                        ref collection,
                        ..
                    } => {
                        if let Some(ref key) = *key {
                            expression(key);
                        }
                        expression(value);
                        expression(collection);
                    }
                    Expr::ArrayCompr {
                        ref term,
                        ref query,
                        ..
                    }
                    | Expr::SetCompr {
                        ref term,
                        ref query,
                        ..
                    } => {
                        expression(term);
                        pending.push((AstNode::Query(query), next));
                    }
                    Expr::ObjectCompr {
                        ref key,
                        ref value,
                        ref query,
                        ..
                    } => {
                        expression(key);
                        expression(value);
                        pending.push((AstNode::Query(query), next));
                    }
                    _ => {}
                }
            }
            AstNode::Query(root_query) => {
                for stmt in &root_query.stmts {
                    for modifier in &stmt.with_mods {
                        pending.push((AstNode::Expr(&modifier.refr), next));
                        pending.push((AstNode::Expr(&modifier.r#as), next));
                    }
                    match stmt.literal {
                        Literal::Expr { ref expr, .. } | Literal::NotExpr { ref expr, .. } => {
                            pending.push((AstNode::Expr(expr), next));
                        }
                        Literal::SomeIn {
                            ref key,
                            ref value,
                            ref collection,
                            ..
                        } => {
                            if let Some(ref key) = *key {
                                pending.push((AstNode::Expr(key), next));
                            }
                            pending.push((AstNode::Expr(value), next));
                            pending.push((AstNode::Expr(collection), next));
                        }
                        Literal::Every {
                            ref domain,
                            ref query,
                            ..
                        } => {
                            pending.push((AstNode::Expr(domain), next));
                            pending.push((AstNode::Query(query), next));
                        }
                        Literal::SomeVars { .. } => {}
                    }
                }
            }
        }
        crate::utils::limits::check_memory_limit_if_needed()?;
    }
    Ok(())
}

enum OwnedAstNode {
    Expr(Ref<Expr>),
    Query(Ref<Query>),
}

fn release_ast(pending: &mut Vec<OwnedAstNode>) {
    while let Some(node) = pending.pop() {
        match node {
            OwnedAstNode::Expr(reference) => {
                if let Some(mut expression) = reference.into_inner() {
                    expression.detach_children(pending);
                }
            }
            OwnedAstNode::Query(reference) => {
                if let Some(mut query) = reference.into_inner() {
                    query.detach_children(pending);
                }
            }
        }
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach_children(&mut pending);
        release_ast(&mut pending);
    }
}

impl Expr {
    pub const fn span(&self) -> &Span {
        match *self {
            Self::String { ref span, .. }
            | Self::RawString { ref span, .. }
            | Self::Number { ref span, .. }
            | Self::Bool { ref span, .. }
            | Self::Null { ref span, .. }
            | Self::Var { ref span, .. }
            | Self::Array { ref span, .. }
            | Self::Set { ref span, .. }
            | Self::Object { ref span, .. }
            | Self::ArrayCompr { ref span, .. }
            | Self::SetCompr { ref span, .. }
            | Self::ObjectCompr { ref span, .. }
            | Self::Call { ref span, .. }
            | Self::UnaryExpr { ref span, .. }
            | Self::RefDot { ref span, .. }
            | Self::RefBrack { ref span, .. }
            | Self::BinExpr { ref span, .. }
            | Self::BoolExpr { ref span, .. }
            | Self::ArithExpr { ref span, .. }
            | Self::AssignExpr { ref span, .. }
            | Self::Membership { ref span, .. } => span,
            #[cfg(feature = "rego-extensions")]
            Self::OrExpr { ref span, .. } => span,
        }
    }

    pub const fn eidx(&self) -> u32 {
        match *self {
            Self::String { eidx, .. }
            | Self::RawString { eidx, .. }
            | Self::Number { eidx, .. }
            | Self::Bool { eidx, .. }
            | Self::Null { eidx, .. }
            | Self::Var { eidx, .. }
            | Self::Array { eidx, .. }
            | Self::Set { eidx, .. }
            | Self::Object { eidx, .. }
            | Self::ArrayCompr { eidx, .. }
            | Self::SetCompr { eidx, .. }
            | Self::ObjectCompr { eidx, .. }
            | Self::Call { eidx, .. }
            | Self::UnaryExpr { eidx, .. }
            | Self::RefDot { eidx, .. }
            | Self::RefBrack { eidx, .. }
            | Self::BinExpr { eidx, .. }
            | Self::BoolExpr { eidx, .. }
            | Self::ArithExpr { eidx, .. }
            | Self::AssignExpr { eidx, .. }
            | Self::Membership { eidx, .. } => eidx,
            #[cfg(feature = "rego-extensions")]
            Self::OrExpr { eidx, .. } => eidx,
        }
    }
}

#[cfg(test)]
mod reference_ownership_tests {
    #![allow(clippy::panic_in_result_fn)]

    use super::*;
    use anyhow::Result;

    fn source_span() -> Result<Span> {
        let source = Source::from_contents("ast-drop.rego".to_string(), "root".to_string())?;
        Ok(Span {
            source,
            line: 1,
            col: 1,
            start: 0,
            end: 4,
        })
    }

    fn variable(span: Span, name: &str) -> Expr {
        Expr::Var {
            span,
            value: Value::from(name),
            eidx: 0,
        }
    }

    fn deep_brack_chain(span: &Span, depth: usize) -> Ref<Expr> {
        let mut reference = Ref::new(variable(span.clone(), "root"));
        for _ in 0..depth {
            reference = Ref::new(Expr::RefBrack {
                span: span.clone(),
                refr: reference,
                index: Ref::new(variable(span.clone(), "index")),
                eidx: 0,
            });
        }
        reference
    }

    fn deep_refdot_chain(span: &Span, depth: usize) -> Ref<Expr> {
        let mut reference = Ref::new(variable(span.clone(), "root"));
        for _ in 0..depth {
            reference = Ref::new(Expr::RefDot {
                span: span.clone(),
                refr: reference,
                field: (span.clone(), Value::from("field")),
                eidx: 0,
            });
        }
        reference
    }

    #[test]
    fn plain_expression_references_keep_their_shared_owner() -> Result<()> {
        let reference = Ref::new(variable(source_span()?, "root"));
        let clone = reference.clone();

        assert_eq!(reference, clone);
        drop(reference);
        assert!(matches!(clone.as_ref(), Expr::Var { .. }));
        drop(clone);

        Ok(())
    }

    #[test]
    fn refdot_drop_preserves_a_shared_reference_until_its_final_owner() -> Result<()> {
        let span = source_span()?;
        let child = Ref::new(variable(span.clone(), "root"));
        let weak = Rc::downgrade(&child.r);
        let retained = child.clone();
        let identity = Rc::as_ptr(&child.r);
        let parent = Expr::RefDot {
            span: span.clone(),
            refr: child,
            field: (span, Value::from("field")),
            eidx: 0,
        };

        drop(parent);
        assert_eq!(identity, Rc::as_ptr(&retained.r));
        assert!(weak.upgrade().is_some());
        drop(retained);
        assert!(weak.upgrade().is_none());

        Ok(())
    }

    #[test]
    fn deep_shared_refdot_preserves_identity_until_the_final_owner() -> Result<()> {
        const DEPTH: usize = 20_000;

        let span = source_span()?;
        let child = deep_refdot_chain(&span, DEPTH);
        let weak = Rc::downgrade(&child.r);
        let retained = child.clone();
        let identity = Rc::as_ptr(&child.r);
        let parent = Expr::RefDot {
            span: span.clone(),
            refr: child,
            field: (span, Value::from("parent")),
            eidx: 0,
        };

        drop(parent);
        assert_eq!(identity, Rc::as_ptr(&retained.r));
        assert!(weak.upgrade().is_some());
        drop(retained);
        assert!(weak.upgrade().is_none());

        Ok(())
    }

    #[cfg(feature = "arc")]
    #[test]
    fn concurrent_deep_shared_refdot_final_release_drops_iteratively() -> Result<()> {
        const DEPTH: usize = 20_000;
        const OWNER_COUNT: usize = 8;

        let span = source_span()?;
        let child = deep_refdot_chain(&span, DEPTH);
        let weak = Rc::downgrade(&child.r);
        let mut parents = Vec::with_capacity(OWNER_COUNT);
        for _ in 0..OWNER_COUNT {
            parents.push(Expr::RefDot {
                span: span.clone(),
                refr: child.clone(),
                field: (span.clone(), Value::from("parent")),
                eidx: 0,
            });
        }
        drop(child);

        let barrier = std::sync::Barrier::new(OWNER_COUNT);
        std::thread::scope(|scope| {
            for parent in parents {
                let barrier = &barrier;
                scope.spawn(move || {
                    barrier.wait();
                    drop(parent);
                });
            }
        });

        assert!(weak.upgrade().is_none());
        Ok(())
    }

    #[test]
    fn deeply_bracketed_reference_and_index_drop_iteratively() -> Result<()> {
        const DEPTH: usize = 20_000;

        let span = source_span()?;
        let root = Ref::new(Expr::RefBrack {
            span: span.clone(),
            refr: deep_brack_chain(&span, DEPTH),
            index: deep_brack_chain(&span, DEPTH),
            eidx: 0,
        });

        drop(root);
        Ok(())
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum Literal {
    SomeVars {
        span: Span,
        vars: Vec<Span>,
    },
    SomeIn {
        span: Span,
        key: Option<Ref<Expr>>,
        value: Ref<Expr>,
        collection: Ref<Expr>,
    },
    Expr {
        span: Span,
        expr: Ref<Expr>,
    },
    NotExpr {
        span: Span,
        expr: Ref<Expr>,
    },
    Every {
        span: Span,
        key: Option<Span>,
        value: Span,
        domain: Ref<Expr>,
        query: Ref<Query>,
    },
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct WithModifier {
    pub span: Span,
    pub refr: Ref<Expr>,
    pub r#as: Ref<Expr>,
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct LiteralStmt {
    pub span: Span,
    pub literal: Literal,
    #[cfg_attr(feature = "ast", serde(skip_serializing_if = "Vec::is_empty"))]
    pub with_mods: Vec<WithModifier>,
    pub sidx: u32,
}

pub struct Query {
    pub span: Span,
    pub stmts: Vec<LiteralStmt>,
    pub qidx: u32,
}

impl fmt::Debug for Query {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Err(error) = self.check_depth() {
            return write!(formatter, "<Query cannot be formatted: {error}>");
        }
        formatter
            .debug_struct("Query")
            .field("span", &self.span)
            .field("stmts", &self.stmts)
            .field("qidx", &self.qidx)
            .finish()
    }
}

#[cfg(feature = "ast")]
impl serde::Serialize for Query {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.check_depth()
            .map_err(<S::Error as serde::ser::Error>::custom)?;
        let mut query = serializer.serialize_struct("Query", 3)?;
        serde::ser::SerializeStruct::serialize_field(&mut query, "span", &self.span)?;
        serde::ser::SerializeStruct::serialize_field(&mut query, "stmts", &self.stmts)?;
        serde::ser::SerializeStruct::serialize_field(&mut query, "qidx", &self.qidx)?;
        serde::ser::SerializeStruct::end(query)
    }
}

impl Query {
    pub(crate) fn check_depth(&self) -> anyhow::Result<()> {
        check_ast_depth(AstNode::Query(self))
    }

    fn detach_children(&mut self, pending: &mut Vec<OwnedAstNode>) {
        for stmt in core::mem::take(&mut self.stmts) {
            for modifier in stmt.with_mods {
                pending.push(OwnedAstNode::Expr(modifier.refr));
                pending.push(OwnedAstNode::Expr(modifier.r#as));
            }
            match stmt.literal {
                Literal::Expr { expr, .. } | Literal::NotExpr { expr, .. } => {
                    pending.push(OwnedAstNode::Expr(expr));
                }
                Literal::SomeIn {
                    key,
                    value,
                    collection,
                    ..
                } => {
                    if let Some(key) = key {
                        pending.push(OwnedAstNode::Expr(key));
                    }
                    pending.push(OwnedAstNode::Expr(value));
                    pending.push(OwnedAstNode::Expr(collection));
                }
                Literal::Every { domain, query, .. } => {
                    pending.push(OwnedAstNode::Expr(domain));
                    pending.push(OwnedAstNode::Query(query));
                }
                Literal::SomeVars { .. } => {}
            }
        }
    }
}

impl Drop for Query {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.detach_children(&mut pending);
        release_ast(&mut pending);
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct RuleAssign {
    pub span: Span,
    pub op: AssignOp,
    pub value: Ref<Expr>,
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct RuleBody {
    pub span: Span,
    pub assign: Option<RuleAssign>,
    /// True when this body was introduced by an `else` clause. Unlike
    /// independent legacy query blocks, else bodies are mutually exclusive.
    pub is_else: bool,
    pub query: Ref<Query>,
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum RuleHead {
    Compr {
        span: Span,
        refr: Ref<Expr>,
        assign: Option<RuleAssign>,
    },
    Set {
        span: Span,
        refr: Ref<Expr>,
        key: Option<Ref<Expr>>,
    },
    Func {
        span: Span,
        refr: Ref<Expr>,
        args: Vec<Ref<Expr>>,
        assign: Option<RuleAssign>,
    },
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum Rule {
    Spec {
        span: Span,
        head: RuleHead,
        bodies: Vec<RuleBody>,
    },
    Default {
        span: Span,
        refr: Ref<Expr>,
        args: Vec<Ref<Expr>>,
        op: AssignOp,
        value: Ref<Expr>,
    },
}

impl Rule {
    pub const fn span(&self) -> &Span {
        match *self {
            Self::Spec { ref span, .. } | Self::Default { ref span, .. } => span,
        }
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct Package {
    pub span: Span,
    pub refr: Ref<Expr>,
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct Import {
    pub span: Span,
    pub refr: Ref<Expr>,
    #[cfg_attr(feature = "ast", serde(skip_serializing_if = "Option::is_none"))]
    pub r#as: Option<Span>,
}

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct Module {
    pub package: Package,
    pub imports: Vec<Import>,
    #[cfg_attr(feature = "ast", serde(rename(serialize = "rules")))]
    pub policy: Vec<Ref<Rule>>,
    pub rego_v1: bool,
    // Target name if specified via __target__ rule
    #[cfg_attr(feature = "ast", serde(skip_serializing_if = "Option::is_none"))]
    pub target: Option<String>,
    // Number of expressions in the module.
    pub num_expressions: u32,
    // Number of statements in the module.
    pub num_statements: u32,
    // Number of queries in the module.
    pub num_queries: u32,
}

pub type ExprRef = Ref<Expr>;
