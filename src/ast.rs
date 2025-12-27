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
}

pub type Ref<T> = NodeRef<T>;

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub enum Expr {
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

#[derive(Debug)]
#[cfg_attr(feature = "ast", derive(serde::Serialize))]
pub struct Query {
    pub span: Span,
    pub stmts: Vec<LiteralStmt>,
    pub qidx: u32,
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
