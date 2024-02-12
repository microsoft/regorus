// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::lexer::*;
use crate::Rc;

use std::ops::Deref;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum BinOp {
    And,
    Or,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum BoolOp {
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Ne,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AssignOp {
    Eq,
    ColEq,
}

pub struct NodeRef<T> {
    r: Rc<T>,
}

impl<T> Clone for NodeRef<T> {
    fn clone(&self) -> Self {
        Self { r: self.r.clone() }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for NodeRef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.r.as_ref().fmt(f)
    }
}

impl<T> std::cmp::PartialEq for NodeRef<T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::as_ptr(&self.r).eq(&Rc::as_ptr(&other.r))
    }
}

impl<T> std::cmp::Eq for NodeRef<T> {}

impl<T> std::cmp::Ord for NodeRef<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Rc::as_ptr(&self.r).cmp(&Rc::as_ptr(&other.r))
    }
}

impl<T> std::cmp::PartialOrd for NodeRef<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
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
pub enum Expr {
    // Simple items that only have a span as content.
    String(Span),
    RawString(Span),
    Number(Span),
    True(Span),
    False(Span),
    Null(Span),
    Var(Span),

    // array
    Array {
        span: Span,
        items: Vec<Ref<Expr>>,
    },

    // set
    Set {
        span: Span,
        items: Vec<Ref<Expr>>,
    },

    Object {
        span: Span,
        fields: Vec<(Span, Ref<Expr>, Ref<Expr>)>,
    },

    // Comprehensions
    ArrayCompr {
        span: Span,
        term: Ref<Expr>,
        query: Ref<Query>,
    },

    SetCompr {
        span: Span,
        term: Ref<Expr>,
        query: Ref<Query>,
    },

    ObjectCompr {
        span: Span,
        key: Ref<Expr>,
        value: Ref<Expr>,
        query: Ref<Query>,
    },

    Call {
        span: Span,
        fcn: Ref<Expr>,
        params: Vec<Ref<Expr>>,
    },

    UnaryExpr {
        span: Span,
        expr: Ref<Expr>,
    },

    // ref
    RefDot {
        span: Span,
        refr: Ref<Expr>,
        field: Span,
    },

    RefBrack {
        span: Span,
        refr: Ref<Expr>,
        index: Ref<Expr>,
    },

    // Infix expressions
    BinExpr {
        span: Span,
        op: BinOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
    },
    BoolExpr {
        span: Span,
        op: BoolOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
    },

    ArithExpr {
        span: Span,
        op: ArithOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
    },

    AssignExpr {
        span: Span,
        op: AssignOp,
        lhs: Ref<Expr>,
        rhs: Ref<Expr>,
    },

    Membership {
        span: Span,
        key: Option<Ref<Expr>>,
        value: Ref<Expr>,
        collection: Ref<Expr>,
    },
}

impl Expr {
    pub fn span(&self) -> &Span {
        use Expr::*;
        match self {
            String(s) | RawString(s) | Number(s) | True(s) | False(s) | Null(s) | Var(s) => s,
            Array { span, .. }
            | Set { span, .. }
            | Object { span, .. }
            | ArrayCompr { span, .. }
            | SetCompr { span, .. }
            | ObjectCompr { span, .. }
            | Call { span, .. }
            | UnaryExpr { span, .. }
            | RefDot { span, .. }
            | RefBrack { span, .. }
            | BinExpr { span, .. }
            | BoolExpr { span, .. }
            | ArithExpr { span, .. }
            | AssignExpr { span, .. }
            | Membership { span, .. } => span,
        }
    }
}

#[derive(Debug)]
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
pub struct WithModifier {
    pub span: Span,
    pub refr: Ref<Expr>,
    pub r#as: Ref<Expr>,
}

#[derive(Debug)]
pub struct LiteralStmt {
    pub span: Span,
    pub literal: Literal,
    pub with_mods: Vec<WithModifier>,
}

#[derive(Debug)]
pub struct Query {
    pub span: Span,
    pub stmts: Vec<LiteralStmt>,
}

#[derive(Debug)]
pub struct RuleAssign {
    pub span: Span,
    pub op: AssignOp,
    pub value: Ref<Expr>,
}

#[derive(Debug)]
pub struct RuleBody {
    pub span: Span,
    pub assign: Option<RuleAssign>,
    pub query: Ref<Query>,
}

#[derive(Debug)]
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
    pub fn span(&self) -> &Span {
        match self {
            Self::Spec { span, .. } | Self::Default { span, .. } => span,
        }
    }
}

#[derive(Debug)]
pub struct Package {
    pub span: Span,
    pub refr: Ref<Expr>,
}

#[derive(Debug)]
pub struct Import {
    pub span: Span,
    pub refr: Ref<Expr>,
    pub r#as: Option<Span>,
}

#[derive(Debug)]
pub struct Module {
    pub package: Package,
    pub imports: Vec<Import>,
    pub policy: Vec<Ref<Rule>>,
    pub rego_v1: bool,
}

pub type ExprRef = Ref<Expr>;
