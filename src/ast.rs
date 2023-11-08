// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::lexer::*;

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

#[derive(Debug, Clone)]
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
        items: Vec<Expr>,
    },

    // set
    Set {
        span: Span,
        items: Vec<Expr>,
    },

    Object {
        span: Span,
        fields: Vec<(Span, Expr, Expr)>,
    },

    // Comprehensions
    ArrayCompr {
        span: Span,
        term: Box<Expr>,
        query: Query,
    },

    SetCompr {
        span: Span,
        term: Box<Expr>,
        query: Query,
    },

    ObjectCompr {
        span: Span,
        key: Box<Expr>,
        value: Box<Expr>,
        query: Query,
    },

    Call {
        span: Span,
        fcn: Box<Expr>,
        params: Vec<Expr>,
    },

    UnaryExpr {
        span: Span,
        expr: Box<Expr>,
    },

    // ref
    RefDot {
        span: Span,
        refr: Box<Expr>,
        field: Span,
    },

    RefBrack {
        span: Span,
        refr: Box<Expr>,
        index: Box<Expr>,
    },

    // Infix expressions
    BinExpr {
        span: Span,
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    BoolExpr {
        span: Span,
        op: BoolOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },

    ArithExpr {
        span: Span,
        op: ArithOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },

    AssignExpr {
        span: Span,
        op: AssignOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },

    Membership {
        span: Span,
        key: Box<Option<Expr>>,
        value: Box<Expr>,
        collection: Box<Expr>,
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

#[derive(Debug, Clone)]
pub enum Literal {
    SomeVars {
        span: Span,
        vars: Vec<Span>,
    },
    SomeIn {
        span: Span,
        key: Option<Expr>,
        value: Expr,
        collection: Expr,
    },
    Expr {
        span: Span,
        expr: Expr,
    },
    NotExpr {
        span: Span,
        expr: Expr,
    },
    Every {
        span: Span,
        key: Option<Span>,
        value: Span,
        domain: Expr,
        query: Query,
    },
}

#[derive(Debug, Clone)]
pub struct WithModifier {
    pub span: Span,
    pub refr: Expr,
    pub r#as: Expr,
}

#[derive(Debug, Clone)]
pub struct LiteralStmt {
    pub span: Span,
    pub literal: Literal,
    pub with_mods: Vec<WithModifier>,
}

#[derive(Debug, Clone)]
pub struct Query {
    pub span: Span,
    pub stmts: Vec<LiteralStmt>,
}

#[derive(Debug, Clone)]
pub struct RuleAssign {
    pub span: Span,
    pub op: AssignOp,
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct RuleBody {
    pub span: Span,
    pub assign: Option<RuleAssign>,
    pub query: Query,
}

#[derive(Debug, Clone)]
pub enum RuleHead {
    Compr {
        span: Span,
        refr: Expr,
        assign: Option<RuleAssign>,
    },
    Set {
        span: Span,
        refr: Expr,
        key: Option<Expr>,
    },
    Func {
        span: Span,
        refr: Expr,
        args: Vec<Expr>,
        assign: Option<RuleAssign>,
    },
}

#[derive(Debug, Clone)]
pub enum Rule {
    Spec {
        span: Span,
        head: RuleHead,
        bodies: Vec<RuleBody>,
    },
    Default {
        span: Span,
        refr: Expr,
        op: AssignOp,
        value: Expr,
    },
}

#[derive(Debug, Clone)]
pub struct Package {
    pub span: Span,
    pub refr: Expr,
}

#[derive(Debug, Clone)]
pub struct Import {
    pub span: Span,
    pub refr: Expr,
    pub r#as: Option<Span>,
}

#[derive(Debug, Clone)]
pub struct Module {
    pub package: Package,
    pub imports: Vec<Import>,
    pub policy: Vec<Rule>,
}

#[derive(Debug, Clone)]
pub struct Ref<'a, T> {
    r: &'a T,
}

impl<'a, T> Ref<'a, T> {
    pub fn make(r: &'a T) -> Self {
        Self { r }
    }

    pub fn inner(&self) -> &'a T {
        self.r
    }
}

impl<'a, T> Eq for Ref<'a, T> {}

impl<'a, T> PartialEq for Ref<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.r, other.r)
    }
}

impl<'a, T> PartialOrd for Ref<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a, T> Ord for Ref<'a, T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        (self.r as *const T).cmp(&(other.r as *const T))
    }
}
