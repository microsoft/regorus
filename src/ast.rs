// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::lexer::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum BinOp {
    And,
    Or,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum BoolOp {
    Lt,
    Le,
    Eq,
    Ge,
    Gt,
    Ne,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum AssignOp {
    Eq,
    ColEq,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Expr<'source> {
    // Simple items that only have a span as content.
    String(Span<'source>),
    RawString(Span<'source>),
    Number(Span<'source>),
    True(Span<'source>),
    False(Span<'source>),
    Null(Span<'source>),
    Var(Span<'source>),

    // array
    Array {
        span: Span<'source>,
        items: Vec<Expr<'source>>,
    },

    // set
    Set {
        span: Span<'source>,
        items: Vec<Expr<'source>>,
    },

    Object {
        span: Span<'source>,
        fields: Vec<(Span<'source>, Expr<'source>, Expr<'source>)>,
    },

    // Comprehensions
    ArrayCompr {
        span: Span<'source>,
        term: Box<Expr<'source>>,
        query: Query<'source>,
    },

    SetCompr {
        span: Span<'source>,
        term: Box<Expr<'source>>,
        query: Query<'source>,
    },

    ObjectCompr {
        span: Span<'source>,
        key: Box<Expr<'source>>,
        value: Box<Expr<'source>>,
        query: Query<'source>,
    },

    Call {
        span: Span<'source>,
        fcn: Box<Expr<'source>>,
        params: Vec<Expr<'source>>,
    },

    UnaryExpr {
        span: Span<'source>,
        expr: Box<Expr<'source>>,
    },

    // ref
    RefDot {
        span: Span<'source>,
        refr: Box<Expr<'source>>,
        field: Span<'source>,
    },

    RefBrack {
        span: Span<'source>,
        refr: Box<Expr<'source>>,
        index: Box<Expr<'source>>,
    },

    // Infix expressions
    BinExpr {
        span: Span<'source>,
        op: BinOp,
        lhs: Box<Expr<'source>>,
        rhs: Box<Expr<'source>>,
    },
    BoolExpr {
        span: Span<'source>,
        op: BoolOp,
        lhs: Box<Expr<'source>>,
        rhs: Box<Expr<'source>>,
    },

    ArithExpr {
        span: Span<'source>,
        op: ArithOp,
        lhs: Box<Expr<'source>>,
        rhs: Box<Expr<'source>>,
    },

    AssignExpr {
        span: Span<'source>,
        op: AssignOp,
        lhs: Box<Expr<'source>>,
        rhs: Box<Expr<'source>>,
    },

    Membership {
        span: Span<'source>,
        key: Box<Option<Expr<'source>>>,
        value: Box<Expr<'source>>,
        collection: Box<Expr<'source>>,
    },
}

impl<'source> Expr<'source> {
    pub fn span(&self) -> &Span<'source> {
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Literal<'source> {
    SomeVars {
        span: Span<'source>,
        vars: Vec<Span<'source>>,
    },
    SomeIn {
        span: Span<'source>,
        key: Option<Expr<'source>>,
        value: Expr<'source>,
        collection: Expr<'source>,
    },
    Expr {
        span: Span<'source>,
        expr: Expr<'source>,
    },
    NotExpr {
        span: Span<'source>,
        expr: Expr<'source>,
    },
    Every {
        span: Span<'source>,
        key: Option<Span<'source>>,
        value: Span<'source>,
        domain: Expr<'source>,
        query: Query<'source>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct WithModifier<'source> {
    pub span: Span<'source>,
    pub refr: Expr<'source>,
    pub r#as: Expr<'source>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct LiteralStmt<'source> {
    pub span: Span<'source>,
    pub literal: Literal<'source>,
    pub with_mods: Vec<WithModifier<'source>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Query<'source> {
    pub span: Span<'source>,
    pub stmts: Vec<LiteralStmt<'source>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct RuleAssign<'source> {
    pub span: Span<'source>,
    pub op: AssignOp,
    pub value: Expr<'source>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct RuleBody<'source> {
    pub span: Span<'source>,
    pub assign: Option<RuleAssign<'source>>,
    pub query: Query<'source>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum RuleHead<'source> {
    Compr {
        span: Span<'source>,
        refr: Expr<'source>,
        assign: Option<RuleAssign<'source>>,
    },
    Set {
        span: Span<'source>,
        refr: Expr<'source>,
        key: Option<Expr<'source>>,
    },
    Func {
        span: Span<'source>,
        refr: Expr<'source>,
        args: Vec<Expr<'source>>,
        assign: Option<RuleAssign<'source>>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub enum Rule<'source> {
    Spec {
        span: Span<'source>,
        head: RuleHead<'source>,
        bodies: Vec<RuleBody<'source>>,
    },
    Default {
        span: Span<'source>,
        refr: Expr<'source>,
        op: AssignOp,
        value: Expr<'source>,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Package<'source> {
    pub span: Span<'source>,
    pub refr: Expr<'source>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Import<'source> {
    pub span: Span<'source>,
    pub refr: Expr<'source>,
    pub r#as: Option<Span<'source>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Module<'source> {
    pub package: Package<'source>,
    pub imports: Vec<Import<'source>>,
    pub policy: Vec<Rule<'source>>,
}
