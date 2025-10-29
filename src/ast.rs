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
        #[cfg_attr(feature = "ast", serde(skip_serializing_if = "Option::is_none"))]
        field: Option<(Span, Value)>,
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
    pub fn span(&self) -> &Span {
        use Expr::*;
        match self {
            String { span, .. }
            | RawString { span, .. }
            | Number { span, .. }
            | Bool { span, .. }
            | Null { span, .. }
            | Var { span, .. }
            | Array { span, .. }
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
            #[cfg(feature = "rego-extensions")]
            OrExpr { span, .. } => span,
        }
    }

    pub fn eidx(&self) -> u32 {
        use Expr::*;
        match self {
            String { eidx, .. }
            | RawString { eidx, .. }
            | Number { eidx, .. }
            | Bool { eidx, .. }
            | Null { eidx, .. }
            | Var { eidx, .. }
            | Array { eidx, .. }
            | Set { eidx, .. }
            | Object { eidx, .. }
            | ArrayCompr { eidx, .. }
            | SetCompr { eidx, .. }
            | ObjectCompr { eidx, .. }
            | Call { eidx, .. }
            | UnaryExpr { eidx, .. }
            | RefDot { eidx, .. }
            | RefBrack { eidx, .. }
            | BinExpr { eidx, .. }
            | BoolExpr { eidx, .. }
            | ArithExpr { eidx, .. }
            | AssignExpr { eidx, .. }
            | Membership { eidx, .. } => *eidx,
            #[cfg(feature = "rego-extensions")]
            OrExpr { eidx, .. } => *eidx,
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
    pub fn span(&self) -> &Span {
        match self {
            Self::Spec { span, .. } | Self::Default { span, .. } => span,
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
    // Position lookup table: maps (byte_offset) -> expr_idx for quick hover/completion
    #[cfg_attr(feature = "ast", serde(skip))]
    pub expr_positions: alloc::vec::Vec<(u32, u32, u32)>, // (line, col, eidx) - 1-based
}

pub type ExprRef = Ref<Expr>;

impl Module {
    /// Find the expression at a given position using the position lookup table.
    /// Returns the expr_idx of the expression at or just before the position.
    /// Line and column are 1-based (matching Span convention).
    /// Uses binary search for O(log n) performance.
    ///
    /// Note: VS Code/LSP provides Position with 0-based line/character.
    /// Callers must convert: `find_expr_at_position(vscode_line + 1, vscode_char + 1)`
    ///
    /// Strategy: Return the rightmost (most recently parsed) expression at or before
    /// the cursor position. When multiple expressions start at the same position (e.g.,
    /// nested expressions), the later ones in the table are the outer/parent expressions,
    /// so we return the last match which gives us the innermost context for hover.
    pub fn find_expr_at_position(&self, line: usize, col: usize) -> Option<u32> {
        let line = line as u32;
        let col = col as u32;

        // Binary search for the rightmost expression at or before (line, col).
        // The table is sorted by (line, col), with eidx as tiebreaker for stability.
        let idx = self
            .expr_positions
            .partition_point(|(eline, ecol, _)| *eline < line || (*eline == line && *ecol <= col));

        // partition_point returns the index where we'd insert, so we need idx - 1
        if idx > 0 {
            self.expr_positions.get(idx - 1).map(|(_, _, eidx)| *eidx)
        } else {
            None
        }
    }
}
