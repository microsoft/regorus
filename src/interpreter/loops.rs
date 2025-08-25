use crate::ast::*;
use crate::interpreter::Interpreter;
use crate::lexer::*;
use crate::scheduler::traverse;
use crate::utils::get_path_string;
use crate::value::Value;
use crate::*;

#[derive(Debug)]
pub enum LoopExpr {
    Loop {
        span: Span,
        expr: Ref<Expr>,
        value: Ref<Expr>,
        index: Ref<Expr>,
    },
    Walk {
        span: Span,
        expr: Ref<Expr>,
    },
}

impl LoopExpr {
    pub fn span(&self) -> Span {
        match self {
            Self::Loop { span, .. } => span.clone(),
            Self::Walk { span, .. } => span.clone(),
        }
    }

    pub fn value(&self) -> Ref<Expr> {
        match self {
            Self::Loop { value, .. } => value.clone(),
            Self::Walk { expr, .. } => expr.clone(),
        }
    }

    pub fn expr(&self) -> Ref<Expr> {
        match self {
            Self::Loop { expr, .. } => expr.clone(),
            Self::Walk { expr, .. } => expr.clone(),
        }
    }

    pub fn index(&self) -> Option<Ref<Expr>> {
        match self {
            Self::Loop { index, .. } => Some(index.clone()),
            Self::Walk { .. } => None,
        }
    }
}

impl Interpreter {
    pub(super) fn hoist_loops_impl(&self, expr: &ExprRef, loops: &mut Vec<LoopExpr>) {
        use Expr::*;
        match expr.as_ref() {
            RefBrack {
                refr, index, span, ..
            } => {
                // First hoist any loops in refr
                self.hoist_loops_impl(refr, loops);

                // hoist any loops in index expression.
                self.hoist_loops_impl(index, loops);

                // Then hoist the current bracket operation.
                let mut indices = Vec::with_capacity(1);
                let _ = traverse(index, &mut |e| match e.as_ref() {
                    Var { span: ident, .. } if self.is_loop_index_var(&ident.source_str()) => {
                        indices.push(ident.source_str());
                        Ok(false)
                    }
                    Array { .. } | Object { .. } => Ok(true),
                    _ => Ok(false),
                });
                if !indices.is_empty() {
                    loops.push(LoopExpr::Loop {
                        span: span.clone(),
                        expr: expr.clone(),
                        value: refr.clone(),
                        index: index.clone(),
                    })
                }
            }

            // Primitives
            String { .. }
            | RawString { .. }
            | Number { .. }
            | Bool { .. }
            | Null { .. }
            | Var { .. } => (),

            // Recurse into expressions in other variants.
            Array { items, .. } | Set { items, .. } | Call { params: items, .. } => {
                for item in items {
                    self.hoist_loops_impl(item, loops);
                }

                // Handle walk builtin which acts as a generator.
                // TODO: Handle with modifier on the walk builtin.
                if let Expr::Call { fcn, .. } = expr.as_ref() {
                    if let Ok(fcn_path) = get_path_string(fcn, None) {
                        if fcn_path == "walk" {
                            // TODO: Use an enum for LoopExpr to handle walk
                            loops.push(LoopExpr::Walk {
                                span: expr.span().clone(),
                                expr: expr.clone(),
                            })
                        }
                    }
                }
            }

            Object { fields, .. } => {
                for (_, key, value) in fields {
                    self.hoist_loops_impl(key, loops);
                    self.hoist_loops_impl(value, loops);
                }
            }

            RefDot { refr: expr, .. } | UnaryExpr { expr, .. } => {
                self.hoist_loops_impl(expr, loops)
            }

            BinExpr { lhs, rhs, .. }
            | BoolExpr { lhs, rhs, .. }
            | ArithExpr { lhs, rhs, .. }
            | AssignExpr { lhs, rhs, .. } => {
                self.hoist_loops_impl(lhs, loops);
                self.hoist_loops_impl(rhs, loops);
            }

            #[cfg(feature = "rego-extensions")]
            OrExpr { lhs, rhs, .. } => {
                self.hoist_loops_impl(lhs, loops);
                self.hoist_loops_impl(rhs, loops);
            }

            Membership {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key.as_ref() {
                    self.hoist_loops_impl(key, loops);
                }
                self.hoist_loops_impl(value, loops);
                self.hoist_loops_impl(collection, loops);
            }

            // The output expressions of comprehensions must be subject to hoisting
            // only after evaluating the body of the comprehensions since the output
            // expressions may depend on variables defined within the body.
            ArrayCompr { .. } | SetCompr { .. } | ObjectCompr { .. } => (),
        }
    }

    pub(super) fn hoist_loops(&self, literal: &Literal) -> Vec<LoopExpr> {
        let mut loops = vec![];
        use Literal::*;
        match literal {
            SomeVars { .. } => (),
            SomeIn {
                key,
                value,
                collection,
                ..
            } => {
                if let Some(key) = key {
                    self.hoist_loops_impl(key, &mut loops);
                }
                self.hoist_loops_impl(value, &mut loops);
                self.hoist_loops_impl(collection, &mut loops);
            }
            Every {
                domain: collection, ..
            } => self.hoist_loops_impl(collection, &mut loops),
            Expr { expr, .. } | NotExpr { expr, .. } => self.hoist_loops_impl(expr, &mut loops),
        }
        loops
    }

    pub(super) fn is_loop_index_var(&self, ident: &SourceStr) -> bool {
        // TODO: check for vars that are declared using some-vars
        match ident.text() {
            "_" => true,
            _ => match self.lookup_local_var(ident) {
                // Vars declared using `some v` can be loop vars.
                // They are initialized to undefined.
                Some(Value::Undefined) => true,
                // If ident is a local var (in current or parent scopes),
                // then it is not a loop var.
                Some(_) => false,
                None => {
                    // Check if ident is a rule.
                    let path = self.current_module_path.clone() + "." + ident.text();
                    !self.compiled_policy.rules.contains_key(&path)
                }
            },
        }
    }
}
