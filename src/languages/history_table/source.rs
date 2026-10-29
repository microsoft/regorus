// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::value::{Array, Object};
use crate::Value;
use alloc::{
    format,
    string::{String, ToString as _},
    vec::Vec,
};
use history_syntax::Component;
use junco_core::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use junco_core::limits::Limits;
use junco_core::observation::ObservationWorld;
use junco_core::scope::VariableScope;
use junco_core::{CompileError, HistoryError};

fn invalid_policy(path: &str, message: &'static str) -> HistoryError {
    HistoryError::InvalidPolicy {
        path: path.to_string(),
        message,
    }
}

const fn invariant(message: &'static str) -> HistoryError {
    HistoryError::Invariant { message }
}

fn tagged<'a>(value: &'a Value, path: &str) -> Result<(&'a str, &'a Value), HistoryError> {
    let Value::Object(ref object) = *value else {
        return Err(invalid_policy(path, "expected a tagged object"));
    };
    if object.len() != 1 {
        return Err(invalid_policy(path, "expected exactly one tag"));
    }
    let Some((key, payload)) = object.iter_sorted().next() else {
        return Err(invalid_policy(path, "tag must be a string"));
    };
    let Value::String(ref tag) = *key else {
        return Err(invalid_policy(path, "tag must be a string"));
    };
    Ok((tag, payload))
}

fn array<'a>(value: &'a Value, path: &str) -> Result<&'a Array, HistoryError> {
    match *value {
        Value::Array(ref values) => Ok(values),
        _ => Err(invalid_policy(path, "expected an array")),
    }
}

fn marker(value: &Value, path: &str) -> Result<(), HistoryError> {
    if matches!(value, Value::Bool(true)) {
        Ok(())
    } else {
        Err(invalid_policy(path, "marker must be true"))
    }
}

fn member<'a>(object: &'a Object, key: &str, path: &str) -> Result<&'a Value, HistoryError> {
    object
        .iter_sorted()
        .find_map(|(candidate, value)| {
            matches!(candidate, Value::String(name) if &**name == key).then_some(value)
        })
        .ok_or_else(|| invalid_policy(path, "missing required member"))
}

fn string<'a>(value: &'a Value, path: &str) -> Result<&'a str, HistoryError> {
    match *value {
        Value::String(ref value) => Ok(value),
        _ => Err(invalid_policy(path, "identity constant must be a string")),
    }
}

fn push<T>(
    values: &mut Vec<T>,
    value: T,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    world
        .try_reserve_vec(values, 1)
        .map_err(|_| HistoryError::AllocationFailed)?;
    values.push(value);
    Ok(())
}

fn parse_field(name: &str, path: &str) -> Result<Component, HistoryError> {
    match name {
        "principal" => Ok(Component::Principal),
        "action" => Ok(Component::Action),
        "resource" => Ok(Component::Resource),
        _ => Err(invalid_policy(
            path,
            "expected principal, action or resource",
        )),
    }
}

#[allow(
    clippy::shadow_unrelated,
    reason = "Nested parser tags retain the existing pattern-matching structure"
)]
#[allow(
    clippy::semicolon_if_nothing_returned,
    reason = "Preserve the existing match-arm mutation style"
)]
fn parse_head<'a, L: Limits>(
    request: &'a Value,
    limits: &mut L,
) -> Result<([FlatHead<String>; 3], VariableScope<'a>), HistoryError> {
    let mut head = [FlatHead::Any, FlatHead::Any, FlatHead::Any];
    let mut scope = VariableScope::new();
    let (tag, payload) = tagged(request, "$.request")?;
    if tag == "any" {
        marker(payload, "$.request")?;
        return Ok((head, scope));
    }
    if tag != "object" {
        return Err(invalid_policy("$.request", "request must be any or object"));
    }
    let Value::Object(ref fields) = *payload else {
        return Err(invalid_policy("$.request.object", "expected an object"));
    };
    // Preserve sorted-member error precedence; scope slots retain principal/action/resource order.
    for (key, value) in fields.iter_sorted() {
        limits.checkpoint()?;
        let coordinate = parse_field(string(key, "$.request.object")?, "$.request.object")?;
        let (tag, payload) = tagged(value, "$.request.object")?;
        let slot = head
            .get_mut(coordinate.index())
            .ok_or_else(|| invariant("invalid head field"))?;
        match tag {
            "any" => marker(payload, "$.request.object")?,
            "value" => *slot = FlatHead::Constant(string(payload, "$.request.object")?.to_string()),
            "var" => {
                let name = string(payload, "$.request.object")?;
                if name.is_empty() {
                    return Err(invalid_policy(
                        "$.request.object",
                        "variable name must not be empty",
                    ));
                }
                scope.bind(coordinate, name).map_err(|error| match error {
                    CompileError::VariableComponentConflict { .. } => {
                        invalid_policy("$.request.object", "variable name reused across domains")
                    }
                    CompileError::UnboundVariable { name } => {
                        HistoryError::UnboundVariable { name }
                    }
                    CompileError::Runtime(error) => error,
                })?;
                *slot = FlatHead::Bind;
            }
            _ => {
                return Err(invalid_policy(
                    "$.request.object",
                    "field must be any, value or var",
                ))
            }
        }
    }
    Ok((head, scope))
}

fn parse_term(
    value: &Value,
    coordinate: Component,
    scope: &VariableScope<'_>,
    at: &str,
) -> Result<FlatTerm<String>, HistoryError> {
    let (tag, payload) = tagged(value, at)?;
    match tag {
        "value" => Ok(FlatTerm::Constant(string(payload, at)?.to_string())),
        "var" => {
            let name = string(payload, at)?;
            if name.is_empty() {
                return Err(invalid_policy(at, "variable name must not be empty"));
            }
            let field = scope
                .resolve(coordinate, name)
                .map_err(|error| match error {
                    CompileError::VariableComponentConflict { .. } => {
                        invalid_policy(at, "variable belongs to another identity domain")
                    }
                    CompileError::UnboundVariable { name: unbound } => {
                        HistoryError::UnboundVariable { name: unbound }
                    }
                    CompileError::Runtime(error) => error,
                })?;
            Ok(FlatTerm::Variable(field))
        }
        _ => Err(invalid_policy(at, "unknown term tag")),
    }
}

enum SourceWork<'a> {
    Regex(&'a Value, String),
    Test(&'a Value, String),
    RegexMany { tag: &'a str, start: usize },
    RegexOne(&'a str),
    TestMany { and: bool, start: usize },
    LiftTest,
}

/// Parse borrowed native Values into flat postorder tables, without constructing a graph.
pub fn parse_pair<L: Limits>(
    request: &Value,
    history: &Value,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatPair<String>, HistoryError> {
    limits.checkpoint()?;
    let (head, scope) = parse_head(request, limits)?;
    let mut source = FlatBuilder::new(head);
    let mut work = Vec::new();
    let mut regexes = Vec::new();
    let mut tests = Vec::new();
    push(
        &mut work,
        SourceWork::Regex(history, "$.history".to_string()),
        world,
    )?;
    while let Some(task) = work.pop() {
        limits.checkpoint()?;
        match task {
            SourceWork::Regex(value, at) => {
                let (tag, payload) = tagged(value, &at)?;
                match tag {
                    "empty" | "all" | "epsilon" => {
                        marker(payload, &at)?;
                        let leaf = match tag {
                            "empty" => FlatRegex::Empty,
                            "all" => FlatRegex::All,
                            _ => FlatRegex::Epsilon,
                        };
                        push(&mut regexes, source.regex(leaf, limits, world)?, world)?;
                    }
                    "test" => {
                        push(&mut work, SourceWork::LiftTest, world)?;
                        push(
                            &mut work,
                            SourceWork::Test(payload, format!("{at}.test")),
                            world,
                        )?;
                    }
                    "star" | "not" => {
                        push(&mut work, SourceWork::RegexOne(tag), world)?;
                        push(
                            &mut work,
                            SourceWork::Regex(payload, format!("{at}.{tag}")),
                            world,
                        )?;
                    }
                    "concat" | "union" | "intersect" => {
                        let children = array(payload, &at)?;
                        push(
                            &mut work,
                            SourceWork::RegexMany {
                                tag,
                                start: regexes.len(),
                            },
                            world,
                        )?;
                        for (index, child) in children.iter().enumerate().rev() {
                            limits.checkpoint()?;
                            push(
                                &mut work,
                                SourceWork::Regex(child, format!("{at}.{tag}[{index}]")),
                                world,
                            )?;
                        }
                    }
                    _ => return Err(invalid_policy(&at, "unknown history regex tag")),
                }
            }
            SourceWork::Test(value, at) => {
                if let Value::Bool(flag) = *value {
                    push(
                        &mut tests,
                        source.test(FlatTest::Bool(flag), limits, world)?,
                        world,
                    )?;
                    continue;
                }
                let (tag, payload) = tagged(value, &at)?;
                match tag {
                    "and" | "or" => {
                        let children = array(payload, &at)?;
                        push(
                            &mut work,
                            SourceWork::TestMany {
                                and: tag == "and",
                                start: tests.len(),
                            },
                            world,
                        )?;
                        for (index, child) in children.iter().enumerate().rev() {
                            limits.checkpoint()?;
                            push(
                                &mut work,
                                SourceWork::Test(child, format!("{at}.{tag}[{index}]")),
                                world,
                            )?;
                        }
                    }
                    "eq" | "neq" => {
                        let Value::Object(ref fields) = *payload else {
                            return Err(invalid_policy(
                                &at,
                                "comparison payload must be an object",
                            ));
                        };
                        if fields.len() != 2 {
                            return Err(invalid_policy(
                                &at,
                                "comparison requires exactly path and term",
                            ));
                        }
                        let path = array(member(fields, "path", &at)?, &at)?;
                        if path.len() != 1 {
                            return Err(invalid_policy(
                                &at,
                                "comparison path must contain exactly one typed field",
                            ));
                        }
                        let name = path
                            .first()
                            .ok_or_else(|| invalid_policy(&at, "missing comparison path"))?;
                        let coordinate = parse_field(string(name, &at)?, &at)?;
                        let term =
                            parse_term(member(fields, "term", &at)?, coordinate, &scope, &at)?;
                        let node = FlatTest::Atom {
                            field: coordinate,
                            term,
                            positive: tag == "eq",
                        };
                        push(&mut tests, source.test(node, limits, world)?, world)?;
                    }
                    _ => return Err(invalid_policy(&at, "unknown test tag")),
                }
            }
            SourceWork::RegexMany { tag, start } => {
                let children = take_children(&mut regexes, start, world)?;
                let node = match tag {
                    "concat" => FlatRegex::Concat(children),
                    "union" => FlatRegex::Union(children),
                    _ => FlatRegex::Intersect(children),
                };
                push(&mut regexes, source.regex(node, limits, world)?, world)?;
            }
            SourceWork::RegexOne(tag) => {
                let child = regexes
                    .pop()
                    .ok_or_else(|| invariant("missing regex operand"))?;
                let node = if tag == "star" {
                    FlatRegex::Star(child)
                } else {
                    FlatRegex::Complement(child)
                };
                push(&mut regexes, source.regex(node, limits, world)?, world)?;
            }
            SourceWork::TestMany { and, start } => {
                let children = take_children(&mut tests, start, world)?;
                let node = if and {
                    FlatTest::And(children)
                } else {
                    FlatTest::Or(children)
                };
                push(&mut tests, source.test(node, limits, world)?, world)?;
            }
            SourceWork::LiftTest => {
                let child = tests
                    .pop()
                    .ok_or_else(|| invariant("missing test operand"))?;
                push(
                    &mut regexes,
                    source.regex(FlatRegex::Test(child), limits, world)?,
                    world,
                )?;
            }
        }
    }
    if regexes.len() != 1 || !tests.is_empty() {
        return Err(invariant("invalid source result stack"));
    }
    let root = regexes
        .pop()
        .ok_or_else(|| invariant("missing source root"))?;
    limits.checkpoint()?;
    source.finish(root)
}

fn take_children(
    values: &mut Vec<u32>,
    start: usize,
    world: &mut ObservationWorld,
) -> Result<Vec<u32>, HistoryError> {
    let slice = values
        .get(start..)
        .ok_or_else(|| invariant("invalid source child stack"))?;
    let children = copy_ids(slice, world)?;
    values.truncate(start);
    Ok(children)
}

fn copy_ids(ids: &[u32], world: &mut ObservationWorld) -> Result<Vec<u32>, HistoryError> {
    let mut copied = Vec::new();
    world
        .try_reserve_vec_exact(&mut copied, ids.len())
        .map_err(|_| HistoryError::AllocationFailed)?;
    copied.extend_from_slice(ids);
    Ok(copied)
}
