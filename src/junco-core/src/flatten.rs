//! Fallible, iterative lowering of the owned DSL into the canonical portable tables.

use crate::errors::{CompileError, HistoryError};
use crate::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatRule, FlatTerm, FlatTest};
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use crate::scope::VariableScope;
use alloc::vec::Vec;
use history_syntax::syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use history_syntax::{Arity, Event};

// Only borrowed source nodes enter the work stack: every failure leaves caller-owned trees intact.
pub(crate) enum Work<'a, E: Event> {
    Regex(&'a RegexExpr<E>),
    Test(&'a TestExpr<E>),
    FinishRegex(&'a RegexExpr<E>, usize),
    FinishTest(&'a TestExpr<E>, usize),
}

fn push<T, L: Limits>(
    values: &mut Vec<T>,
    value: T,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    match world.try_reserve_vec(values, 1) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed),
    }
    limits.enforce_memory()?;
    values.push(value);
    Ok(())
}

fn take_children<L: Limits>(
    values: &mut Vec<u32>,
    start: usize,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<Vec<u32>, HistoryError> {
    if start > values.len() {
        return Err(HistoryError::invariant("invalid source operand range"));
    }
    let count = values.len() - start;
    let mut children = Vec::new();
    match world.try_reserve_vec_exact(&mut children, count) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed),
    }
    limits.enforce_memory()?;
    let mut index = start;
    while index < values.len() {
        limits.checkpoint()?;
        children.push(values[index]);
        index += 1;
    }
    values.truncate(start);
    Ok(children)
}

fn flatten_head<'a, E: Event, L: Limits>(
    head: &'a Head<E>,
    scope: &mut VariableScope<'a>,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<Vec<FlatHead<E::Component>>, CompileError> {
    let arity = E::Arity::value();
    let slots = head.slots();
    if slots.len() != arity {
        return Err(CompileError::HeadArity {
            expected: arity,
            found: slots.len(),
        });
    }
    let mut flat = Vec::new();
    match world.try_reserve_vec_exact(&mut flat, arity) {
        Ok(()) => {}
        Err(_) => return Err(HistoryError::AllocationFailed.into()),
    }
    limits.enforce_memory().map_err(HistoryError::from)?;
    let mut index = 0;
    while index < arity {
        limits.checkpoint().map_err(HistoryError::from)?;
        let component = Component::new(index);
        let slot = match &slots[index] {
            ComponentPattern::Constant(value) => {
                let coordinate = E::coordinate(*value);
                if coordinate != index {
                    return Err(CompileError::ComponentCoordinate {
                        component: index,
                        coordinate,
                    });
                }
                FlatHead::Constant(*value)
            }
            ComponentPattern::Variable(name) => {
                scope.bind(component, name.as_str())?;
                FlatHead::Bind
            }
        };
        flat.push(slot);
        index += 1;
    }
    Ok(flat)
}

fn flatten_atom<E: Event>(
    atom: &AtomPattern<E>,
    scope: &VariableScope<'_>,
) -> Result<(Component, FlatTerm<E::Component>), CompileError> {
    let component = atom.component;
    let index = component.index();
    if index >= scope.arity() {
        return Err(HistoryError::invalid_policy(
            "atom.component",
            "component index is outside the event arity",
        )
        .into());
    }
    let term = match &atom.pattern {
        ComponentPattern::Constant(value) => {
            let coordinate = E::coordinate(*value);
            if coordinate != index {
                return Err(CompileError::ComponentCoordinate {
                    component: index,
                    coordinate,
                });
            }
            FlatTerm::Constant(*value)
        }
        ComponentPattern::Variable(name) => {
            FlatTerm::Variable(scope.resolve(component, name.as_str())?)
        }
    };
    Ok((component, term))
}

fn schedule_regexes<'a, E: Event, L: Limits>(
    work: &mut Vec<Work<'a, E>>,
    children: &'a [RegexExpr<E>],
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    let mut index = children.len();
    while index > 0 {
        limits.checkpoint()?;
        index -= 1;
        push(work, Work::Regex(&children[index]), limits, world)?;
    }
    Ok(())
}

fn schedule_tests<'a, E: Event, L: Limits>(
    work: &mut Vec<Work<'a, E>>,
    children: &'a [TestExpr<E>],
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<(), HistoryError> {
    let mut index = children.len();
    while index > 0 {
        limits.checkpoint()?;
        index -= 1;
        push(work, Work::Test(&children[index]), limits, world)?;
    }
    Ok(())
}

/// Lowers a rule through the borrowed-source flattener.
pub fn flatten_rule<E: Event, L: Limits>(
    rule: &Rule<E>,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatRule<E::Component>, CompileError> {
    flatten_rule_parts(rule.mode, &rule.head, &rule.tail, limits, world)
}

/// Lowers borrowed syntax in source order without constructing an executable graph.
/// Resource failures propagate; well-scoped inputs cannot produce scope diagnostics.
/// The continuation invariant excludes internal stack and operand-guard failures.
pub fn flatten_rule_parts<E: Event, L: Limits>(
    mode: RuleMode,
    source_head: &Head<E>,
    source_tail: &RegexExpr<E>,
    limits: &mut L,
    world: &mut ObservationWorld,
) -> Result<FlatRule<E::Component>, CompileError> {
    limits.checkpoint().map_err(HistoryError::from)?;
    let mut scope = VariableScope::new(E::Arity::value());
    let head = flatten_head(source_head, &mut scope, limits, world)?;
    let mut builder = FlatBuilder::new(head);
    let mut work = Vec::new();
    let mut tests: Vec<u32> = Vec::new();
    let mut regexes: Vec<u32> = Vec::new();
    push(&mut work, Work::Regex(source_tail), limits, world)?;
    while !work.is_empty() {
        limits.checkpoint().map_err(HistoryError::from)?;
        let task = match work.pop() {
            Some(task) => task,
            None => return Err(HistoryError::invariant("missing source work").into()),
        };
        match task {
            Work::Regex(regex) => match regex {
                RegexExpr::Empty | RegexExpr::All | RegexExpr::Epsilon => {
                    let node = match regex {
                        RegexExpr::Empty => FlatRegex::Empty,
                        RegexExpr::All => FlatRegex::All,
                        _ => FlatRegex::Epsilon,
                    };
                    let id = builder.regex(node, limits, world)?;
                    push(&mut regexes, id, limits, world)?;
                }
                RegexExpr::Test(test) => {
                    push(
                        &mut work,
                        Work::FinishRegex(regex, tests.len()),
                        limits,
                        world,
                    )?;
                    push(&mut work, Work::Test(test), limits, world)?;
                }
                RegexExpr::Star(child) | RegexExpr::Not(child) => {
                    push(
                        &mut work,
                        Work::FinishRegex(regex, regexes.len()),
                        limits,
                        world,
                    )?;
                    push(&mut work, Work::Regex(child), limits, world)?;
                }
                RegexExpr::Concat(children)
                | RegexExpr::Union(children)
                | RegexExpr::Intersect(children) => {
                    push(
                        &mut work,
                        Work::FinishRegex(regex, regexes.len()),
                        limits,
                        world,
                    )?;
                    schedule_regexes(&mut work, children, limits, world)?;
                }
            },
            Work::Test(test) => match test {
                TestExpr::True | TestExpr::False | TestExpr::Atom { .. } => {
                    let node = match test {
                        TestExpr::True => FlatTest::Bool(true),
                        TestExpr::False => FlatTest::Bool(false),
                        TestExpr::Atom {
                            comparison,
                            pattern,
                        } => {
                            let atom_result = flatten_atom(pattern, &scope);
                            let (field, term) = atom_result?;
                            FlatTest::Atom {
                                field,
                                term,
                                positive: matches!(comparison, Comparison::Eq),
                            }
                        }
                        _ => return Err(HistoryError::invariant("invalid source test leaf").into()),
                    };
                    let id = builder.test(node, limits, world)?;
                    push(&mut tests, id, limits, world)?;
                }
                TestExpr::And(children) | TestExpr::Or(children) => {
                    push(
                        &mut work,
                        Work::FinishTest(test, tests.len()),
                        limits,
                        world,
                    )?;
                    schedule_tests(&mut work, children, limits, world)?;
                }
            },
            Work::FinishTest(test, start) => {
                let children = take_children(&mut tests, start, limits, world)?;
                let node = match test {
                    TestExpr::And(_) => FlatTest::And(children),
                    TestExpr::Or(_) => FlatTest::Or(children),
                    _ => return Err(HistoryError::invariant("invalid source test finish").into()),
                };
                let id = builder.test(node, limits, world)?;
                push(&mut tests, id, limits, world)?;
            }
            Work::FinishRegex(regex, start) => {
                let node = match regex {
                    RegexExpr::Test(_) => {
                        let child = match tests.pop() {
                            Some(child) => child,
                            None => {
                                return Err(
                                    HistoryError::invariant("missing source test operand").into()
                                );
                            }
                        };
                        FlatRegex::Test(child)
                    }
                    RegexExpr::Star(_) | RegexExpr::Not(_) => {
                        let child = match regexes.pop() {
                            Some(child) => child,
                            None => {
                                return Err(HistoryError::invariant(
                                    "missing source regex operand",
                                )
                                .into());
                            }
                        };
                        match regex {
                            RegexExpr::Star(_) => FlatRegex::Star(child),
                            _ => FlatRegex::Complement(child),
                        }
                    }
                    RegexExpr::Concat(_) | RegexExpr::Union(_) | RegexExpr::Intersect(_) => {
                        let children = take_children(&mut regexes, start, limits, world)?;
                        match regex {
                            RegexExpr::Concat(_) => FlatRegex::Concat(children),
                            RegexExpr::Union(_) => FlatRegex::Union(children),
                            _ => FlatRegex::Intersect(children),
                        }
                    }
                    _ => return Err(HistoryError::invariant("invalid source regex finish").into()),
                };
                let id = builder.regex(node, limits, world)?;
                push(&mut regexes, id, limits, world)?;
            }
        }
    }
    if regexes.len() != 1 || !tests.is_empty() {
        return Err(HistoryError::invariant("invalid source result stack").into());
    }
    let root = match regexes.pop() {
        Some(root) => root,
        None => return Err(HistoryError::invariant("missing source root").into()),
    };
    limits.checkpoint().map_err(HistoryError::from)?;
    let source: FlatPair<E::Component> = builder.finish(root)?;
    Ok(FlatRule { mode, source })
}
