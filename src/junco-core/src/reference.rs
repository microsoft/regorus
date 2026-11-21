//! Unverified reference evaluator for numeric history sources by Brzozowski derivatives,
//! kept (`test-util`) as a differential oracle for the symbolic `history-semantics` runtime.
//!
//! A history is in a rule's language iff folding [`Lang::step`] over its events ends in a
//! [`Lang::nullable`] language. Smart constructors apply similarity rules so residuals of the
//! usual `[any, ..., any]` and `star(...)` shapes stay small.

use crate::errors::HistoryError;
use crate::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use crate::limits::Limits;
use alloc::boxed::Box;
use alloc::vec::Vec;

/// Deepest residual the evaluator builds or recurses over.
pub const MAX_REFERENCE_DEPTH: usize = 256;
/// Most nodes built while inflating a source or taking one derivative.
pub const MAX_REFERENCE_NODES: usize = 1 << 16;

/// Whether `request` matches the head. Head variables bind their own coordinate, so a
/// matching request is also the bindings vector.
pub fn head_matches(head: &[FlatHead<u64>], request: &[u64]) -> bool {
    head.len() == request.len()
        && head.iter().zip(request).all(|(slot, value)| match slot {
            FlatHead::Constant(constant) => constant == value,
            FlatHead::Any | FlatHead::Bind => true,
        })
}

/// Truth value of every test for one event. Validated sources only reference earlier tests,
/// so one pass in index order evaluates the DAG without recursion.
fn test_values(tests: &[FlatTest<u64>], event: &[u64], bindings: &[u64]) -> Vec<bool> {
    let mut values: Vec<bool> = Vec::with_capacity(tests.len());
    for test in tests {
        let child = |index: &u32| {
            usize::try_from(*index)
                .ok()
                .and_then(|index| values.get(index))
                .copied()
                .unwrap_or(false)
        };
        let value = match test {
            FlatTest::Bool(value) => *value,
            FlatTest::Atom {
                field,
                term,
                positive,
            } => {
                let expected = match term {
                    FlatTerm::Constant(constant) => Some(constant),
                    FlatTerm::Variable(variable) => bindings.get(variable.index()),
                };
                match (event.get(field.index()), expected) {
                    (Some(actual), Some(expected)) => (actual == expected) == *positive,
                    _ => false,
                }
            }
            FlatTest::And(children) => children.iter().all(child),
            FlatTest::Or(children) => children.iter().any(child),
        };
        values.push(value);
    }
    values
}

/// Node counter shared by one inflation or one derivative.
struct Budget<'a, L> {
    limits: &'a mut L,
    nodes: usize,
}

impl<L: Limits> Budget<'_, L> {
    fn charge(&mut self, nodes: usize) -> Result<(), HistoryError> {
        self.limits.checkpoint()?;
        self.nodes = self.nodes.saturating_add(nodes);
        if self.nodes > MAX_REFERENCE_NODES {
            return Err(HistoryError::GraphBudget {
                limit: MAX_REFERENCE_NODES,
            });
        }
        Ok(())
    }

    fn clone(&mut self, lang: &Lang) -> Result<Lang, HistoryError> {
        self.charge(lang.size())?;
        Ok(lang.clone())
    }
}

/// A regular language over events; `Test(i)` is the single events satisfying test `i`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Lang {
    Empty,
    All,
    Epsilon,
    Test(u32),
    Union(Vec<Lang>),
    Concat(Vec<Lang>),
    Intersect(Vec<Lang>),
    Star(Box<Lang>),
    Not(Box<Lang>),
}

// shortcut: structural dedup is quadratic in the number of alternatives; the symbolic
// checker hash-conses residuals when wide unions matter.
fn push_unique(children: &mut Vec<Lang>, child: Lang) {
    if !children.contains(&child) {
        children.push(child);
    }
}

impl Lang {
    fn union(children: Vec<Lang>) -> Lang {
        let mut out = Vec::new();
        for child in children {
            match child {
                Lang::Empty => {}
                Lang::All => return Lang::All,
                Lang::Union(inner) => inner.into_iter().for_each(|c| push_unique(&mut out, c)),
                other => push_unique(&mut out, other),
            }
        }
        match out.len() {
            0 => Lang::Empty,
            1 => out.pop().unwrap_or(Lang::Empty),
            _ => Lang::Union(out),
        }
    }

    fn intersect(children: Vec<Lang>) -> Lang {
        let mut out = Vec::new();
        for child in children {
            match child {
                Lang::All => {}
                Lang::Empty => return Lang::Empty,
                Lang::Intersect(inner) => {
                    inner.into_iter().for_each(|c| push_unique(&mut out, c));
                }
                other => push_unique(&mut out, other),
            }
        }
        match out.len() {
            0 => Lang::All,
            1 => out.pop().unwrap_or(Lang::All),
            _ => Lang::Intersect(out),
        }
    }

    fn concat(children: Vec<Lang>) -> Lang {
        let mut out = Vec::new();
        for child in children {
            match child {
                Lang::Epsilon => {}
                Lang::Empty => return Lang::Empty,
                Lang::Concat(inner) => out.extend(inner),
                other => out.push(other),
            }
        }
        match out.len() {
            0 => Lang::Epsilon,
            1 => out.pop().unwrap_or(Lang::Epsilon),
            _ => Lang::Concat(out),
        }
    }

    fn star(inner: Lang) -> Lang {
        match inner {
            Lang::Empty | Lang::Epsilon => Lang::Epsilon,
            Lang::All => Lang::All,
            star @ Lang::Star(_) => star,
            other => Lang::Star(Box::new(other)),
        }
    }

    fn not(inner: Lang) -> Lang {
        match inner {
            Lang::Empty => Lang::All,
            Lang::All => Lang::Empty,
            Lang::Not(inner) => *inner,
            other => Lang::Not(Box::new(other)),
        }
    }

    /// Builds the language of `pair`'s root regex.
    // shortcut: expands the source DAG into a tree under depth/node caps; fine for small
    // differential corpora, never used to decide production requests.
    pub fn inflate<L: Limits>(pair: &FlatPair<u64>, limits: &mut L) -> Result<Lang, HistoryError> {
        let mut budget = Budget { limits, nodes: 0 };
        Self::inflate_node(&pair.regexes, pair.root, 0, &mut budget)
    }

    fn inflate_node<L: Limits>(
        regexes: &[FlatRegex],
        index: u32,
        depth: usize,
        budget: &mut Budget<'_, L>,
    ) -> Result<Lang, HistoryError> {
        budget.charge(1)?;
        check_depth(depth)?;
        let regex = usize::try_from(index)
            .ok()
            .and_then(|index| regexes.get(index))
            .ok_or(HistoryError::GraphIndex)?;
        let depth = depth.saturating_add(1);
        let mut all = |children: &[u32]| -> Result<Vec<Lang>, HistoryError> {
            children
                .iter()
                .map(|child| Self::inflate_node(regexes, *child, depth, budget))
                .collect()
        };
        Ok(match regex {
            FlatRegex::Empty => Lang::Empty,
            FlatRegex::All => Lang::All,
            FlatRegex::Epsilon => Lang::Epsilon,
            FlatRegex::Test(test) => Lang::Test(*test),
            FlatRegex::Concat(children) => Self::concat(all(children)?),
            FlatRegex::Union(children) => Self::union(all(children)?),
            FlatRegex::Intersect(children) => Self::intersect(all(children)?),
            FlatRegex::Star(child) => {
                Self::star(Self::inflate_node(regexes, *child, depth, budget)?)
            }
            FlatRegex::Complement(child) => {
                Self::not(Self::inflate_node(regexes, *child, depth, budget)?)
            }
        })
    }

    /// Whether the empty history is in the language.
    pub fn nullable(&self) -> bool {
        match self {
            Lang::Empty | Lang::Test(_) => false,
            Lang::All | Lang::Epsilon | Lang::Star(_) => true,
            Lang::Union(children) => children.iter().any(Lang::nullable),
            Lang::Concat(children) | Lang::Intersect(children) => {
                children.iter().all(Lang::nullable)
            }
            Lang::Not(inner) => !inner.nullable(),
        }
    }

    fn size(&self) -> usize {
        match self {
            Lang::Empty | Lang::All | Lang::Epsilon | Lang::Test(_) => 1,
            Lang::Union(children) | Lang::Concat(children) | Lang::Intersect(children) => children
                .iter()
                .fold(1, |total, child| total.saturating_add(child.size())),
            Lang::Star(inner) | Lang::Not(inner) => inner.size().saturating_add(1),
        }
    }

    /// Residual after one event whose bindings come from the matched request.
    pub fn step<L: Limits>(
        &self,
        pair: &FlatPair<u64>,
        event: &[u64],
        bindings: &[u64],
        limits: &mut L,
    ) -> Result<Lang, HistoryError> {
        let holds = test_values(&pair.tests, event, bindings);
        let next = self.derivative(&holds, &mut Budget { limits, nodes: 0 })?;
        next.check_depths(0)?;
        Ok(next)
    }

    /// Derivative given the truth value of every test for one event.
    fn derivative<L: Limits>(
        &self,
        holds: &[bool],
        budget: &mut Budget<'_, L>,
    ) -> Result<Lang, HistoryError> {
        budget.charge(1)?;
        Ok(match self {
            Lang::Empty | Lang::Epsilon => Lang::Empty,
            Lang::All => Lang::All,
            Lang::Test(test) => {
                let held = usize::try_from(*test)
                    .ok()
                    .and_then(|index| holds.get(index))
                    .copied()
                    .unwrap_or(false);
                if held { Lang::Epsilon } else { Lang::Empty }
            }
            Lang::Union(children) => Self::union(
                children
                    .iter()
                    .map(|c| c.derivative(holds, budget))
                    .collect::<Result<_, _>>()?,
            ),
            Lang::Intersect(children) => Self::intersect(
                children
                    .iter()
                    .map(|c| c.derivative(holds, budget))
                    .collect::<Result<_, _>>()?,
            ),
            Lang::Not(inner) => Self::not(inner.derivative(holds, budget)?),
            Lang::Star(inner) => Self::concat(alloc::vec![
                inner.derivative(holds, budget)?,
                budget.clone(self)?
            ]),
            Lang::Concat(children) => {
                let mut alternatives = Vec::new();
                for (index, child) in children.iter().enumerate() {
                    let mut factors = alloc::vec![child.derivative(holds, budget)?];
                    for rest in children.iter().skip(index.saturating_add(1)) {
                        factors.push(budget.clone(rest)?);
                    }
                    alternatives.push(Self::concat(factors));
                    if !child.nullable() {
                        break;
                    }
                }
                Self::union(alternatives)
            }
        })
    }

    fn check_depths(&self, depth: usize) -> Result<(), HistoryError> {
        check_depth(depth)?;
        let depth = depth.saturating_add(1);
        match self {
            Lang::Empty | Lang::All | Lang::Epsilon | Lang::Test(_) => Ok(()),
            Lang::Union(children) | Lang::Concat(children) | Lang::Intersect(children) => children
                .iter()
                .try_for_each(|child| child.check_depths(depth)),
            Lang::Star(inner) | Lang::Not(inner) => inner.check_depths(depth),
        }
    }
}

fn check_depth(depth: usize) -> Result<(), HistoryError> {
    if depth > MAX_REFERENCE_DEPTH {
        return Err(HistoryError::GraphBudget {
            limit: MAX_REFERENCE_DEPTH,
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flat::FlatBuilder;
    use crate::limits::Unmetered;
    use crate::observation::ObservationWorld;
    use alloc::vec;
    use history_syntax::syntax::Component;

    const ACTOR: u64 = 7;
    const EDIT: u64 = 11;
    const DOC: u64 = 13;
    const REMOVE: u64 = 17;

    struct Source(FlatBuilder<u64>);

    impl Source {
        // Head: principal and resource bind, action is any.
        fn new() -> Self {
            Self(FlatBuilder::new(vec![
                FlatHead::Bind,
                FlatHead::Any,
                FlatHead::Bind,
            ]))
        }

        fn test(&mut self, node: FlatTest<u64>) -> u32 {
            self.0
                .test(node, &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        }

        fn regex(&mut self, node: FlatRegex) -> u32 {
            self.0
                .regex(node, &mut Unmetered, &mut ObservationWorld)
                .unwrap()
        }

        // `principal == actor, action == action, resource == doc`.
        fn event_test(&mut self, action: u64) -> u32 {
            let principal = self.test(FlatTest::Atom {
                field: Component(0),
                term: FlatTerm::Variable(Component(0)),
                positive: true,
            });
            let action = self.test(FlatTest::Atom {
                field: Component(1),
                term: FlatTerm::Constant(action),
                positive: true,
            });
            let resource = self.test(FlatTest::Atom {
                field: Component(2),
                term: FlatTerm::Variable(Component(2)),
                positive: true,
            });
            self.test(FlatTest::And(vec![principal, action, resource]))
        }

        // `[any, <test>, any]`.
        fn contains(&mut self, test: u32) -> u32 {
            let any = self.regex(FlatRegex::All);
            let event = self.regex(FlatRegex::Test(test));
            self.regex(FlatRegex::Concat(vec![any, event, any]))
        }

        fn finish(self, root: u32) -> FlatPair<u64> {
            self.0.finish(root).unwrap()
        }
    }

    fn accepts(pair: &FlatPair<u64>, request: &[u64], history: &[[u64; 3]]) -> bool {
        assert!(head_matches(&pair.head, request));
        let mut lang = Lang::inflate(pair, &mut Unmetered).unwrap();
        for event in history {
            lang = lang.step(pair, event, request, &mut Unmetered).unwrap();
        }
        lang.nullable()
    }

    #[test]
    fn prior_edit_by_the_same_principal_on_the_same_resource() {
        let mut source = Source::new();
        let edit = source.event_test(EDIT);
        let root = source.contains(edit);
        let pair = source.finish(root);
        let request = [ACTOR, 99, DOC];

        assert!(!Lang::inflate(&pair, &mut Unmetered).unwrap().nullable());
        assert!(accepts(&pair, &request, &[[ACTOR, EDIT, DOC]]));
        assert!(accepts(
            &pair,
            &request,
            &[[1, 2, 3], [ACTOR, EDIT, DOC], [4, 5, 6]]
        ));
        assert!(!accepts(&pair, &request, &[]));
        assert!(!accepts(&pair, &request, &[[ACTOR + 1, EDIT, DOC]]));
        assert!(!accepts(&pair, &request, &[[ACTOR, REMOVE, DOC]]));
        assert!(!accepts(
            &pair,
            &[ACTOR, 99, DOC + 1],
            &[[ACTOR, EDIT, DOC]]
        ));
    }

    #[test]
    fn residual_of_a_contains_pattern_stays_small() {
        let mut source = Source::new();
        let edit = source.event_test(EDIT);
        let root = source.contains(edit);
        let pair = source.finish(root);
        let request = [ACTOR, 99, DOC];
        let mut lang = Lang::inflate(&pair, &mut Unmetered).unwrap();
        for _ in 0..64 {
            lang = lang
                .step(&pair, &[1, 2, 3], &request, &mut Unmetered)
                .unwrap();
        }
        assert!(lang.size() <= 8, "{lang:?}");
        lang = lang
            .step(&pair, &[ACTOR, EDIT, DOC], &request, &mut Unmetered)
            .unwrap();
        assert_eq!(lang, Lang::All);
    }

    #[test]
    fn complement_and_intersection() {
        // Edited somewhere, and never removed: `[any, edit, any] & ![any, remove, any]`.
        let mut source = Source::new();
        let edit = source.event_test(EDIT);
        let remove = source.event_test(REMOVE);
        let edited = source.contains(edit);
        let removed = source.contains(remove);
        let not_removed = source.regex(FlatRegex::Complement(removed));
        let root = source.regex(FlatRegex::Intersect(vec![edited, not_removed]));
        let pair = source.finish(root);
        let request = [ACTOR, 99, DOC];

        assert!(accepts(&pair, &request, &[[ACTOR, EDIT, DOC]]));
        assert!(!accepts(
            &pair,
            &request,
            &[[ACTOR, EDIT, DOC], [ACTOR, REMOVE, DOC]]
        ));
        assert!(!accepts(&pair, &request, &[]));
        // A removal by someone else does not count.
        assert!(accepts(
            &pair,
            &request,
            &[[ACTOR, EDIT, DOC], [ACTOR + 1, REMOVE, DOC]]
        ));
    }

    #[test]
    fn star_accepts_only_repetitions() {
        let mut source = Source::new();
        let edit = source.event_test(EDIT);
        let event = source.regex(FlatRegex::Test(edit));
        let root = source.regex(FlatRegex::Star(event));
        let pair = source.finish(root);
        let request = [ACTOR, 99, DOC];

        assert!(accepts(&pair, &request, &[]));
        assert!(accepts(&pair, &request, &[[ACTOR, EDIT, DOC]; 3]));
        assert!(!accepts(
            &pair,
            &request,
            &[[ACTOR, EDIT, DOC], [ACTOR, REMOVE, DOC]]
        ));
    }

    #[test]
    fn head_constants_must_match_the_request() {
        let head = [FlatHead::Constant(EDIT), FlatHead::Any, FlatHead::Bind];
        assert!(head_matches(&head, &[EDIT, 1, 2]));
        assert!(!head_matches(&head, &[EDIT + 1, 1, 2]));
        assert!(!head_matches(&head, &[EDIT, 1]));
    }

    #[test]
    fn deep_sources_exceed_the_depth_budget() {
        let mut source = Source::new();
        let mut node = source.regex(FlatRegex::Epsilon);
        for _ in 0..=MAX_REFERENCE_DEPTH {
            node = source.regex(FlatRegex::Complement(node));
        }
        let pair = source.finish(node);
        assert_eq!(
            Lang::inflate(&pair, &mut Unmetered),
            Err(HistoryError::GraphBudget {
                limit: MAX_REFERENCE_DEPTH
            })
        );
    }

    #[test]
    fn shared_subterms_exceed_the_node_budget() {
        // Each level doubles the inflated tree: 2^17 leaves exceed the node cap.
        let mut source = Source::new();
        let mut node = source.regex(FlatRegex::Epsilon);
        for _ in 0..17 {
            node = source.regex(FlatRegex::Union(vec![node, node]));
        }
        let pair = source.finish(node);
        assert_eq!(
            Lang::inflate(&pair, &mut Unmetered),
            Err(HistoryError::GraphBudget {
                limit: MAX_REFERENCE_NODES
            })
        );
    }
}
