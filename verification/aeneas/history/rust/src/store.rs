// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
use crate::error::HistoryError;
use crate::kernel::*;
use alloc::vec::Vec;
use core::mem::size_of;

enum TestNode {
    True,
    False,
    Atom(Primitive, bool),
    And(Vec<TestId>),
    Or(Vec<TestId>),
}
impl TestNode {
    fn view(&self) -> TestView<'_> {
        match self {
            Self::True => TestView::True,
            Self::False => TestView::False,
            Self::Atom(primitive, positive) => TestView::Atom {
                primitive: *primitive,
                positive: *positive,
            },
            Self::And(ids) => TestView::And(ids),
            Self::Or(ids) => TestView::Or(ids),
        }
    }
}
enum RegexNode {
    Empty,
    All,
    Epsilon,
    Test(TestId),
    Union(Vec<RegexId>),
    Concat(Vec<RegexId>),
    Star(RegexId),
    Intersect(Vec<RegexId>),
    Not(RegexId),
}
impl RegexNode {
    fn view(&self) -> RegexKindView<'_> {
        match self {
            Self::Empty => RegexKindView::Empty,
            Self::All => RegexKindView::All,
            Self::Epsilon => RegexKindView::Epsilon,
            Self::Test(id) => RegexKindView::Test(*id),
            Self::Union(ids) => RegexKindView::Union(ids),
            Self::Concat(ids) => RegexKindView::Concat(ids),
            Self::Star(id) => RegexKindView::Star(*id),
            Self::Intersect(ids) => RegexKindView::Intersect(ids),
            Self::Not(id) => RegexKindView::Not(*id),
        }
    }
}
enum TransitionNode {
    Const(RegexId),
    If(TestId, TransitionId, TransitionId),
    Union(Vec<TransitionId>),
    Intersect(Vec<TransitionId>),
    Not(TransitionId),
    Append(TransitionId, Vec<RegexId>),
}
impl TransitionNode {
    fn view(&self) -> TransitionView<'_> {
        match self {
            Self::Const(id) => TransitionView::Const(*id),
            Self::If(test, then_transition, else_transition) => TransitionView::If {
                test: *test,
                then_transition: *then_transition,
                else_transition: *else_transition,
            },
            Self::Union(ids) => TransitionView::Union(ids),
            Self::Intersect(ids) => TransitionView::Intersect(ids),
            Self::Not(id) => TransitionView::Not(*id),
            Self::Append(transition, suffix) => TransitionView::Append {
                transition: *transition,
                suffix,
            },
        }
    }
}

// ponytail: extraction-only linear interning; replace this backend if harness size makes it impractical, never use it in production.
pub(crate) struct VecStore {
    tests: Vec<TestNode>,
    regexes: Vec<(RegexNode, bool)>,
    transitions: Vec<TransitionNode>,
    bytes: usize,
    constants: Constants,
}
const fn store_invariant() -> HistoryError {
    HistoryError::Invariant {
        message: "invalid extraction store ID",
    }
}
const fn inconsistent_nullability() -> HistoryError {
    HistoryError::Invariant {
        message: "inconsistent cached nullability",
    }
}
use self::store_invariant as invalid_store_id;
fn limit() -> HistoryError {
    HistoryError::GraphLimit {
        limit: MAX_GRAPH_BYTES,
    }
}
fn copy_ids<T: Copy>(ids: &[T]) -> KernelResult<Vec<T>> {
    let mut result = Vec::new();
    match result.try_reserve(ids.len()) {
        Ok(()) => {
            result.extend_from_slice(ids);
            Ok(result)
        }
        Err(_) => Err(HistoryError::AllocationFailed),
    }
}
fn payload<T>(base: usize, count: usize) -> KernelResult<usize> {
    match count.checked_mul(size_of::<T>()) {
        Some(extra) => match base.checked_add(extra) {
            Some(bytes) => Ok(bytes),
            None => Err(limit()),
        },
        None => Err(limit()),
    }
}
fn test_count(node: TestView<'_>) -> usize {
    match node {
        TestView::And(ids) | TestView::Or(ids) => ids.len(),
        _ => 0,
    }
}
fn regex_count(node: RegexKindView<'_>) -> usize {
    match node {
        RegexKindView::Union(ids) | RegexKindView::Concat(ids) | RegexKindView::Intersect(ids) => {
            ids.len()
        }
        _ => 0,
    }
}
fn transition_extra(node: TransitionView<'_>) -> KernelResult<usize> {
    match node {
        TransitionView::Union(ids) | TransitionView::Intersect(ids) => {
            payload::<TransitionId>(0, ids.len())
        }
        TransitionView::Append { suffix, .. } => payload::<RegexId>(0, suffix.len()),
        _ => Ok(0),
    }
}
fn own_test(node: TestView<'_>) -> KernelResult<TestNode> {
    match node {
        TestView::True => Ok(TestNode::True),
        TestView::False => Ok(TestNode::False),
        TestView::Atom {
            primitive,
            positive,
        } => Ok(TestNode::Atom(primitive, positive)),
        TestView::And(ids) => Ok(TestNode::And(copy_ids(ids)?)),
        TestView::Or(ids) => Ok(TestNode::Or(copy_ids(ids)?)),
    }
}
fn own_regex(node: RegexKindView<'_>) -> KernelResult<RegexNode> {
    match node {
        RegexKindView::Empty => Ok(RegexNode::Empty),
        RegexKindView::All => Ok(RegexNode::All),
        RegexKindView::Epsilon => Ok(RegexNode::Epsilon),
        RegexKindView::Test(id) => Ok(RegexNode::Test(id)),
        RegexKindView::Star(id) => Ok(RegexNode::Star(id)),
        RegexKindView::Not(id) => Ok(RegexNode::Not(id)),
        RegexKindView::Union(ids) => Ok(RegexNode::Union(copy_ids(ids)?)),
        RegexKindView::Concat(ids) => Ok(RegexNode::Concat(copy_ids(ids)?)),
        RegexKindView::Intersect(ids) => Ok(RegexNode::Intersect(copy_ids(ids)?)),
    }
}
fn own_transition(node: TransitionView<'_>) -> KernelResult<TransitionNode> {
    match node {
        TransitionView::Const(id) => Ok(TransitionNode::Const(id)),
        TransitionView::If {
            test,
            then_transition,
            else_transition,
        } => Ok(TransitionNode::If(test, then_transition, else_transition)),
        TransitionView::Union(ids) => Ok(TransitionNode::Union(copy_ids(ids)?)),
        TransitionView::Intersect(ids) => Ok(TransitionNode::Intersect(copy_ids(ids)?)),
        TransitionView::Not(id) => Ok(TransitionNode::Not(id)),
        TransitionView::Append { transition, suffix } => {
            Ok(TransitionNode::Append(transition, copy_ids(suffix)?))
        }
    }
}
impl VecStore {
    pub(crate) fn new() -> KernelResult<Self> {
        let mut backend = Self {
            tests: Vec::new(),
            regexes: Vec::new(),
            transitions: Vec::new(),
            bytes: 0,
            constants: Constants {
                test_true: TestId(0),
                test_false: TestId(0),
                empty: RegexId(0),
                all: RegexId(0),
                epsilon: RegexId(0),
                transition_empty: TransitionId(0),
                transition_all: TransitionId(0),
                transition_epsilon: TransitionId(0),
            },
        };
        let test_true = backend.intern_test(TestView::True)?;
        let test_false = backend.intern_test(TestView::False)?;
        let empty = backend.intern_regex(RegexKindView::Empty, false)?;
        let all = backend.intern_regex(RegexKindView::All, true)?;
        let epsilon = backend.intern_regex(RegexKindView::Epsilon, true)?;
        let transition_empty = backend.intern_transition(TransitionView::Const(empty))?;
        let transition_all = backend.intern_transition(TransitionView::Const(all))?;
        let transition_epsilon = backend.intern_transition(TransitionView::Const(epsilon))?;
        backend.constants = Constants {
            test_true,
            test_false,
            empty,
            all,
            epsilon,
            transition_empty,
            transition_all,
            transition_epsilon,
        };
        Ok(backend)
    }
    fn projected(&self, bytes: usize) -> KernelResult<usize> {
        match self.bytes.checked_add(bytes) {
            Some(total) if total <= MAX_GRAPH_BYTES => Ok(total),
            _ => Err(limit()),
        }
    }
    fn test_matches_at(&self, index: usize, node: TestView<'_>) -> KernelResult<bool> {
        match self.tests.get(index) {
            Some(candidate) => Ok(candidate.view() == node),
            None => Err(invalid_store_id()),
        }
    }
    fn regex_matches_at(&self, index: usize, node: RegexKindView<'_>) -> KernelResult<bool> {
        match self.regexes.get(index) {
            Some((candidate, _)) => Ok(candidate.view() == node),
            None => Err(invalid_store_id()),
        }
    }
    fn transition_matches_at(&self, index: usize, node: TransitionView<'_>) -> KernelResult<bool> {
        match self.transitions.get(index) {
            Some(candidate) => Ok(candidate.view() == node),
            None => Err(invalid_store_id()),
        }
    }
    fn find_test(&self, node: TestView<'_>) -> KernelResult<Option<usize>> {
        let mut index = 0usize;
        let mut found = None;
        let mut failure_state = None;
        while index < self.tests.len() && found.is_none() && failure_state.is_none() {
            match self.test_matches_at(index, node) {
                Ok(matches) => {
                    if matches {
                        found = Some(index);
                    }
                }
                Err(failure) => failure_state = Some(failure),
            }
            index = index.saturating_add(1);
        }
        match failure_state {
            Some(failure) => Err(failure),
            None => Ok(found),
        }
    }
    fn find_regex(&self, node: RegexKindView<'_>) -> KernelResult<Option<usize>> {
        let mut index = 0usize;
        let mut found = None;
        let mut failure_state = None;
        while index < self.regexes.len() && found.is_none() && failure_state.is_none() {
            match self.regex_matches_at(index, node) {
                Ok(matches) => {
                    if matches {
                        found = Some(index);
                    }
                }
                Err(failure) => failure_state = Some(failure),
            }
            index = index.saturating_add(1);
        }
        match failure_state {
            Some(failure) => Err(failure),
            None => Ok(found),
        }
    }
    fn find_transition(&self, node: TransitionView<'_>) -> KernelResult<Option<usize>> {
        let mut index = 0usize;
        let mut found = None;
        let mut failure_state = None;
        while index < self.transitions.len() && found.is_none() && failure_state.is_none() {
            match self.transition_matches_at(index, node) {
                Ok(matches) => {
                    if matches {
                        found = Some(index);
                    }
                }
                Err(failure) => failure_state = Some(failure),
            }
            index = index.saturating_add(1);
        }
        match failure_state {
            Some(failure) => Err(failure),
            None => Ok(found),
        }
    }
}
impl KernelStore for VecStore {
    fn checkpoint(&mut self) -> KernelResult<()> {
        self.projected(0)?;
        Ok(())
    }
    fn charge_aux(&mut self, bytes: usize) -> KernelResult<()> {
        self.bytes = self.projected(bytes)?;
        Ok(())
    }
    fn reserve_derivatives(
        &mut self,
        values: &mut Vec<Option<TransitionId>>,
        additional: usize,
    ) -> KernelResult<()> {
        match values.try_reserve(additional) {
            Ok(()) => Ok(()),
            Err(_) => Err(HistoryError::AllocationFailed),
        }
    }
    fn reserve_atoms(&mut self, values: &mut Vec<TestId>, additional: usize) -> KernelResult<()> {
        match values.try_reserve(additional) {
            Ok(()) => Ok(()),
            Err(_) => Err(HistoryError::AllocationFailed),
        }
    }
    fn constants(&self) -> Constants {
        self.constants
    }
    fn test(&self, id: TestId) -> KernelResult<TestView<'_>> {
        match self.tests.get(id.index()?) {
            Some(node) => Ok(node.view()),
            None => Err(invalid_store_id()),
        }
    }
    fn regex(&self, id: RegexId) -> KernelResult<RegexView<'_>> {
        match self.regexes.get(id.index()?) {
            Some((node, nullable)) => Ok(RegexView {
                kind: node.view(),
                nullable: *nullable,
            }),
            None => Err(invalid_store_id()),
        }
    }
    fn transition(&self, id: TransitionId) -> KernelResult<TransitionView<'_>> {
        match self.transitions.get(id.index()?) {
            Some(node) => Ok(node.view()),
            None => Err(invalid_store_id()),
        }
    }
    fn intern_test(&mut self, node: TestView<'_>) -> KernelResult<TestId> {
        match self.find_test(node)? {
            Some(index) => TestId::from_index(index),
            None => {
                let charge = payload::<TestId>(size_of::<TestNode>(), test_count(node))?;
                let bytes = self.projected(charge)?;
                let id = TestId::from_index(self.tests.len())?;
                match self.tests.try_reserve(1) {
                    Ok(()) => (),
                    Err(_) => return Err(HistoryError::AllocationFailed),
                }
                let owned = own_test(node)?;
                self.tests.push(owned);
                self.bytes = bytes;
                Ok(id)
            }
        }
    }
    fn intern_regex(&mut self, kind: RegexKindView<'_>, nullable: bool) -> KernelResult<RegexId> {
        match self.find_regex(kind)? {
            Some(index) => {
                let old_nullable = match self.regexes.get(index) {
                    Some((_, value)) => *value,
                    None => return Err(invalid_store_id()),
                };
                if old_nullable != nullable {
                    Err(inconsistent_nullability())
                } else {
                    RegexId::from_index(index)
                }
            }
            None => {
                let charge = payload::<RegexId>(size_of::<(RegexNode, bool)>(), regex_count(kind))?;
                let bytes = self.projected(charge)?;
                let id = RegexId::from_index(self.regexes.len())?;
                match self.regexes.try_reserve(1) {
                    Ok(()) => (),
                    Err(_) => return Err(HistoryError::AllocationFailed),
                }
                let owned = own_regex(kind)?;
                self.regexes.push((owned, nullable));
                self.bytes = bytes;
                Ok(id)
            }
        }
    }
    fn intern_transition(&mut self, node: TransitionView<'_>) -> KernelResult<TransitionId> {
        match self.find_transition(node)? {
            Some(index) => TransitionId::from_index(index),
            None => {
                let extra = transition_extra(node)?;
                let charge = match size_of::<TransitionNode>().checked_add(extra) {
                    Some(bytes) => bytes,
                    None => return Err(limit()),
                };
                let bytes = self.projected(charge)?;
                let id = TransitionId::from_index(self.transitions.len())?;
                match self.transitions.try_reserve(1) {
                    Ok(()) => (),
                    Err(_) => return Err(HistoryError::AllocationFailed),
                }
                let owned = own_transition(node)?;
                self.transitions.push(owned);
                self.bytes = bytes;
                Ok(id)
            }
        }
    }
}
