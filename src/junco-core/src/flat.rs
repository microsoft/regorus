//! Portable, store-independent source tables and their checked construction boundary.

use crate::error::HistoryError;
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use alloc::string::String;
use alloc::vec::Vec;
use history_syntax::syntax::{Component, RuleMode};
use vstd::prelude::*;

#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatHead<C> {
    Any,
    Constant(C),
    Bind,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatTerm<C> {
    Constant(C),
    Variable(Component),
}

#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatTest<C> {
    Bool(bool),
    Atom {
        field: Component,
        term: FlatTerm<C>,
        positive: bool,
    },
    And(Vec<u32>),
    Or(Vec<u32>),
}

// Variant order and names are the version-8 portable wire format.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatRegex {
    Empty,
    All,
    Epsilon,
    Test(u32),
    Concat(Vec<u32>),
    Union(Vec<u32>),
    Intersect(Vec<u32>),
    Star(u32),
    Complement(u32),
}

/// References are backward within their own table; the root need not be last.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatPair<C> {
    pub head: [FlatHead<C>; 3],
    pub tests: Vec<FlatTest<C>>,
    pub regexes: Vec<FlatRegex>,
    pub root: u32,
}

#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatRule<C> {
    pub mode: RuleMode,
    pub source: FlatPair<C>,
}

#[cfg(verus_keep_ghost)]
pub mod verify {
    use super::*;

    verus! {
    impl View for FlatHead<u64> {
        type V = crate::verify::history_specs::HeadField;
        open spec fn view(&self) -> crate::verify::history_specs::HeadField {
            match self {
                FlatHead::Any => crate::verify::history_specs::HeadField::Any,
                FlatHead::Constant(value) => crate::verify::history_specs::HeadField::Constant(*value as nat),
                FlatHead::Bind => crate::verify::history_specs::HeadField::Bind,
            }
        }
    }

    broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

    pub open spec fn field_index(field: Component) -> int {
        match field { Component::Principal => 0, Component::Action => 1, Component::Resource => 2 }
    }

    pub open spec fn references_before(children: Seq<u32>, bound: nat) -> bool {
        forall|i: int| 0 <= i < children.len() ==> #[trigger] children[i] < bound
    }

    pub open spec fn test_wf<C>(head: Seq<FlatHead<C>>, test: FlatTest<C>, index: nat) -> bool {
        match test {
            FlatTest::Bool(_) => true,
            FlatTest::Atom { field, term: FlatTerm::Variable(variable), .. } =>
                field == variable && head[field_index(field)] is Bind,
            FlatTest::Atom { .. } => true,
            FlatTest::And(children) | FlatTest::Or(children) => references_before(children@, index),
        }
    }

    pub open spec fn regex_wf(regex: FlatRegex, index: nat, tests: nat) -> bool {
        match regex {
            FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => true,
            FlatRegex::Test(test) => test < tests,
            FlatRegex::Concat(children) | FlatRegex::Union(children) | FlatRegex::Intersect(children) =>
                references_before(children@, index),
            FlatRegex::Star(child) | FlatRegex::Complement(child) => child < index,
        }
    }

    pub open spec fn prefix_wf<C>(
        head: Seq<FlatHead<C>>, tests: Seq<FlatTest<C>>, regexes: Seq<FlatRegex>,
    ) -> bool {
        head.len() == 3
            && (forall|i: int| 0 <= i < tests.len() ==> test_wf(head, #[trigger] tests[i], i as nat))
            && (forall|i: int| 0 <= i < regexes.len() ==>
                regex_wf(#[trigger] regexes[i], i as nat, tests.len()))
    }

    pub open spec fn structural_wf<C>(pair: FlatPair<C>) -> bool {
        prefix_wf(pair.head@, pair.tests@, pair.regexes@) && pair.root < pair.regexes@.len()
    }

    pub open spec fn event_wf<C>(event: Seq<C>) -> bool { event.len() == 3 }

    /// Equality has the same actual/expected orientation as the owned DSL.
    pub open spec fn head_matches<C>(
        head: Seq<FlatHead<C>>, candidate: Seq<C>, eq: spec_fn(Component, C, C) -> bool,
    ) -> bool {
        head.len() == 3 && event_wf(candidate)
            && (forall|field: Component| match #[trigger] head[field_index(field)] {
                FlatHead::Constant(expected) => eq(field, candidate[field_index(field)], expected),
                _ => true,
            })
    }

    pub open spec fn test_sem<C>(
        tests: Seq<FlatTest<C>>, id: nat, candidate: Seq<C>, event: Seq<C>,
        eq: spec_fn(Component, C, C) -> bool,
    ) -> bool
        decreases id,
    {
        id < tests.len() && event_wf(candidate) && event_wf(event) && match tests[id as int] {
            FlatTest::Bool(value) => value,
            FlatTest::Atom { field, term, positive } => {
                let expected = match term {
                    FlatTerm::Constant(value) => value,
                    FlatTerm::Variable(variable) => candidate[field_index(variable)],
                };
                positive == eq(field, event[field_index(field)], expected)
            },
            FlatTest::And(children) => references_before(children@, id)
                && (forall|i: int| 0 <= i < children@.len() ==>
                    test_sem(tests, children@[i] as nat, candidate, event, eq)),
            FlatTest::Or(children) => references_before(children@, id)
                && (exists|i: int| 0 <= i < children@.len()
                    && test_sem(tests, children@[i] as nat, candidate, event, eq)),
        }
    }

    /// Whole-word languages over concrete three-coordinate events, not numeric graph states.
    pub open spec fn lang<C>(
        tests: Seq<FlatTest<C>>, regexes: Seq<FlatRegex>, id: nat,
        candidate: Seq<C>, word: Seq<Seq<C>>, eq: spec_fn(Component, C, C) -> bool,
    ) -> bool
        decreases id,
    {
        id < regexes.len() && event_wf(candidate)
            && (forall|i: int| 0 <= i < word.len() ==> event_wf(#[trigger] word[i]))
            && match regexes[id as int] {
                FlatRegex::Empty => false,
                FlatRegex::All => true,
                FlatRegex::Epsilon => word.len() == 0,
                FlatRegex::Test(test) => word.len() == 1
                    && test_sem(tests, test as nat, candidate, word[0], eq),
                FlatRegex::Union(children) => references_before(children@, id)
                    && (exists|i: int| 0 <= i < children@.len()
                        && lang(tests, regexes, children@[i] as nat, candidate, word, eq)),
                FlatRegex::Intersect(children) => references_before(children@, id)
                    && (forall|i: int| 0 <= i < children@.len() ==>
                        lang(tests, regexes, children@[i] as nat, candidate, word, eq)),
                FlatRegex::Concat(children) => references_before(children@, id)
                    && (exists|parts: Seq<Seq<Seq<C>>>| parts.len() == children@.len()
                        && word == parts.flatten()
                        && (forall|i: int| 0 <= i < children@.len() ==>
                            lang(tests, regexes, children@[i] as nat, candidate, parts[i], eq))),
                FlatRegex::Star(child) => child < id
                    && (exists|parts: Seq<Seq<Seq<C>>>| word == parts.flatten()
                        && (forall|i: int| 0 <= i < parts.len() ==>
                            lang(tests, regexes, child as nat, candidate, parts[i], eq))),
                FlatRegex::Complement(child) => child < id
                    && !lang(tests, regexes, child as nat, candidate, word, eq),
            }
    }

    /// Sharing, repeated edges and unreachable suffixes do not change a stored test.
    pub proof fn lemma_test_prefix<C>(
        tests: Seq<FlatTest<C>>, extended: Seq<FlatTest<C>>, id: nat,
        candidate: Seq<C>, event: Seq<C>, eq: spec_fn(Component, C, C) -> bool,
    )
        requires id < tests.len(), extended.len() >= tests.len(),
            extended.take(tests.len() as int) == tests,
        ensures test_sem(tests, id, candidate, event, eq)
            == test_sem(extended, id, candidate, event, eq),
        decreases id,
    {
        assert(extended[id as int] == tests[id as int]);
        match tests[id as int] {
            FlatTest::And(children) | FlatTest::Or(children) => {
                if references_before(children@, id) {
                    assert forall|i: int| 0 <= i < children@.len() implies
                        test_sem(tests, children@[i] as nat, candidate, event, eq)
                            == test_sem(extended, children@[i] as nat, candidate, event, eq) by {
                        lemma_test_prefix(tests, extended, children@[i] as nat, candidate, event, eq);
                    }
                }
            },
            _ => {},
        }
    }

    /// Appending table nodes preserves every already stored language, without unfolding its DAG.
    pub proof fn lemma_lang_prefix<C>(
        tests: Seq<FlatTest<C>>, more_tests: Seq<FlatTest<C>>,
        regexes: Seq<FlatRegex>, more_regexes: Seq<FlatRegex>, id: nat,
        candidate: Seq<C>, word: Seq<Seq<C>>, eq: spec_fn(Component, C, C) -> bool,
    )
        requires id < regexes.len(), more_tests.len() >= tests.len(),
            more_tests.take(tests.len() as int) == tests,
            more_regexes.len() >= regexes.len(), more_regexes.take(regexes.len() as int) == regexes,
            forall|i: int| 0 <= i < regexes.len() ==>
                regex_wf(#[trigger] regexes[i], i as nat, tests.len()),
        ensures lang(tests, regexes, id, candidate, word, eq)
            == lang(more_tests, more_regexes, id, candidate, word, eq),
        decreases id,
    {
        assert(more_regexes[id as int] == regexes[id as int]);
        match regexes[id as int] {
            FlatRegex::Test(test) => {
                if word.len() == 1 {
                    lemma_test_prefix(tests, more_tests, test as nat, candidate, word[0], eq);
                }
            },
            FlatRegex::Concat(children) => {
                assert forall|parts: Seq<Seq<Seq<C>>>| parts.len() == children@.len() implies
                    ((forall|i: int| 0 <= i < children@.len() ==>
                        lang(tests, regexes, children@[i] as nat, candidate, parts[i], eq))
                    == (forall|i: int| 0 <= i < children@.len() ==>
                        lang(more_tests, more_regexes, children@[i] as nat, candidate, parts[i], eq))) by {
                    assert forall|i: int| 0 <= i < children@.len() implies
                        lang(tests, regexes, children@[i] as nat, candidate, parts[i], eq)
                        == lang(more_tests, more_regexes, children@[i] as nat, candidate, parts[i], eq) by {
                        lemma_lang_prefix(tests, more_tests, regexes, more_regexes,
                            children@[i] as nat, candidate, parts[i], eq);
                    }
                }
                assert(lang(tests, regexes, id, candidate, word, eq)
                    == lang(more_tests, more_regexes, id, candidate, word, eq));
            },
            FlatRegex::Union(children) | FlatRegex::Intersect(children) => {
                assert forall|i: int| 0 <= i < children@.len() implies
                    lang(tests, regexes, children@[i] as nat, candidate, word, eq)
                        == lang(more_tests, more_regexes, children@[i] as nat, candidate, word, eq) by {
                    lemma_lang_prefix(tests, more_tests, regexes, more_regexes,
                        children@[i] as nat, candidate, word, eq);
                }
                assert(lang(tests, regexes, id, candidate, word, eq)
                    == lang(more_tests, more_regexes, id, candidate, word, eq));
            },
            FlatRegex::Star(child) => {
                assert forall|parts: Seq<Seq<Seq<C>>>| #![trigger parts.len()]
                    ((forall|i: int| 0 <= i < parts.len() ==>
                        lang(tests, regexes, child as nat, candidate, parts[i], eq))
                    == (forall|i: int| 0 <= i < parts.len() ==>
                        lang(more_tests, more_regexes, child as nat, candidate, parts[i], eq))) by {
                    assert forall|i: int| 0 <= i < parts.len() implies
                        lang(tests, regexes, child as nat, candidate, parts[i], eq)
                        == lang(more_tests, more_regexes, child as nat, candidate, parts[i], eq) by {
                        lemma_lang_prefix(tests, more_tests, regexes, more_regexes,
                            child as nat, candidate, parts[i], eq);
                    }
                }
                assert(lang(tests, regexes, id, candidate, word, eq)
                    == lang(more_tests, more_regexes, id, candidate, word, eq));
            },
            FlatRegex::Complement(child) => {
                lemma_lang_prefix(tests, more_tests, regexes, more_regexes,
                    child as nat, candidate, word, eq);
            },
            _ => {},
        }
    }

    pub proof fn lemma_empty_operators<C>(empty: Vec<u32>, candidate: Seq<C>, word: Seq<Seq<C>>,
        eq: spec_fn(Component, C, C) -> bool)
        requires empty@.len() == 0, event_wf(candidate),
            forall|i: int| 0 <= i < word.len() ==> event_wf(#[trigger] word[i]),
        ensures
            test_sem(seq![FlatTest::And(empty)], 0, candidate, candidate, eq),
            !test_sem(seq![FlatTest::Or(empty)], 0, candidate, candidate, eq),
            !lang(Seq::<FlatTest<C>>::empty(), seq![FlatRegex::Union(empty)], 0, candidate, word, eq),
            lang(Seq::<FlatTest<C>>::empty(), seq![FlatRegex::Intersect(empty)], 0, candidate, word, eq),
            lang(Seq::<FlatTest<C>>::empty(), seq![FlatRegex::Concat(empty)], 0, candidate, word, eq)
                <==> word.len() == 0,
    {
        if lang(Seq::<FlatTest<C>>::empty(), seq![FlatRegex::Concat(empty)], 0, candidate, word, eq) {
            let parts = choose|parts: Seq<Seq<Seq<C>>>| parts.len() == 0 && word == parts.flatten();
            assert(parts =~= Seq::empty());
        }
        if word.len() == 0 {
            let parts: Seq<Seq<Seq<C>>> = Seq::empty();
            assert(parts.flatten() =~= word);
            assert(lang(Seq::<FlatTest<C>>::empty(), seq![FlatRegex::Concat(empty)], 0, candidate, word, eq));
        }
    }

    pub proof fn lemma_complement_is_whole_word<C>(
        tests: Seq<FlatTest<C>>, regexes: Seq<FlatRegex>, id: nat, child: u32,
        candidate: Seq<C>, word: Seq<Seq<C>>, eq: spec_fn(Component, C, C) -> bool,
    )
        requires id < regexes.len(), regexes[id as int] == FlatRegex::Complement(child),
            child < id, event_wf(candidate),
            forall|i: int| 0 <= i < word.len() ==> event_wf(#[trigger] word[i]),
        ensures lang(tests, regexes, id, candidate, word, eq)
            <==> !lang(tests, regexes, child as nat, candidate, word, eq),
    {}
    }
}

#[verus_verify]
#[verus_spec(result => ensures result == verify::references_before(children@, bound as nat))]
fn references_before(children: &[u32], bound: usize) -> bool {
    let mut index = 0;
    #[cfg_attr(verus_keep_ghost, verus_spec(
        invariant index <= children@.len(),
            forall|i: int| 0 <= i < index ==> #[trigger] children@[i] < bound,
        decreases children@.len() - index,
    ))]
    while index < children.len() {
        let child = children[index];
        let child = match usize::try_from(child) {
            Ok(child) => child,
            Err(_) => return false,
        };
        if child >= bound {
            return false;
        }
        index += 1;
    }
    true
}

#[verus_verify]
#[verus_spec(result => ensures result == verify::test_wf(head@, *test, index as nat))]
fn test_valid<C>(head: &[FlatHead<C>; 3], test: &FlatTest<C>, index: usize) -> bool {
    match test {
        FlatTest::Bool(_) => true,
        FlatTest::Atom {
            field,
            term: FlatTerm::Variable(variable),
            ..
        } => {
            if field != variable {
                return false;
            }
            matches!(head.get(field.index()), Some(&FlatHead::Bind))
        }
        FlatTest::Atom { .. } => true,
        FlatTest::And(children) | FlatTest::Or(children) => references_before(children, index),
    }
}

#[verus_verify]
#[verus_spec(result => ensures result == verify::regex_wf(*regex, index as nat, tests as nat))]
fn regex_valid(regex: &FlatRegex, index: usize, tests: usize) -> bool {
    match regex {
        FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => true,
        FlatRegex::Test(test) => match usize::try_from(*test) {
            Ok(test) => test < tests,
            Err(_) => false,
        },
        FlatRegex::Concat(children)
        | FlatRegex::Union(children)
        | FlatRegex::Intersect(children) => references_before(children, index),
        FlatRegex::Star(child) | FlatRegex::Complement(child) => match usize::try_from(*child) {
            Ok(child) => child < index,
            Err(_) => false,
        },
    }
}

#[verus_verify]
impl<C> FlatPair<C> {
    /// Validate even when no evaluator or runtime feature is enabled.
    #[verus_spec(result => ensures result is Ok <==> verify::structural_wf(*self))]
    pub fn validate(&self) -> Result<(), String> {
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.tests@.len(),
                forall|i: int| 0 <= i < index ==>
                    verify::test_wf(self.head@, #[trigger] self.tests@[i], i as nat),
            decreases self.tests@.len() - index,
        ))]
        while index < self.tests.len() {
            let test = &self.tests[index];
            if !test_valid(&self.head, test, index) {
                return Err(String::from(match test {
                    FlatTest::Atom { .. } => "history variable must bind its own head domain",
                    _ => "history test reference must point to an earlier node",
                }));
            }
            index += 1;
        }
        index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant index <= self.regexes@.len(),
                forall|i: int| 0 <= i < self.tests@.len() ==>
                    verify::test_wf(self.head@, #[trigger] self.tests@[i], i as nat),
                forall|i: int| 0 <= i < index ==>
                    verify::regex_wf(#[trigger] self.regexes@[i], i as nat, self.tests@.len()),
            decreases self.regexes@.len() - index,
        ))]
        while index < self.regexes.len() {
            let regex = &self.regexes[index];
            if !regex_valid(regex, index, self.tests.len()) {
                return Err(String::from(match regex {
                    FlatRegex::Test(_) => "history regex test reference is out of bounds",
                    _ => "history regex reference must point to an earlier node",
                }));
            }
            index += 1;
        }
        let root = match usize::try_from(self.root) {
            Ok(root) => root,
            Err(_) => return Err(String::from("history regex root is out of bounds")),
        };
        if root >= self.regexes.len() {
            return Err(String::from("history regex root is out of bounds"));
        }
        Ok(())
    }
}

/// Checked, topology-preserving construction shared by both source frontends.
#[verus_verify]
pub struct FlatBuilder<C> {
    head: [FlatHead<C>; 3],
    tests: Vec<FlatTest<C>>,
    regexes: Vec<FlatRegex>,
}

#[cfg(verus_keep_ghost)]
verus! {
impl<C> FlatBuilder<C> {
    pub closed spec fn head_view(&self) -> Seq<FlatHead<C>> { self.head@ }
    pub closed spec fn tests_view(&self) -> Seq<FlatTest<C>> { self.tests@ }
    pub closed spec fn regexes_view(&self) -> Seq<FlatRegex> { self.regexes@ }
    pub open spec fn wf(&self) -> bool {
        verify::prefix_wf(self.head_view(), self.tests_view(), self.regexes_view())
    }
}
}

#[verus_verify]
#[verus_spec(result => ensures result is InvalidPolicy)]
fn invalid_source() -> HistoryError {
    HistoryError::InvalidPolicy {
        path: String::from("$"),
        message: "invalid portable history source",
    }
}

#[verus_verify]
impl<C> FlatBuilder<C> {
    #[verus_spec(result => ensures result.wf(), result.head_view() == head@,
        result.tests_view() == Seq::<FlatTest<C>>::empty(), result.regexes_view() == Seq::<FlatRegex>::empty())]
    pub fn new(head: [FlatHead<C>; 3]) -> Self {
        proof! { reveal(FlatBuilder::head_view); reveal(FlatBuilder::tests_view); reveal(FlatBuilder::regexes_view); }
        Self {
            head,
            tests: Vec::new(),
            regexes: Vec::new(),
        }
    }

    #[verus_spec(result => ensures result@ == self.head_view())]
    pub fn head(&self) -> &[FlatHead<C>; 3] {
        proof! { reveal(FlatBuilder::head_view); }
        &self.head
    }

    #[verus_spec(result => ensures result@ == self.tests_view())]
    pub fn tests(&self) -> &Vec<FlatTest<C>> {
        proof! { reveal(FlatBuilder::tests_view); }
        &self.tests
    }

    #[verus_spec(result => ensures result@ == self.regexes_view())]
    pub fn regexes(&self) -> &Vec<FlatRegex> {
        proof! { reveal(FlatBuilder::regexes_view); }
        &self.regexes
    }

    #[verus_spec(result => requires old(self).wf(), ensures
        final(self).wf(), final(self).head_view() == old(self).head_view(),
        final(self).regexes_view() == old(self).regexes_view(),
        match result {
            Ok(id) => id == old(self).tests_view().len()
                && final(self).tests_view() == old(self).tests_view().push(node),
            Err(_) => final(self).tests_view() == old(self).tests_view(),
        },
    )]
    pub fn test<L: Limits>(
        &mut self,
        node: FlatTest<C>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<u32, HistoryError> {
        proof! { reveal(FlatBuilder::head_view); reveal(FlatBuilder::tests_view); reveal(FlatBuilder::regexes_view); }
        limits.checkpoint()?;
        if !test_valid(&self.head, &node, self.tests.len()) {
            return Err(invalid_source());
        }
        let id = match u32::try_from(self.tests.len()) {
            Ok(id) => id,
            Err(_) => return Err(HistoryError::graph_index_overflow()),
        };
        if world.try_reserve_vec(&mut self.tests, 1).is_err() {
            return Err(HistoryError::AllocationFailed);
        }
        limits.enforce_memory()?;
        proof_decl! { let ghost previous = self.tests@; }
        self.tests.push(node);
        proof! {
            assert forall|i: int| 0 <= i < self.tests@.len() implies
                verify::test_wf(self.head@, #[trigger] self.tests@[i], i as nat) by {
                if i < previous.len() { assert(self.tests@[i] == previous[i]); }
                else { assert(i == previous.len()); }
            }
            assert forall|i: int| 0 <= i < self.regexes@.len() implies
                verify::regex_wf(#[trigger] self.regexes@[i], i as nat, self.tests@.len()) by {
                assert(verify::regex_wf(self.regexes@[i], i as nat, previous.len()));
            }
        }
        Ok(id)
    }

    #[verus_spec(result => requires old(self).wf(), ensures
        final(self).wf(), final(self).head_view() == old(self).head_view(),
        final(self).tests_view() == old(self).tests_view(),
        match result {
            Ok(id) => id == old(self).regexes_view().len()
                && final(self).regexes_view() == old(self).regexes_view().push(node),
            Err(_) => final(self).regexes_view() == old(self).regexes_view(),
        },
    )]
    pub fn regex<L: Limits>(
        &mut self,
        node: FlatRegex,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<u32, HistoryError> {
        proof! { reveal(FlatBuilder::head_view); reveal(FlatBuilder::tests_view); reveal(FlatBuilder::regexes_view); }
        limits.checkpoint()?;
        if !regex_valid(&node, self.regexes.len(), self.tests.len()) {
            return Err(invalid_source());
        }
        let id = match u32::try_from(self.regexes.len()) {
            Ok(id) => id,
            Err(_) => return Err(HistoryError::graph_index_overflow()),
        };
        if world.try_reserve_vec(&mut self.regexes, 1).is_err() {
            return Err(HistoryError::AllocationFailed);
        }
        limits.enforce_memory()?;
        proof_decl! { let ghost previous = self.regexes@; }
        self.regexes.push(node);
        proof! {
            assert forall|i: int| 0 <= i < self.regexes@.len() implies
                verify::regex_wf(#[trigger] self.regexes@[i], i as nat, self.tests@.len()) by {
                if i < previous.len() { assert(self.regexes@[i] == previous[i]); }
                else { assert(i == previous.len()); }
            }
        }
        Ok(id)
    }

    #[verus_spec(result => requires self.wf(), ensures
        (result is Ok) <==> root < self.regexes_view().len(),
        match result {
            Ok(pair) => verify::structural_wf(pair) && pair.head@ == self.head_view()
                && pair.tests@ == self.tests_view() && pair.regexes@ == self.regexes_view()
                && pair.root == root,
            Err(_) => true,
        },
    )]
    pub fn finish(self, root: u32) -> Result<FlatPair<C>, HistoryError> {
        proof! { reveal(FlatBuilder::head_view); reveal(FlatBuilder::tests_view); reveal(FlatBuilder::regexes_view); }
        let pair = FlatPair {
            head: self.head,
            tests: self.tests,
            regexes: self.regexes,
            root,
        };
        if pair.validate().is_err() {
            return Err(invalid_source());
        }
        Ok(pair)
    }
}
