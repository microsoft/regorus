//! Structural and semantic clients of the actual iterative owned-source lowering.

use crate::errors::CompileError;
use crate::flat::verify as flat;
use crate::flat::{FlatHead, FlatRegex, FlatRule, FlatTerm, FlatTest};
use crate::flatten::Work;
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use crate::scope::VariableScope;
use crate::spec::semantics as dsl;
use history_syntax::Event;
use history_syntax::event::specs::EventSpec;
use history_syntax::spec::events::{AtomView, HeadView, PatternView, RegexView, TestView, arity};
use history_syntax::syntax::{
    Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
type SourceHead<E> = HeadView<<E as Event>::Component>;
type SourceTest<E> = TestView<<E as Event>::Component>;
type SourceRegex<E> = RegexView<<E as Event>::Component>;
type SourceEvent<E> = Seq<<E as Event>::Component>;

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// Tagged component equality is already the event type's own equality contract.
pub open spec fn component_eq<E: Event>(_field: Component, left: E::Component, right: E::Component) -> bool {
    left.eq_spec(&right)
}

pub open spec fn component_equality<E: Event>() -> spec_fn(Component, E::Component, E::Component) -> bool {
    |field: Component, left: E::Component, right: E::Component| component_eq::<E>(field, left, right)
}

/// A typed constant belongs only to its declared product coordinate.
pub open spec fn component_domain<E: Event>() -> crate::verify::encoding::Domain<E::Component> {
    |field: Component, value: E::Component| E::coordinate_spec(value) == field.0 as nat
}

pub open spec fn head_coordinates_wf<E: Event>(head: SourceHead<E>) -> bool {
    head.len() == arity::<E>() && forall|i: int| 0 <= i < head.len() ==> match #[trigger] head[i] {
        PatternView::Constant(value) => E::coordinate_spec(value) == i,
        _ => true,
    }
}

pub(crate) proof fn lemma_rule_head_coordinates<E: Event>(
    rule: history_syntax::spec::events::RuleView<E::Component>,
)
    requires rule.head.len() == arity::<E>(), dsl::rule_constants_tagged::<E>(rule),
    ensures head_coordinates_wf::<E>(rule.head),
{
    assert forall|i: int| 0 <= i < rule.head.len() implies match #[trigger] rule.head[i] {
        PatternView::Constant(value) => E::coordinate_spec(value) == i,
        _ => true,
    } by {
        if let PatternView::Constant(value) = rule.head[i] {
            assert(crate::spec::questions::head_constants(rule.head)[i].contains(value));
            assert(crate::spec::questions::rule_constants(rule)[i].contains(value));
        }
    }
}

pub open spec fn atom_coordinates_wf<E: Event>(atom: AtomView<E::Component>) -> bool {
    atom.component < arity::<E>() && match atom.pattern {
        PatternView::Constant(value) => E::coordinate_spec(value) == atom.component,
        _ => true,
    }
}

pub open spec fn head_slot_represents<C>(flat: FlatHead<C>, source: PatternView<C>) -> bool {
    match (flat, source) {
        (FlatHead::Constant(a), PatternView::Constant(b)) => a == b,
        (FlatHead::Bind, PatternView::Variable(_)) => true,
        _ => false,
    }
}

pub open spec fn head_represents<E: Event>(flat: Seq<FlatHead<E::Component>>, head: SourceHead<E>) -> bool {
    flat.len() == head.len() && head.len() == arity::<E>()
        && 1 <= head.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < head.len() ==> head_slot_represents(#[trigger] flat[i], head[i])
}

pub open spec fn scope_matches<E: Event>(scope: VariableScope<'_>, head: SourceHead<E>) -> bool {
    scope.wf() && scope.arity_spec() == head.len() && head.len() == arity::<E>()
        && 1 <= head.len() <= history_syntax::MAX_ARITY
        && forall|i: int| 0 <= i < head.len() ==> match scope.name_spec(Component(i as u8)) {
            Some(name) => dsl::pattern_name(#[trigger] head[i]) == Some(name@),
            None => dsl::pattern_name(#[trigger] head[i]) is None,
        }
}

pub open spec fn atom_term_represents<E: Event>(field: Component, term: FlatTerm<E::Component>,
    atom: AtomView<E::Component>, head: SourceHead<E>) -> bool
{
    field.0 as nat == atom.component && atom.component < head.len() && match (term, atom.pattern) {
        (FlatTerm::Constant(a), PatternView::Constant(b)) => a == b,
        (FlatTerm::Variable(bound), PatternView::Variable(name)) => bound == field
            && dsl::pattern_name(head[atom.component as int]) == Some(name),
        _ => false,
    }
}

#[verifier::opaque]
pub open spec fn test_operands<C>(node: FlatTest<C>) -> Seq<u32> {
    match node { FlatTest::And(ids) | FlatTest::Or(ids) => ids@, _ => Seq::empty() }
}

#[verifier::opaque]
pub open spec fn regex_operands(node: FlatRegex) -> Seq<u32> {
    match node { FlatRegex::Concat(ids) | FlatRegex::Union(ids) | FlatRegex::Intersect(ids) => ids@, _ => Seq::empty() }
}

pub proof fn lemma_test_operands<C>(node: FlatTest<C>)
    ensures test_operands(node) == match node { FlatTest::And(ids) | FlatTest::Or(ids) => ids@, _ => Seq::empty() },
{ reveal(test_operands); }

pub proof fn lemma_regex_operands(node: FlatRegex)
    ensures regex_operands(node) == match node {
        FlatRegex::Concat(ids) | FlatRegex::Union(ids) | FlatRegex::Intersect(ids) => ids@, _ => Seq::empty(),
    },
{ reveal(regex_operands); }

/// This is a structural relation, not the semantic equivalence that the bridge must prove.
pub open spec fn test_represents<E: Event>(tests: Seq<FlatTest<E::Component>>, id: nat,
    source: SourceTest<E>, head: SourceHead<E>) -> bool
    decreases source,
{
    id < tests.len() && dsl::test_scoped(source, head) && match source {
        TestView::True => tests[id as int] == FlatTest::Bool(true),
        TestView::False => tests[id as int] == FlatTest::Bool(false),
        TestView::Atom { comparison, pattern } => match tests[id as int] {
            FlatTest::Atom { field, term, positive } => positive == (comparison is Eq)
                && atom_term_represents::<E>(field, term, pattern, head),
            _ => false,
        },
        TestView::And(children) | TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            ((source is And && tests[id as int] is And) || (source is Or && tests[id as int] is Or))
                && children.len() == ids.len() && flat::references_before(ids, id)
                && forall|i: int| #![trigger ids[i]] 0 <= i < children.len() ==>
                    test_represents::<E>(tests, ids[i] as nat, children[i], head)
        },
    }
}

pub open spec fn regex_represents<E: Event>(tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>, id: nat,
    source: SourceRegex<E>, head: SourceHead<E>) -> bool
    decreases source,
{
    id < regexes.len() && dsl::regex_scoped(source, head) && match source {
        RegexView::Empty => regexes[id as int] is Empty,
        RegexView::All => regexes[id as int] is All,
        RegexView::Epsilon => regexes[id as int] is Epsilon,
        RegexView::Test(test) => match regexes[id as int] {
            FlatRegex::Test(test_id) => test_represents::<E>(tests, test_id as nat, test, head),
            _ => false,
        },
        RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            ((source is Concat && regexes[id as int] is Concat)
                || (source is Union && regexes[id as int] is Union)
                || (source is Intersect && regexes[id as int] is Intersect))
                && children.len() == ids.len() && flat::references_before(ids, id)
                && forall|i: int| #![trigger ids[i]] 0 <= i < children.len() ==>
                    regex_represents::<E>(tests, regexes, ids[i] as nat, children[i], head)
        },
        RegexView::Star(child) | RegexView::Not(child) =>
            ((source is Star && regexes[id as int] is Star) || (source is Not && regexes[id as int] is Complement))
            && match regexes[id as int] {
                FlatRegex::Star(child_id) | FlatRegex::Complement(child_id) => child_id < id
                    && regex_represents::<E>(tests, regexes, child_id as nat, *child, head),
                _ => false,
            },
    }
}

pub open spec fn flattened<E: Event>(rule: Rule<E>, flat_rule: FlatRule<E::Component>) -> bool {
    flat_rule.mode == rule.mode && flat::structural_wf(flat_rule.source)
        && dsl::head_scoped(rule.head@) && head_represents::<E>(flat_rule.source.head@, rule.head@)
        && regex_represents::<E>(flat_rule.source.tests@, flat_rule.source.regexes@,
            flat_rule.source.root as nat, rule.tail@, rule.head@)
        && forall|i: int| 0 <= i < flat_rule.source.tests@.len()
            ==> flat_test_within(#[trigger] flat_rule.source.tests@[i], rule.tail@)
}

pub open spec fn test_views<E: Event>(children: Seq<TestExpr<E>>) -> Seq<SourceTest<E>> {
    children.map(|i: int, child: TestExpr<E>| child@)
}
pub open spec fn regex_views<E: Event>(children: Seq<RegexExpr<E>>) -> Seq<SourceRegex<E>> {
    children.map(|i: int, child: RegexExpr<E>| child@)
}

pub open spec fn result_stacks<E: Event>(tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>,
    test_ids: Seq<u32>, regex_ids: Seq<u32>, test_sources: Seq<SourceTest<E>>, regex_sources: Seq<SourceRegex<E>>,
    head: SourceHead<E>) -> bool
{
    test_ids.len() == test_sources.len() && regex_ids.len() == regex_sources.len()
        && (forall|i: int| 0 <= i < test_ids.len() ==>
            #[trigger] test_represents::<E>(tests, test_ids[i] as nat, test_sources[i], head))
        && (forall|i: int| 0 <= i < regex_ids.len() ==>
            #[trigger] regex_represents::<E>(tests, regexes, regex_ids[i] as nat, regex_sources[i], head))
}

/// Pending source visits inherit scope; finish frames retain that same source.
#[verifier::opaque]
pub(crate) open spec fn work_scoped<E: Event>(work: Seq<Work<'_, E>>, head: SourceHead<E>) -> bool {
    forall|i: int| 0 <= i < work.len() ==> match #[trigger] work[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    }
}

pub(crate) proof fn lemma_work_scoped_push<'a, E: Event>(work: Seq<Work<'a, E>>,
    task: Work<'a, E>, head: SourceHead<E>)
    requires work_scoped::<E>(work, head), match task {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    },
    ensures work_scoped::<E>(work.push(task), head),
{
    reveal(work_scoped);
    assert forall|i: int| 0 <= i < work.push(task).len() implies match #[trigger] work.push(task)[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    } by {
        if i < work.len() { assert(work.push(task)[i] == work[i]); }
        else { assert(i == work.len()); }
    }
}

pub(crate) proof fn lemma_work_scoped_pop<E: Event>(work: Seq<Work<'_, E>>, head: SourceHead<E>)
    requires work_scoped::<E>(work, head), work.len() > 0,
    ensures work_scoped::<E>(work.drop_last(), head), match work.last() {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    },
{
    reveal(work_scoped);
    assert forall|i: int| 0 <= i < work.drop_last().len() implies match #[trigger] work.drop_last()[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => dsl::regex_scoped(source@, head),
        Work::Test(source) | Work::FinishTest(source, _) => dsl::test_scoped(source@, head),
    } by { assert(work.drop_last()[i] == work[i]); }
}

// ----- the constants a flattening may intern are the rule's (the analyzer's `known`) -----

/// `source` compares each coordinate only against constants `tail` does (a sub-term of `tail`).
pub open spec fn regex_constants_within<C>(source: RegexView<C>, tail: RegexView<C>) -> bool {
    forall|k: int| (#[trigger] crate::spec::questions::regex_constant_at(source, k))
        .subset_of(crate::spec::questions::regex_constant_at(tail, k))
}

pub open spec fn test_constants_within<C>(source: TestView<C>, tail: RegexView<C>) -> bool {
    forall|k: int| (#[trigger] crate::spec::questions::test_constant_at(source, k))
        .subset_of(crate::spec::questions::regex_constant_at(tail, k))
}

/// A flat atom's constant is one `tail` compares its field against.
pub open spec fn flat_test_within<C>(test: FlatTest<C>, tail: RegexView<C>) -> bool {
    match test {
        FlatTest::Atom { field, term: FlatTerm::Constant(value), .. } =>
            crate::spec::questions::regex_constant_at(tail, field.0 as int).contains(value),
        _ => true,
    }
}

/// Every pending source is a sub-term of the tail (its constants are among the tail's).
#[verifier::opaque]
pub(crate) open spec fn work_within<E: Event>(work: Seq<Work<'_, E>>, tail: SourceRegex<E>) -> bool {
    forall|i: int| 0 <= i < work.len() ==> match #[trigger] work[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => regex_constants_within(source@, tail),
        Work::Test(source) | Work::FinishTest(source, _) => test_constants_within(source@, tail),
    }
}

pub(crate) proof fn lemma_work_within_push<'a, E: Event>(work: Seq<Work<'a, E>>,
    task: Work<'a, E>, tail: SourceRegex<E>)
    requires work_within::<E>(work, tail), match task {
        Work::Regex(source) | Work::FinishRegex(source, _) => regex_constants_within(source@, tail),
        Work::Test(source) | Work::FinishTest(source, _) => test_constants_within(source@, tail),
    },
    ensures work_within::<E>(work.push(task), tail),
{
    reveal(work_within);
    assert forall|i: int| 0 <= i < work.push(task).len() implies match #[trigger] work.push(task)[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => regex_constants_within(source@, tail),
        Work::Test(source) | Work::FinishTest(source, _) => test_constants_within(source@, tail),
    } by {
        if i < work.len() { assert(work.push(task)[i] == work[i]); }
        else { assert(i == work.len()); }
    }
}

pub(crate) proof fn lemma_work_within_pop<E: Event>(work: Seq<Work<'_, E>>, tail: SourceRegex<E>)
    requires work_within::<E>(work, tail), work.len() > 0,
    ensures work_within::<E>(work.drop_last(), tail), match work.last() {
        Work::Regex(source) | Work::FinishRegex(source, _) => regex_constants_within(source@, tail),
        Work::Test(source) | Work::FinishTest(source, _) => test_constants_within(source@, tail),
    },
{
    reveal(work_within);
    assert forall|i: int| 0 <= i < work.drop_last().len() implies match #[trigger] work.drop_last()[i] {
        Work::Regex(source) | Work::FinishRegex(source, _) => regex_constants_within(source@, tail),
        Work::Test(source) | Work::FinishTest(source, _) => test_constants_within(source@, tail),
    } by { assert(work.drop_last()[i] == work[i]); }
}

/// A member of a forest contributes to the forest's constants.
pub proof fn lemma_regex_forest_member<C>(regexes: Seq<RegexView<C>>, i: int, k: int)
    requires 0 <= i < regexes.len(),
    ensures crate::spec::questions::regex_constant_at(regexes[i], k)
        .subset_of(crate::spec::questions::regex_constant_forest(regexes, k)),
    decreases regexes.len(),
{
    if i < regexes.len() - 1 {
        lemma_regex_forest_member(regexes.drop_last(), i, k);
        assert(regexes.drop_last()[i] == regexes[i]);
    }
}

pub proof fn lemma_test_forest_member<C>(tests: Seq<TestView<C>>, i: int, k: int)
    requires 0 <= i < tests.len(),
    ensures crate::spec::questions::test_constant_at(tests[i], k)
        .subset_of(crate::spec::questions::test_constant_forest(tests, k)),
    decreases tests.len(),
{
    if i < tests.len() - 1 {
        lemma_test_forest_member(tests.drop_last(), i, k);
        assert(tests.drop_last()[i] == tests[i]);
    }
}

/// Children of a composite are sub-terms of it.
pub proof fn lemma_regex_children_within<C>(children: Seq<RegexView<C>>, source: RegexView<C>, tail: RegexView<C>)
    requires regex_constants_within(source, tail),
        source == RegexView::Concat(children) || source == RegexView::Union(children) || source == RegexView::Intersect(children),
    ensures forall|i: int| 0 <= i < children.len() ==> regex_constants_within(#[trigger] children[i], tail),
{
    assert forall|i: int| 0 <= i < children.len() implies regex_constants_within(#[trigger] children[i], tail) by {
        assert forall|k: int| (#[trigger] crate::spec::questions::regex_constant_at(children[i], k))
            .subset_of(crate::spec::questions::regex_constant_at(tail, k)) by {
            lemma_regex_forest_member(children, i, k);
            assert(crate::spec::questions::regex_constant_at(source, k)
                == crate::spec::questions::regex_constant_forest(children, k));
        }
    }
}

pub proof fn lemma_test_children_within<C>(children: Seq<TestView<C>>, source: TestView<C>, tail: RegexView<C>)
    requires test_constants_within(source, tail),
        source == TestView::And(children) || source == TestView::Or(children),
    ensures forall|i: int| 0 <= i < children.len() ==> test_constants_within(#[trigger] children[i], tail),
{
    assert forall|i: int| 0 <= i < children.len() implies test_constants_within(#[trigger] children[i], tail) by {
        assert forall|k: int| (#[trigger] crate::spec::questions::test_constant_at(children[i], k))
            .subset_of(crate::spec::questions::regex_constant_at(tail, k)) by {
            lemma_test_forest_member(children, i, k);
            assert(crate::spec::questions::test_constant_at(source, k)
                == crate::spec::questions::test_constant_forest(children, k));
        }
    }
}

/// Every constant a flattening can intern is a constant of the rule at that coordinate (the
/// analyzer specification's `known` after `add_rule` is `known_with(.., rule_constants(rule))`).
pub proof fn lemma_flattened_constants<E: Event>(rule: Rule<E>, flat: FlatRule<E::Component>)
    requires flattened::<E>(rule, flat),
    ensures forall|f: Component, v: E::Component| #[trigger] crate::verify::encoding::source_constant(flat.source, f, v)
        ==> f.0 < rule.head@.len() && crate::spec::questions::rule_constants(rule@)[f.0 as int].contains(v),
{
    assert forall|f: Component, v: E::Component| #[trigger] crate::verify::encoding::source_constant(flat.source, f, v)
        implies f.0 < rule.head@.len() && crate::spec::questions::rule_constants(rule@)[f.0 as int].contains(v) by {
        let source = flat.source;
        if exists|i: int| 0 <= i < source.head@.len() && crate::verify::encoding::field_at(i) == f
            && (#[trigger] source.head@[i]) == FlatHead::Constant(v) {
            let i = choose|i: int| 0 <= i < source.head@.len() && crate::verify::encoding::field_at(i) == f
                && (#[trigger] source.head@[i]) == FlatHead::Constant(v);
            assert(head_slot_represents(source.head@[i], rule.head@[i]));
            assert(rule.head@[i] == PatternView::Constant(v));
            assert(crate::spec::questions::head_constants(rule.head@)[i].contains(v));
            assert(f.0 as int == i);
        } else {
            let i = choose|i: int| 0 <= i < source.tests@.len() && match #[trigger] source.tests@[i] {
                FlatTest::Atom { field: f2, term: FlatTerm::Constant(v2), .. } => f2 == f && v2 == v,
                _ => false,
            };
            assert(flat_test_within(source.tests@[i], rule.tail@));
            assert(flat::test_wf(source.head@, source.tests@[i], i as nat));
            assert(f.0 < source.head@.len());
            assert(crate::spec::questions::regex_constants(rule.tail@, rule.head@.len())[f.0 as int].contains(v));
        }
    }
}

/// Erased continuation interpreter: visits contribute original views; finish frames check order.
/// It neither evaluates policies nor reconstructs any executable source tree.
#[verifier::opaque]
pub(crate) open spec fn run_work<E: Event>(work: Seq<Work<'_, E>>, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>)
    -> Option<(Seq<SourceTest<E>>, Seq<SourceRegex<E>>)>
    decreases work.len(),
{
    if work.len() == 0 { Some((tests, regexes)) }
    else {
        let rest = work.drop_last();
        match work.last() {
            Work::Regex(source) => run_work::<E>(rest, tests, regexes.push(source@)),
            Work::Test(source) => run_work::<E>(rest, tests.push(source@), regexes),
            Work::FinishTest(source, start) => match source@ {
                TestView::And(children) | TestView::Or(children) =>
                    if start <= tests.len() && tests.subrange(start as int, tests.len() as int) == children {
                        run_work::<E>(rest, tests.take(start as int).push(source@), regexes)
                    } else { None },
                _ => None,
            },
            Work::FinishRegex(source, start) => match source@ {
                RegexView::Test(child) =>
                    if tests.len() == start + 1 && tests[start as int] == child {
                        run_work::<E>(rest, tests.take(start as int), regexes.push(source@))
                    } else { None },
                RegexView::Star(child) | RegexView::Not(child) =>
                    if regexes.len() == start + 1 && regexes[start as int] == *child {
                        run_work::<E>(rest, tests, regexes.take(start as int).push(source@))
                    } else { None },
                RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) =>
                    if start <= regexes.len() && regexes.subrange(start as int, regexes.len() as int) == children {
                        run_work::<E>(rest, tests, regexes.take(start as int).push(source@))
                    } else { None },
                _ => None,
            },
        }
    }
}

/// A successful continuation fixes the next frame's operands and successor stacks.
pub(crate) proof fn lemma_run_work_step<E: Event>(work: Seq<Work<'_, E>>,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>)
    requires work.len() > 0, run_work::<E>(work, tests, regexes) is Some,
    ensures match work.last() {
        Work::Regex(source) => run_work::<E>(work.drop_last(), tests, regexes.push(source@))
            == run_work::<E>(work, tests, regexes),
        Work::Test(source) => run_work::<E>(work.drop_last(), tests.push(source@), regexes)
            == run_work::<E>(work, tests, regexes),
        Work::FinishTest(source, start) => match source@ {
            TestView::And(children) | TestView::Or(children) => start <= tests.len()
                && tests.subrange(start as int, tests.len() as int) == children
                && run_work::<E>(work.drop_last(), tests.take(start as int).push(source@), regexes)
                    == run_work::<E>(work, tests, regexes),
            _ => false,
        },
        Work::FinishRegex(source, start) => match source@ {
            RegexView::Test(child) => tests.len() == start + 1 && tests[start as int] == child
                && run_work::<E>(work.drop_last(), tests.take(start as int), regexes.push(source@))
                    == run_work::<E>(work, tests, regexes),
            RegexView::Star(child) | RegexView::Not(child) => regexes.len() == start + 1
                && regexes[start as int] == *child
                && run_work::<E>(work.drop_last(), tests, regexes.take(start as int).push(source@))
                    == run_work::<E>(work, tests, regexes),
            RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) =>
                start <= regexes.len()
                && regexes.subrange(start as int, regexes.len() as int) == children
                && run_work::<E>(work.drop_last(), tests, regexes.take(start as int).push(source@))
                    == run_work::<E>(work, tests, regexes),
            _ => false,
        },
    },
{
    reveal_with_fuel(run_work, 1);
}

pub(crate) proof fn lemma_finish_test<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a TestExpr<E>, start: usize,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, children: Seq<SourceTest<E>>, head: SourceHead<E>,
    tail: SourceRegex<E>)
    requires start == tests.len(), source@ == TestView::And(children) || source@ == TestView::Or(children),
    ensures run_work::<E>(work.push(Work::FinishTest(source, start)), tests + children, regexes)
        == run_work::<E>(work, tests.push(source@), regexes),
        work_scoped::<E>(work, head) && dsl::test_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishTest(source, start)), head)
            && (forall|i: int| 0 <= i < children.len() ==> dsl::test_scoped(#[trigger] children[i], head)),
        work_within::<E>(work, tail) && test_constants_within(source@, tail) ==>
            work_within::<E>(work.push(Work::FinishTest(source, start)), tail)
            && (forall|i: int| 0 <= i < children.len() ==> test_constants_within(#[trigger] children[i], tail)),
{
    hide(dsl::test_scoped);
    if work_scoped::<E>(work, head) && dsl::test_scoped(source@, head) {
        assert(forall|i: int| 0 <= i < children.len() ==> dsl::test_scoped(#[trigger] children[i], head)) by {
            reveal_with_fuel(dsl::test_scoped, 1);
        }
        lemma_work_scoped_push::<E>(work, Work::FinishTest(source, start), head);
    }
    if work_within::<E>(work, tail) && test_constants_within(source@, tail) {
        lemma_test_children_within(children, source@, tail);
        lemma_work_within_push::<E>(work, Work::FinishTest(source, start), tail);
    }
    let operands = tests + children;
    assert(operands.subrange(start as int, operands.len() as int) =~= children);
    assert(operands.take(start as int) =~= tests);
    assert(work.push(Work::FinishTest(source, start)).drop_last() =~= work);
    reveal_with_fuel(run_work, 2);
}

pub(crate) proof fn lemma_visit_test_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, child: &'a TestExpr<E>,
    start: usize, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, head: SourceHead<E>, tail: SourceRegex<E>)
    requires start == tests.len(), source@ == RegexView::Test(child@),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Test(child)), tests, regexes)
        == run_work::<E>(work, tests, regexes.push(source@)),
        work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Test(child)), head),
        work_within::<E>(work, tail) && regex_constants_within(source@, tail) ==>
            work_within::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Test(child)), tail),
{
    if work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) {
        reveal_with_fuel(dsl::regex_scoped, 1);
        lemma_work_scoped_push::<E>(work, Work::FinishRegex(source, start), head);
        lemma_work_scoped_push::<E>(work.push(Work::FinishRegex(source, start)), Work::Test(child), head);
    }
    if work_within::<E>(work, tail) && regex_constants_within(source@, tail) {
        assert forall|k: int| (#[trigger] crate::spec::questions::test_constant_at(child@, k))
            .subset_of(crate::spec::questions::regex_constant_at(tail, k)) by {
            assert(crate::spec::questions::regex_constant_at(source@, k) == crate::spec::questions::test_constant_at(child@, k));
        }
        lemma_work_within_push::<E>(work, Work::FinishRegex(source, start), tail);
        lemma_work_within_push::<E>(work.push(Work::FinishRegex(source, start)), Work::Test(child), tail);
    }
    let finish = work.push(Work::FinishRegex(source, start));
    let program = finish.push(Work::Test(child));
    assert(program.drop_last() =~= finish);
    assert(finish.drop_last() =~= work);
    assert(tests.push(child@).take(start as int) =~= tests);
    reveal_with_fuel(run_work, 3);
}

pub(crate) proof fn lemma_visit_unary_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, child: &'a RegexExpr<E>,
    start: usize, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, head: SourceHead<E>, tail: SourceRegex<E>)
    requires start == regexes.len(), source@ == RegexView::Star(alloc::boxed::Box::new(child@))
        || source@ == RegexView::Not(alloc::boxed::Box::new(child@)),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Regex(child)), tests, regexes)
        == run_work::<E>(work, tests, regexes.push(source@)),
        work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Regex(child)), head),
        work_within::<E>(work, tail) && regex_constants_within(source@, tail) ==>
            work_within::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Regex(child)), tail),
{
    if work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) {
        reveal_with_fuel(dsl::regex_scoped, 1);
        lemma_work_scoped_push::<E>(work, Work::FinishRegex(source, start), head);
        lemma_work_scoped_push::<E>(work.push(Work::FinishRegex(source, start)), Work::Regex(child), head);
    }
    if work_within::<E>(work, tail) && regex_constants_within(source@, tail) {
        assert forall|k: int| (#[trigger] crate::spec::questions::regex_constant_at(child@, k))
            .subset_of(crate::spec::questions::regex_constant_at(tail, k)) by {
            assert(crate::spec::questions::regex_constant_at(source@, k) == crate::spec::questions::regex_constant_at(child@, k));
        }
        lemma_work_within_push::<E>(work, Work::FinishRegex(source, start), tail);
        lemma_work_within_push::<E>(work.push(Work::FinishRegex(source, start)), Work::Regex(child), tail);
    }
    let finish = work.push(Work::FinishRegex(source, start));
    let program = finish.push(Work::Regex(child));
    assert(program.drop_last() =~= finish);
    assert(finish.drop_last() =~= work);
    assert(regexes.push(child@).take(start as int) =~= regexes);
    reveal_with_fuel(run_work, 3);
}

pub(crate) proof fn lemma_finish_many_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, start: usize,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, children: Seq<SourceRegex<E>>, head: SourceHead<E>,
    tail: SourceRegex<E>)
    requires start == regexes.len(), source@ == RegexView::Concat(children)
        || source@ == RegexView::Union(children) || source@ == RegexView::Intersect(children),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)), tests, regexes + children)
        == run_work::<E>(work, tests, regexes.push(source@)),
        work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) ==>
            work_scoped::<E>(work.push(Work::FinishRegex(source, start)), head)
            && (forall|i: int| 0 <= i < children.len() ==> dsl::regex_scoped(#[trigger] children[i], head)),
        work_within::<E>(work, tail) && regex_constants_within(source@, tail) ==>
            work_within::<E>(work.push(Work::FinishRegex(source, start)), tail)
            && (forall|i: int| 0 <= i < children.len() ==> regex_constants_within(#[trigger] children[i], tail)),
{
    hide(dsl::regex_scoped);
    if work_scoped::<E>(work, head) && dsl::regex_scoped(source@, head) {
        assert(forall|i: int| 0 <= i < children.len() ==> dsl::regex_scoped(#[trigger] children[i], head)) by {
            reveal_with_fuel(dsl::regex_scoped, 1);
        }
        lemma_work_scoped_push::<E>(work, Work::FinishRegex(source, start), head);
    }
    if work_within::<E>(work, tail) && regex_constants_within(source@, tail) {
        lemma_regex_children_within(children, source@, tail);
        lemma_work_within_push::<E>(work, Work::FinishRegex(source, start), tail);
    }
    let operands = regexes + children;
    assert(operands.subrange(start as int, operands.len() as int) =~= children);
    assert(operands.take(start as int) =~= regexes);
    assert(work.push(Work::FinishRegex(source, start)).drop_last() =~= work);
    reveal_with_fuel(run_work, 2);
}

pub open spec fn test_cost<E: Event>(test: SourceTest<E>) -> nat
    decreases test,
{
    match test {
        TestView::And(children) | TestView::Or(children) => 2 + test_forest_cost::<E>(children),
        _ => 1,
    }
}
pub open spec fn test_forest_cost<E: Event>(tests: Seq<SourceTest<E>>) -> nat
    decreases tests,
{
    if tests.len() == 0 { 0 } else { test_forest_cost::<E>(tests.drop_last()) + test_cost::<E>(tests.last()) }
}
pub open spec fn regex_cost<E: Event>(regex: SourceRegex<E>) -> nat
    decreases regex,
{
    match regex {
        RegexView::Test(test) => 2 + test_cost::<E>(test),
        RegexView::Star(child) | RegexView::Not(child) => 2 + regex_cost::<E>(*child),
        RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) => 2 + regex_forest_cost::<E>(children),
        _ => 1,
    }
}
pub open spec fn regex_forest_cost<E: Event>(regexes: Seq<SourceRegex<E>>) -> nat
    decreases regexes,
{
    if regexes.len() == 0 { 0 } else { regex_forest_cost::<E>(regexes.drop_last()) + regex_cost::<E>(regexes.last()) }
}
pub(crate) open spec fn work_cost<E: Event>(work: Seq<Work<'_, E>>) -> nat
    decreases work.len(),
{
    if work.len() == 0 { 0 }
    else { work_cost::<E>(work.drop_last()) + match work.last() {
        Work::Regex(source) => regex_cost::<E>(source@),
        Work::Test(source) => test_cost::<E>(source@),
        _ => 1,
    } }
}

pub(crate) proof fn lemma_work_cost_push<'a, E: Event>(work: Seq<Work<'a, E>>, task: Work<'a, E>)
    ensures work_cost::<E>(work.push(task)) == work_cost::<E>(work) + match task {
        Work::Regex(source) => regex_cost::<E>(source@),
        Work::Test(source) => test_cost::<E>(source@),
        _ => 1,
    },
{
    assert(work.push(task).drop_last() =~= work);
    assert(work.push(task).last() == task);
    reveal_with_fuel(work_cost, 1);
}


pub proof fn lemma_test_forest_cost_append<E: Event>(left: Seq<SourceTest<E>>, right: Seq<SourceTest<E>>)
    ensures test_forest_cost::<E>(left + right) == test_forest_cost::<E>(left) + test_forest_cost::<E>(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_test_forest_cost_append::<E>(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    } else { assert(left + right =~= left); }
}

pub proof fn lemma_regex_forest_cost_append<E: Event>(left: Seq<SourceRegex<E>>, right: Seq<SourceRegex<E>>)
    ensures regex_forest_cost::<E>(left + right) == regex_forest_cost::<E>(left) + regex_forest_cost::<E>(right),
    decreases right.len(),
{
    if right.len() > 0 {
        lemma_regex_forest_cost_append::<E>(left, right.drop_last());
        assert((left + right).drop_last() =~= left + right.drop_last());
    } else { assert(left + right =~= left); }
}

pub proof fn lemma_test_extension<E: Event>(tests: Seq<FlatTest<E::Component>>, more: Seq<FlatTest<E::Component>>,
    id: nat, source: SourceTest<E>, head: SourceHead<E>)
    requires more.len() >= tests.len(), more.take(tests.len() as int) == tests,
        test_represents::<E>(tests, id, source, head),
    ensures test_represents::<E>(more, id, source, head),
    decreases source,
{
    reveal_with_fuel(test_represents, 2);
    assert(more[id as int] == tests[id as int]);
    match source {
        TestView::And(children) | TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            assert(ids.len() == children.len());
            assert(flat::references_before(ids, id));
            assert forall|i: int| 0 <= i < children.len() implies
                test_represents::<E>(tests, ids[i] as nat, children[i], head) by {}
            assert forall|i: int| 0 <= i < children.len() implies
                test_represents::<E>(more, ids[i] as nat, children[i], head) by {
                lemma_test_extension::<E>(tests, more, ids[i] as nat, children[i], head);
            }
        },
        _ => {},
    }
}

pub proof fn lemma_regex_extension<E: Event>(tests: Seq<FlatTest<E::Component>>, more_tests: Seq<FlatTest<E::Component>>,
    regexes: Seq<FlatRegex>, more_regexes: Seq<FlatRegex>, id: nat, source: SourceRegex<E>, head: SourceHead<E>)
    requires more_tests.len() >= tests.len(), more_tests.take(tests.len() as int) == tests,
        more_regexes.len() >= regexes.len(), more_regexes.take(regexes.len() as int) == regexes,
        regex_represents::<E>(tests, regexes, id, source, head),
    ensures regex_represents::<E>(more_tests, more_regexes, id, source, head),
    decreases source,
{
    reveal_with_fuel(regex_represents, 2);
    assert(more_regexes[id as int] == regexes[id as int]);
    match source {
        RegexView::Test(test) => match regexes[id as int] {
            FlatRegex::Test(test_id) => lemma_test_extension::<E>(tests, more_tests, test_id as nat, test, head),
            _ => {},
        },
        RegexView::Concat(children) | RegexView::Union(children) | RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            assert forall|i: int| 0 <= i < children.len() implies
                regex_represents::<E>(more_tests, more_regexes, ids[i] as nat, children[i], head) by {
                lemma_regex_extension::<E>(tests, more_tests, regexes, more_regexes, ids[i] as nat, children[i], head);
            }
        },
        RegexView::Star(child) | RegexView::Not(child) => match regexes[id as int] {
            FlatRegex::Star(child_id) | FlatRegex::Complement(child_id) =>
                lemma_regex_extension::<E>(tests, more_tests, regexes, more_regexes, child_id as nat, *child, head),
            _ => {},
        },
        _ => {},
    }
}

pub proof fn lemma_stack_extension<E: Event>(tests: Seq<FlatTest<E::Component>>, more_tests: Seq<FlatTest<E::Component>>,
    regexes: Seq<FlatRegex>, more_regexes: Seq<FlatRegex>, test_ids: Seq<u32>, regex_ids: Seq<u32>,
    test_sources: Seq<SourceTest<E>>, regex_sources: Seq<SourceRegex<E>>, head: SourceHead<E>)
    requires more_tests.len() >= tests.len(), more_tests.take(tests.len() as int) == tests,
        more_regexes.len() >= regexes.len(), more_regexes.take(regexes.len() as int) == regexes,
        result_stacks::<E>(tests, regexes, test_ids, regex_ids, test_sources, regex_sources, head),
    ensures result_stacks::<E>(more_tests, more_regexes, test_ids, regex_ids, test_sources, regex_sources, head),
{
    assert forall|i: int| 0 <= i < test_ids.len() implies
        test_represents::<E>(more_tests, test_ids[i] as nat, test_sources[i], head) by {
        lemma_test_extension::<E>(tests, more_tests, test_ids[i] as nat, test_sources[i], head);
    }
    assert forall|i: int| 0 <= i < regex_ids.len() implies
        regex_represents::<E>(more_tests, more_regexes, regex_ids[i] as nat, regex_sources[i], head) by {
        lemma_regex_extension::<E>(tests, more_tests, regexes, more_regexes, regex_ids[i] as nat, regex_sources[i], head);
    }
}

pub proof fn lemma_head_semantics<E: Event>(head: Seq<FlatHead<E::Component>>, source: SourceHead<E>, candidate: SourceEvent<E>)
    requires head_represents::<E>(head, source),
    ensures flat::head_matches(head, candidate, component_equality::<E>())
        == dsl::head_matches(source, candidate),
{
    if head.len() == candidate.len() {
        assert forall|i: int| 0 <= i < head.len() implies
            (match head[i] {
                FlatHead::Constant(expected) => component_equality::<E>()(Component(i as u8), candidate[i], expected),
                _ => true,
            }) == dsl::head_pattern_matches(source[i], candidate[i]) by {
            assert(head_slot_represents(head[i], source[i]));
            match source[i] { PatternView::Constant(_) => {}, PatternView::Variable(_) => {} }
        }
    }
}

pub proof fn lemma_test_semantics<E: Event>(tests: Seq<FlatTest<E::Component>>, id: nat, source: SourceTest<E>,
    head: SourceHead<E>, candidate: SourceEvent<E>, event: SourceEvent<E>)
    requires test_represents::<E>(tests, id, source, head),
        candidate.len() == head.len(), event.len() == candidate.len(),
    ensures flat::test_sem(tests, id, candidate, event, component_equality::<E>())
        == dsl::test_sem(source, head, candidate, event),
    decreases source,
{
    reveal_with_fuel(flat::test_sem, 2);
    reveal_with_fuel(dsl::test_sem, 2);
    lemma_test_operands(tests[id as int]);
    reveal_with_fuel(test_represents, 2);
    match source {
        TestView::Atom { comparison, pattern } => {
            match tests[id as int] {
                FlatTest::Atom { field, term, positive } => {
                    match pattern.pattern {
                        PatternView::Constant(_) => {},
                        PatternView::Variable(_) => {
                            match head[pattern.component as int] {
                                PatternView::Constant(_) => {}, PatternView::Variable(_) => {},
                            }
                        },
                    }
                },
                _ => {},
            }
            assert(flat::test_sem(tests, id, candidate, event, component_equality::<E>())
                == dsl::test_sem(source, head, candidate, event));
        },
        TestView::And(children) => {
            let ids = test_operands(tests[id as int]);
            if dsl::test_sem(source, head, candidate, event) {
                assert forall|i: int| 0 <= i < ids.len() implies
                    flat::test_sem(tests, ids[i] as nat, candidate, event, component_equality::<E>()) by {
                    assert(dsl::test_sem(children[i], head, candidate, event));
                    lemma_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                }
                assert(flat::test_sem(tests, id, candidate, event, component_equality::<E>()));
            }
            if flat::test_sem(tests, id, candidate, event, component_equality::<E>()) {
                assert forall|i: int| 0 <= i < children.len() implies dsl::test_sem(children[i], head, candidate, event) by {
                    assert(flat::test_sem(tests, ids[i] as nat, candidate, event, component_equality::<E>()));
                    lemma_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                }
                assert(dsl::test_sem(source, head, candidate, event));
            }
        },
        TestView::Or(children) => {
            let ids = test_operands(tests[id as int]);
            if dsl::test_sem(source, head, candidate, event) {
                let i = choose|i: int| 0 <= i < children.len() && dsl::test_sem(children[i], head, candidate, event);
                lemma_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                assert(flat::test_sem(tests, ids[i] as nat, candidate, event, component_equality::<E>()));
                assert(flat::test_sem(tests, id, candidate, event, component_equality::<E>()));
            }
            if flat::test_sem(tests, id, candidate, event, component_equality::<E>()) {
                let i = choose|i: int| 0 <= i < ids.len()
                    && flat::test_sem(tests, ids[i] as nat, candidate, event, component_equality::<E>());
                lemma_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                assert(dsl::test_sem(children[i], head, candidate, event));
                assert(dsl::test_sem(source, head, candidate, event));
            }
        },
        _ => {},
    }
}

/// Every event in a partition retains the original word's coordinate count.
pub proof fn lemma_partition_arity<C>(parts: Seq<Seq<Seq<C>>>, arity: nat)
    requires forall|i: int| 0 <= i < parts.flatten().len() ==> parts.flatten()[i].len() == arity,
    ensures forall|i: int, j: int| 0 <= i < parts.len() && 0 <= j < parts[i].len()
        ==> parts[i][j].len() == arity,
    decreases parts.len(),
{
    if parts.len() > 0 {
        assert(parts =~= parts.drop_last().push(parts.last()));
        parts.drop_last().lemma_flatten_push(parts.last());
        let prefix = parts.drop_last().flatten();
        assert forall|j: int| 0 <= j < prefix.len() implies prefix[j].len() == arity by {
            assert(prefix[j] == parts.flatten()[j]);
        }
        lemma_partition_arity(parts.drop_last(), arity);
        assert forall|i: int, j: int| 0 <= i < parts.len() && 0 <= j < parts[i].len()
            implies parts[i][j].len() == arity by {
            if i < parts.len() - 1 { assert(parts[i] == parts.drop_last()[i]); }
            else {
                assert(parts[i] == parts.last());
                assert(parts[i][j] == parts.flatten()[prefix.len() as int + j]);
            }
        }
    }
}

pub proof fn lemma_regex_semantics<E: Event>(tests: Seq<FlatTest<E::Component>>, regexes: Seq<FlatRegex>, id: nat,
    source: SourceRegex<E>, head: SourceHead<E>, candidate: SourceEvent<E>, word: Seq<SourceEvent<E>>)
    requires regex_represents::<E>(tests, regexes, id, source, head),
        candidate.len() == head.len(),
        forall|i: int| 0 <= i < word.len() ==> word[i].len() == candidate.len(),
    ensures flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>())
        == dsl::lang(source, head, candidate, word),
    decreases source,
{
    reveal_with_fuel(flat::flat_lang, 2);
    reveal_with_fuel(dsl::lang, 2);
    lemma_regex_operands(regexes[id as int]);
    reveal_with_fuel(regex_represents, 2);
    match source {
        RegexView::Test(test) => match regexes[id as int] {
            FlatRegex::Test(test_id) => { if word.len() == 1 {
                lemma_test_semantics::<E>(tests, test_id as nat, test, head, candidate, word[0]);
            } },
            _ => {},
        },
        RegexView::Union(children) => {
            let ids = regex_operands(regexes[id as int]);
            if dsl::lang(source, head, candidate, word) {
                let i = choose|i: int| 0 <= i < children.len() && dsl::lang(children[i], head, candidate, word);
                lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, word);
                assert(flat::flat_lang(tests, regexes, ids[i] as nat, candidate, word, component_equality::<E>()));
                assert(flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()));
            }
            if flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()) {
                let i = choose|i: int| 0 <= i < ids.len()
                    && flat::flat_lang(tests, regexes, ids[i] as nat, candidate, word, component_equality::<E>());
                lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, word);
                assert(dsl::lang(children[i], head, candidate, word));
                assert(dsl::lang(source, head, candidate, word));
            }
        },
        RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            if dsl::lang(source, head, candidate, word) {
                assert forall|i: int| 0 <= i < ids.len() implies
                    flat::flat_lang(tests, regexes, ids[i] as nat, candidate, word, component_equality::<E>()) by {
                    assert(dsl::lang(children[i], head, candidate, word));
                    lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, word);
                }
                assert(flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()));
            }
            if flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()) {
                assert forall|i: int| 0 <= i < children.len() implies dsl::lang(children[i], head, candidate, word) by {
                    assert(flat::flat_lang(tests, regexes, ids[i] as nat, candidate, word, component_equality::<E>()));
                    lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, word);
                }
                assert(dsl::lang(source, head, candidate, word));
            }
        },
        RegexView::Not(child) => match regexes[id as int] {
            FlatRegex::Complement(child_id) => lemma_regex_semantics::<E>(tests, regexes, child_id as nat, *child, head, candidate, word),
            _ => {},
        },
        RegexView::Concat(children) => {
            let ids = regex_operands(regexes[id as int]);
            if dsl::lang(source, head, candidate, word) {
                let parts = choose|parts: Seq<Seq<SourceEvent<E>>>| parts.len() == children.len()
                    && word == parts.flatten() && forall|i: int| 0 <= i < children.len() ==> dsl::lang(children[i], head, candidate, parts[i]);
                lemma_partition_arity(parts, candidate.len());
                assert forall|i: int| 0 <= i < children.len() implies
                    flat::flat_lang(tests, regexes, ids[i] as nat, candidate, parts[i], component_equality::<E>()) by {
                    lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, parts[i]);
                }
                assert(flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()));
            }
            if flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()) {
                let parts = choose|parts: Seq<Seq<Seq<E::Component>>>| parts.len() == ids.len()
                    && word == parts.flatten() && forall|i: int| 0 <= i < ids.len() ==>
                        flat::flat_lang(tests, regexes, ids[i] as nat, candidate, parts[i], component_equality::<E>());
                lemma_partition_arity(parts, candidate.len());
                assert forall|i: int| 0 <= i < children.len() implies dsl::lang(children[i], head, candidate, parts[i]) by {
                    lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, parts[i]);
                }
                assert(dsl::lang(source, head, candidate, word));
            }
        },
        RegexView::Star(child) => {
            let child_id = match regexes[id as int] { FlatRegex::Star(child_id) => child_id, _ => arbitrary() };
            if dsl::lang(source, head, candidate, word) {
                let parts = choose|parts: Seq<Seq<SourceEvent<E>>>| word == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==> dsl::lang(*child, head, candidate, parts[i]);
                lemma_partition_arity(parts, candidate.len());
                assert forall|i: int| 0 <= i < parts.len() implies
                    flat::flat_lang(tests, regexes, child_id as nat, candidate, parts[i], component_equality::<E>()) by {
                    lemma_regex_semantics::<E>(tests, regexes, child_id as nat, *child, head, candidate, parts[i]);
                }
                assert(flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()));
            }
            if flat::flat_lang(tests, regexes, id, candidate, word, component_equality::<E>()) {
                let parts = choose|parts: Seq<Seq<Seq<E::Component>>>| word == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==>
                        flat::flat_lang(tests, regexes, child_id as nat, candidate, parts[i], component_equality::<E>());
                lemma_partition_arity(parts, candidate.len());
                assert forall|i: int| 0 <= i < parts.len() implies dsl::lang(*child, head, candidate, parts[i]) by {
                    lemma_regex_semantics::<E>(tests, regexes, child_id as nat, *child, head, candidate, parts[i]);
                }
                assert(dsl::lang(source, head, candidate, word));
            }
        },
        _ => {},
    }
}

/// The structural result of the executable compiler implies both independent semantic equations.
pub proof fn flattening_preserves_semantics<E: Event>(rule: Rule<E>, lowered: FlatRule<E::Component>,
    candidate: SourceEvent<E>, history: Seq<SourceEvent<E>>)
    requires flattened::<E>(rule, lowered), candidate.len() == rule.head@.len(),
        forall|i: int| 0 <= i < history.len() ==> history[i].len() == candidate.len(),
    ensures
        flat::head_matches(lowered.source.head@, candidate, component_equality::<E>())
            == dsl::head_matches(rule.head@, candidate),
        flat::flat_lang(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
            candidate, history, component_equality::<E>())
            == dsl::lang(rule.tail@, rule.head@, candidate, history),
{
    lemma_head_semantics::<E>(lowered.source.head@, rule.head@, candidate);
    lemma_regex_semantics::<E>(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
        rule.tail@, rule.head@, candidate, history);
}

/// A client of the executable body obtains the semantic bridge without a correctness precondition.
pub fn flattening_client<E: Event, L: Limits>(rule: &Rule<E>, limits: &mut L, world: &mut ObservationWorld,
    Ghost(candidate): Ghost<SourceEvent<E>>, Ghost(history): Ghost<Seq<SourceEvent<E>>>)
    -> (result: Result<FlatRule<E::Component>, CompileError>)
    requires candidate.len() == rule.head@.len(),
        forall|i: int| 0 <= i < history.len() ==> history[i].len() == candidate.len(),
    ensures crate::verify::history_specs::no_invariant_compile_failure(result),
        dsl::head_scoped(rule.head@) && dsl::regex_scoped(rule.tail@, rule.head@)
            ==> !(result matches Err(CompileError::VariableComponentConflict { .. }))
                && !(result matches Err(CompileError::UnboundVariable { .. })),
        result matches Ok(lowered) ==>
        dsl::head_scoped(rule.head@) && dsl::regex_scoped(rule.tail@, rule.head@)
        && flat::head_matches(lowered.source.head@, candidate, component_equality::<E>())
            == dsl::head_matches(rule.head@, candidate)
        && flat::flat_lang(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
            candidate, history, component_equality::<E>())
            == dsl::lang(rule.tail@, rule.head@, candidate, history),
{
    let result = crate::flatten::flatten_rule(rule, limits, world);
    proof {
        match &result {
            Ok(lowered) => flattening_preserves_semantics::<E>(*rule, *lowered, candidate, history),
            Err(_) => {},
        }
    }
    result
}

/// A named-variable proof client works at any declared event arity.
pub fn named_variable_client<E: Event, L: Limits>(head: Head<E>, name: alloc::string::String,
    component: Component, limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<FlatRule<E::Component>, CompileError>)
    requires dsl::head_scoped(head@), component.0 < head@.len(),
        dsl::pattern_name(head@[component.0 as int]) == Some(name@),
    ensures crate::verify::history_specs::no_invariant_compile_failure(result),
        !(result matches Err(CompileError::VariableComponentConflict { .. })),
        !(result matches Err(CompileError::UnboundVariable { .. })),
        result matches Ok(lowered) ==>
        lowered.source.head@[component.0 as int] is Bind && lowered.mode == RuleMode::Require
        && match lowered.source.regexes@[lowered.source.root as int] {
            FlatRegex::Test(id) => lowered.source.tests@[id as int] == (FlatTest::Atom { field: component,
                term: FlatTerm::Variable(component), positive: true }),
            _ => false,
        },
{
    let source = Rule::new(RuleMode::Require, head,
        RegexExpr::test(TestExpr::atom(history_syntax::syntax::Comparison::Eq,
            history_syntax::syntax::AtomPattern::new(component, ComponentPattern::Variable(name)))));
    let result = crate::flatten::flatten_rule(&source, limits, world);
    proof {
        reveal_with_fuel(history_syntax::spec::events::regex_view, 2);
        reveal_with_fuel(history_syntax::spec::events::test_view, 2);
        reveal_with_fuel(regex_represents, 2);
        reveal_with_fuel(test_represents, 2);
    }
    source.dispose();
    result
}

/// Constant-only heads need no invented head-binding premise.
pub fn constant_head_client<E: Event, L: Limits>(head: Head<E>, limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<FlatRule<E::Component>, CompileError>)
    requires forall|i: int| 0 <= i < head@.len() ==> head@[i] is Constant,
    ensures crate::verify::history_specs::no_invariant_compile_failure(result),
        !(result matches Err(CompileError::VariableComponentConflict { .. })),
        !(result matches Err(CompileError::UnboundVariable { .. })),
        !(result matches Err(CompileError::Runtime(crate::errors::HistoryError::InvalidPolicy { .. }))),
{
    let source = Rule::new(RuleMode::Require, head, RegexExpr::all());
    let result = crate::flatten::flatten_rule(&source, limits, world);
    source.dispose();
    result
}

}
