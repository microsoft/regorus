//! Structural and semantic clients of the actual iterative owned-source lowering.

use crate::error::CompileError;
use crate::flat::verify as flat;
use crate::flat::{FlatHead, FlatRegex, FlatRule, FlatTerm, FlatTest};
use crate::flatten::{ComponentValue, Work};
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use crate::scope::VariableScope;
use crate::verify::dsl::{self, EventView};
use history_syntax::Event;
use history_syntax::syntax::{
    Component, ComponentPattern, Head, RegexExpr, Rule, RuleMode, TestExpr,
};
use history_syntax::verify::dsl::{AtomView, HeadView, PatternView, RegexView, TestView};
use vstd::prelude::*;
use vstd::std_specs::cmp::PartialEqSpec;

verus! {
type SourceHead<E> = HeadView<<E as Event>::Principal, <E as Event>::Action, <E as Event>::Resource>;
type SourceTest<E> = TestView<<E as Event>::Principal, <E as Event>::Action, <E as Event>::Resource>;
type SourceRegex<E> = RegexView<<E as Event>::Principal, <E as Event>::Action, <E as Event>::Resource>;
type SourceEvent<E> = EventView<<E as Event>::Principal, <E as Event>::Action, <E as Event>::Resource>;

broadcast use {vstd::std_specs::vec::group_vec_axioms, vstd::seq::group_seq_lemmas};

/// The equality parameter exported to the flat compiler never identifies representations by `==`.
pub open spec fn component_eq<E: Event>(field: Component, left: ComponentValue<E>, right: ComponentValue<E>) -> bool {
    match (field, left, right) {
        (Component::Principal, ComponentValue::Principal(a), ComponentValue::Principal(b)) => a.eq_spec(&b),
        (Component::Action, ComponentValue::Action(a), ComponentValue::Action(b)) => a.eq_spec(&b),
        (Component::Resource, ComponentValue::Resource(a), ComponentValue::Resource(b)) => a.eq_spec(&b),
        _ => false,
    }
}

pub open spec fn component_equality<E: Event>() -> spec_fn(Component, ComponentValue<E>, ComponentValue<E>) -> bool {
    |field: Component, left: ComponentValue<E>, right: ComponentValue<E>| component_eq::<E>(field, left, right)
}

pub open spec fn event_values<E: Event>(event: SourceEvent<E>) -> Seq<ComponentValue<E>> {
    seq![ComponentValue::Principal(event.principal), ComponentValue::Action(event.action),
        ComponentValue::Resource(event.resource)]
}

pub open spec fn word_values<E: Event>(word: Seq<SourceEvent<E>>) -> Seq<Seq<ComponentValue<E>>> {
    word.map(|i: int, event: SourceEvent<E>| event_values::<E>(event))
}

pub open spec fn head_represents<E: Event>(flat: Seq<FlatHead<ComponentValue<E>>>, head: SourceHead<E>) -> bool {
    flat.len() == 3
        && match (flat[0], head.principal) {
            (FlatHead::Constant(ComponentValue::Principal(a)), PatternView::Constant(b)) => a == b,
            (FlatHead::Bind, PatternView::Variable(_)) => true,
            _ => false,
        }
        && match (flat[1], head.action) {
            (FlatHead::Constant(ComponentValue::Action(a)), PatternView::Constant(b)) => a == b,
            (FlatHead::Bind, PatternView::Variable(_)) => true,
            _ => false,
        }
        && match (flat[2], head.resource) {
            (FlatHead::Constant(ComponentValue::Resource(a)), PatternView::Constant(b)) => a == b,
            (FlatHead::Bind, PatternView::Variable(_)) => true,
            _ => false,
        }
}

pub open spec fn scope_matches<E: Event>(scope: VariableScope<'_>, head: SourceHead<E>) -> bool {
    (match scope.name_spec(Component::Principal) {
        Some(name) => dsl::pattern_name(head.principal) == Some(name@),
        None => dsl::pattern_name(head.principal) is None,
    }) && (match scope.name_spec(Component::Action) {
        Some(name) => dsl::pattern_name(head.action) == Some(name@),
        None => dsl::pattern_name(head.action) is None,
    }) && (match scope.name_spec(Component::Resource) {
        Some(name) => dsl::pattern_name(head.resource) == Some(name@),
        None => dsl::pattern_name(head.resource) is None,
    })
}

pub open spec fn atom_term_represents<E: Event>(field: Component, term: FlatTerm<ComponentValue<E>>,
    atom: AtomView<E::Principal, E::Action, E::Resource>, head: SourceHead<E>) -> bool
{
    match (field, term, atom) {
        (Component::Principal, FlatTerm::Constant(ComponentValue::Principal(a)), AtomView::Principal(PatternView::Constant(b))) => a == b,
        (Component::Action, FlatTerm::Constant(ComponentValue::Action(a)), AtomView::Action(PatternView::Constant(b))) => a == b,
        (Component::Resource, FlatTerm::Constant(ComponentValue::Resource(a)), AtomView::Resource(PatternView::Constant(b))) => a == b,
        (Component::Principal, FlatTerm::Variable(Component::Principal), AtomView::Principal(PatternView::Variable(name))) => dsl::pattern_name(head.principal) == Some(name),
        (Component::Action, FlatTerm::Variable(Component::Action), AtomView::Action(PatternView::Variable(name))) => dsl::pattern_name(head.action) == Some(name),
        (Component::Resource, FlatTerm::Variable(Component::Resource), AtomView::Resource(PatternView::Variable(name))) => dsl::pattern_name(head.resource) == Some(name),
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
pub open spec fn test_represents<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, id: nat,
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

pub open spec fn regex_represents<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, regexes: Seq<FlatRegex>, id: nat,
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

pub open spec fn flattened<E: Event>(rule: Rule<E>, flat_rule: FlatRule<ComponentValue<E>>) -> bool {
    flat_rule.mode == rule.mode && flat::structural_wf(flat_rule.source)
        && dsl::head_scoped(rule.head@) && head_represents::<E>(flat_rule.source.head@, rule.head@)
        && regex_represents::<E>(flat_rule.source.tests@, flat_rule.source.regexes@,
            flat_rule.source.root as nat, rule.tail@, rule.head@)
}

pub open spec fn test_views<E: Event>(children: Seq<TestExpr<E>>) -> Seq<SourceTest<E>> {
    children.map(|i: int, child: TestExpr<E>| child@)
}
pub open spec fn regex_views<E: Event>(children: Seq<RegexExpr<E>>) -> Seq<SourceRegex<E>> {
    children.map(|i: int, child: RegexExpr<E>| child@)
}

pub open spec fn result_stacks<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, regexes: Seq<FlatRegex>,
    test_ids: Seq<u32>, regex_ids: Seq<u32>, test_sources: Seq<SourceTest<E>>, regex_sources: Seq<SourceRegex<E>>,
    head: SourceHead<E>) -> bool
{
    test_ids.len() == test_sources.len() && regex_ids.len() == regex_sources.len()
        && (forall|i: int| 0 <= i < test_ids.len() ==>
            #[trigger] test_represents::<E>(tests, test_ids[i] as nat, test_sources[i], head))
        && (forall|i: int| 0 <= i < regex_ids.len() ==>
            #[trigger] regex_represents::<E>(tests, regexes, regex_ids[i] as nat, regex_sources[i], head))
}

/// Erased continuation interpreter: visits contribute original views; finish frames check order.
/// It neither evaluates policies nor reconstructs any executable source tree.
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

pub(crate) proof fn lemma_finish_test<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a TestExpr<E>, start: usize,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, children: Seq<SourceTest<E>>)
    requires start == tests.len(), source@ == TestView::And(children) || source@ == TestView::Or(children),
    ensures run_work::<E>(work.push(Work::FinishTest(source, start)), tests + children, regexes)
        == run_work::<E>(work, tests.push(source@), regexes),
{
    let operands = tests + children;
    assert(operands.subrange(start as int, operands.len() as int) =~= children);
    assert(operands.take(start as int) =~= tests);
    assert(work.push(Work::FinishTest(source, start)).drop_last() =~= work);
    reveal_with_fuel(run_work, 2);
}

pub(crate) proof fn lemma_visit_test_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, child: &'a TestExpr<E>,
    start: usize, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>)
    requires start == tests.len(), source@ == RegexView::Test(child@),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Test(child)), tests, regexes)
        == run_work::<E>(work, tests, regexes.push(source@)),
{
    let finish = work.push(Work::FinishRegex(source, start));
    let program = finish.push(Work::Test(child));
    assert(program.drop_last() =~= finish);
    assert(finish.drop_last() =~= work);
    assert(tests.push(child@).take(start as int) =~= tests);
    reveal_with_fuel(run_work, 3);
}

pub(crate) proof fn lemma_visit_unary_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, child: &'a RegexExpr<E>,
    start: usize, tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>)
    requires start == regexes.len(), source@ == RegexView::Star(alloc::boxed::Box::new(child@))
        || source@ == RegexView::Not(alloc::boxed::Box::new(child@)),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)).push(Work::Regex(child)), tests, regexes)
        == run_work::<E>(work, tests, regexes.push(source@)),
{
    let finish = work.push(Work::FinishRegex(source, start));
    let program = finish.push(Work::Regex(child));
    assert(program.drop_last() =~= finish);
    assert(finish.drop_last() =~= work);
    assert(regexes.push(child@).take(start as int) =~= regexes);
    reveal_with_fuel(run_work, 3);
}

pub(crate) proof fn lemma_finish_many_regex<'a, E: Event>(work: Seq<Work<'a, E>>, source: &'a RegexExpr<E>, start: usize,
    tests: Seq<SourceTest<E>>, regexes: Seq<SourceRegex<E>>, children: Seq<SourceRegex<E>>)
    requires start == regexes.len(), source@ == RegexView::Concat(children)
        || source@ == RegexView::Union(children) || source@ == RegexView::Intersect(children),
    ensures run_work::<E>(work.push(Work::FinishRegex(source, start)), tests, regexes + children)
        == run_work::<E>(work, tests, regexes.push(source@)),
{
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

pub proof fn lemma_test_extension<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, more: Seq<FlatTest<ComponentValue<E>>>,
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

pub proof fn lemma_regex_extension<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, more_tests: Seq<FlatTest<ComponentValue<E>>>,
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

pub proof fn lemma_stack_extension<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, more_tests: Seq<FlatTest<ComponentValue<E>>>,
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

pub proof fn lemma_head_semantics<E: Event>(head: Seq<FlatHead<ComponentValue<E>>>, source: SourceHead<E>, candidate: SourceEvent<E>)
    requires head_represents::<E>(head, source),
    ensures flat::head_matches(head, event_values::<E>(candidate), component_equality::<E>())
        == dsl::head_matches(source, candidate),
{
    if dsl::head_matches(source, candidate) {
        assert forall|field: Component| match #[trigger] head[flat::field_index(field)] {
            FlatHead::Constant(expected) => component_eq::<E>(field, event_values::<E>(candidate)[flat::field_index(field)], expected),
            _ => true,
        } by { match field { Component::Principal => {}, Component::Action => {}, Component::Resource => {} } }
    }
    if flat::head_matches(head, event_values::<E>(candidate), component_equality::<E>()) {
        assert(match head[flat::field_index(Component::Principal)] {
            FlatHead::Constant(expected) => component_equality::<E>()(Component::Principal,
                event_values::<E>(candidate)[flat::field_index(Component::Principal)], expected), _ => true,
        });
        assert(match head[flat::field_index(Component::Action)] {
            FlatHead::Constant(expected) => component_equality::<E>()(Component::Action,
                event_values::<E>(candidate)[flat::field_index(Component::Action)], expected), _ => true,
        });
        assert(match head[flat::field_index(Component::Resource)] {
            FlatHead::Constant(expected) => component_equality::<E>()(Component::Resource,
                event_values::<E>(candidate)[flat::field_index(Component::Resource)], expected), _ => true,
        });
        assert(dsl::head_pattern_matches(source.principal, candidate.principal));
        assert(dsl::head_pattern_matches(source.action, candidate.action));
        assert(dsl::head_pattern_matches(source.resource, candidate.resource));
    }
}

pub proof fn lemma_test_semantics<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, id: nat, source: SourceTest<E>,
    head: SourceHead<E>, candidate: SourceEvent<E>, event: SourceEvent<E>)
    requires test_represents::<E>(tests, id, source, head),
    ensures flat::test_sem(tests, id, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>())
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
                    match pattern {
                        AtomView::Principal(pattern) => { match pattern {
                            PatternView::Constant(_) => {}, PatternView::Variable(_) => { match head.principal { PatternView::Constant(_) => {}, PatternView::Variable(_) => {} } },
                        } },
                        AtomView::Action(pattern) => { match pattern {
                            PatternView::Constant(_) => {}, PatternView::Variable(_) => { match head.action { PatternView::Constant(_) => {}, PatternView::Variable(_) => {} } },
                        } },
                        AtomView::Resource(pattern) => { match pattern {
                            PatternView::Constant(_) => {}, PatternView::Variable(_) => { match head.resource { PatternView::Constant(_) => {}, PatternView::Variable(_) => {} } },
                        } },
                    }
                },
                _ => {},
            }
            assert(flat::test_sem(tests, id, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>())
                == dsl::test_sem(source, head, candidate, event));
        },
        TestView::And(children) => {
            let ids = test_operands(tests[id as int]);
            if dsl::test_sem(source, head, candidate, event) {
                assert forall|i: int| 0 <= i < ids.len() implies
                    flat::test_sem(tests, ids[i] as nat, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>()) by {
                    assert(dsl::test_sem(children[i], head, candidate, event));
                    lemma_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                }
                assert(flat::test_sem(tests, id, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>()));
            }
            if flat::test_sem(tests, id, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>()) {
                assert forall|i: int| 0 <= i < children.len() implies dsl::test_sem(children[i], head, candidate, event) by {
                    assert(flat::test_sem(tests, ids[i] as nat, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>()));
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
                assert(flat::test_sem(tests, ids[i] as nat, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>()));
                assert(flat::test_sem(tests, id, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>()));
            }
            if flat::test_sem(tests, id, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>()) {
                let i = choose|i: int| 0 <= i < ids.len()
                    && flat::test_sem(tests, ids[i] as nat, event_values::<E>(candidate), event_values::<E>(event), component_equality::<E>());
                lemma_test_semantics::<E>(tests, ids[i] as nat, children[i], head, candidate, event);
                assert(dsl::test_sem(children[i], head, candidate, event));
                assert(dsl::test_sem(source, head, candidate, event));
            }
        },
        _ => {},
    }
}

/// Decoding is used only for partition witnesses in the language proof, never at runtime.
pub open spec fn event_from_values<E: Event>(event: Seq<ComponentValue<E>>) -> SourceEvent<E> {
    EventView {
        principal: match event[0] { ComponentValue::Principal(v) => v, _ => arbitrary() },
        action: match event[1] { ComponentValue::Action(v) => v, _ => arbitrary() },
        resource: match event[2] { ComponentValue::Resource(v) => v, _ => arbitrary() },
    }
}
pub open spec fn word_from_values<E: Event>(word: Seq<Seq<ComponentValue<E>>>) -> Seq<SourceEvent<E>> {
    word.map(|i: int, event: Seq<ComponentValue<E>>| event_from_values::<E>(event))
}
pub open spec fn word_typed<E: Event>(word: Seq<Seq<ComponentValue<E>>>) -> bool {
    forall|i: int| 0 <= i < word.len() ==> word[i].len() == 3
        && word[i][0] is Principal && word[i][1] is Action && word[i][2] is Resource
}

pub proof fn lemma_word_roundtrip<E: Event>(word: Seq<SourceEvent<E>>)
    ensures word_typed::<E>(word_values::<E>(word)), word_from_values::<E>(word_values::<E>(word)) == word,
{
    assert(word_from_values::<E>(word_values::<E>(word)) =~= word);
}

pub proof fn lemma_typed_word_roundtrip<E: Event>(word: Seq<Seq<ComponentValue<E>>>)
    requires word_typed::<E>(word),
    ensures word_values::<E>(word_from_values::<E>(word)) == word,
{
    assert forall|i: int| 0 <= i < word.len() implies
        event_values::<E>(event_from_values::<E>(word[i])) == word[i] by {
        assert(event_values::<E>(event_from_values::<E>(word[i])) =~= word[i]);
    }
    assert(word_values::<E>(word_from_values::<E>(word)) =~= word);
}

pub proof fn lemma_word_values_flatten<E: Event>(parts: Seq<Seq<SourceEvent<E>>>)
    ensures word_values::<E>(parts.flatten()) == parts.map(|i: int, part: Seq<SourceEvent<E>>| word_values::<E>(part)).flatten(),
    decreases parts.len(),
{
    if parts.len() > 0 {
        lemma_word_values_flatten::<E>(parts.drop_last());
        assert(parts == parts.drop_last().push(parts.last()));
        parts.drop_last().lemma_flatten_push(parts.last());
        let mapped = parts.map(|i: int, part: Seq<SourceEvent<E>>| word_values::<E>(part));
        let prefix = parts.drop_last().map(|i: int, part: Seq<SourceEvent<E>>| word_values::<E>(part));
        assert(mapped =~= prefix.push(word_values::<E>(parts.last())));
        prefix.lemma_flatten_push(word_values::<E>(parts.last()));
        assert(word_values::<E>(parts.drop_last().flatten() + parts.last())
            =~= word_values::<E>(parts.drop_last().flatten()) + word_values::<E>(parts.last()));
    }
}

pub proof fn lemma_word_from_values_flatten<E: Event>(parts: Seq<Seq<Seq<ComponentValue<E>>>>)
    ensures word_from_values::<E>(parts.flatten()) == parts.map(|i: int, part: Seq<Seq<ComponentValue<E>>>| word_from_values::<E>(part)).flatten(),
    decreases parts.len(),
{
    if parts.len() > 0 {
        lemma_word_from_values_flatten::<E>(parts.drop_last());
        assert(parts == parts.drop_last().push(parts.last()));
        parts.drop_last().lemma_flatten_push(parts.last());
        let mapped = parts.map(|i: int, part: Seq<Seq<ComponentValue<E>>>| word_from_values::<E>(part));
        let prefix = parts.drop_last().map(|i: int, part: Seq<Seq<ComponentValue<E>>>| word_from_values::<E>(part));
        assert(mapped =~= prefix.push(word_from_values::<E>(parts.last())));
        prefix.lemma_flatten_push(word_from_values::<E>(parts.last()));
        assert(word_from_values::<E>(parts.drop_last().flatten() + parts.last())
            =~= word_from_values::<E>(parts.drop_last().flatten()) + word_from_values::<E>(parts.last()));
    }
}

pub proof fn lemma_partition_typed<E: Event>(parts: Seq<Seq<Seq<ComponentValue<E>>>>)
    requires word_typed::<E>(parts.flatten()),
    ensures forall|i: int| 0 <= i < parts.len() ==> word_typed::<E>(parts[i]),
    decreases parts.len(),
{
    if parts.len() > 0 {
        assert(parts =~= parts.drop_last().push(parts.last()));
        parts.drop_last().lemma_flatten_push(parts.last());
        assert(parts.flatten() == parts.drop_last().flatten() + parts.last());
        let left = parts.drop_last().flatten();
        let right = parts.last();
        assert forall|i: int| 0 <= i < left.len() implies left[i].len() == 3
            && left[i][0] is Principal && left[i][1] is Action && left[i][2] is Resource by {
            assert(parts.flatten()[i] == left[i]);
            assert(parts.flatten()[i].len() == 3);
        }
        assert forall|i: int| 0 <= i < right.len() implies right[i].len() == 3
            && right[i][0] is Principal && right[i][1] is Action && right[i][2] is Resource by {
            assert(parts.flatten()[left.len() as int + i] == right[i]);
            assert(parts.flatten()[left.len() as int + i].len() == 3);
        }
        assert(word_typed::<E>(parts.drop_last().flatten()));
        assert(word_typed::<E>(parts.last()));
        lemma_partition_typed::<E>(parts.drop_last());
        assert forall|i: int| 0 <= i < parts.len() implies word_typed::<E>(parts[i]) by {
            if i < parts.len() - 1 { assert(parts[i] == parts.drop_last()[i]); }
            else { assert(parts[i] == parts.last()); }
        }
    }
}

pub proof fn lemma_regex_semantics<E: Event>(tests: Seq<FlatTest<ComponentValue<E>>>, regexes: Seq<FlatRegex>, id: nat,
    source: SourceRegex<E>, head: SourceHead<E>, candidate: SourceEvent<E>, word: Seq<SourceEvent<E>>)
    requires regex_represents::<E>(tests, regexes, id, source, head),
    ensures flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>())
        == dsl::lang(source, head, candidate, word),
    decreases source,
{
    reveal_with_fuel(flat::lang, 2);
    reveal_with_fuel(dsl::lang, 2);
    lemma_regex_operands(regexes[id as int]);
    reveal_with_fuel(regex_represents, 2);
    lemma_word_roundtrip::<E>(word);
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
                assert(flat::lang(tests, regexes, ids[i] as nat, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()));
                assert(flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()));
            }
            if flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()) {
                let i = choose|i: int| 0 <= i < ids.len()
                    && flat::lang(tests, regexes, ids[i] as nat, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>());
                lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, word);
                assert(dsl::lang(children[i], head, candidate, word));
                assert(dsl::lang(source, head, candidate, word));
            }
        },
        RegexView::Intersect(children) => {
            let ids = regex_operands(regexes[id as int]);
            if dsl::lang(source, head, candidate, word) {
                assert forall|i: int| 0 <= i < ids.len() implies
                    flat::lang(tests, regexes, ids[i] as nat, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()) by {
                    assert(dsl::lang(children[i], head, candidate, word));
                    lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, word);
                }
                assert(flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()));
            }
            if flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()) {
                assert forall|i: int| 0 <= i < children.len() implies dsl::lang(children[i], head, candidate, word) by {
                    assert(flat::lang(tests, regexes, ids[i] as nat, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()));
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
                let encoded = parts.map(|i: int, part: Seq<SourceEvent<E>>| word_values::<E>(part));
                lemma_word_values_flatten::<E>(parts);
                assert forall|i: int| 0 <= i < children.len() implies
                    flat::lang(tests, regexes, ids[i] as nat, event_values::<E>(candidate), encoded[i], component_equality::<E>()) by {
                    lemma_regex_semantics::<E>(tests, regexes, ids[i] as nat, children[i], head, candidate, parts[i]);
                }
                assert(flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()));
            }
            if flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()) {
                let encoded = choose|parts: Seq<Seq<Seq<ComponentValue<E>>>>| parts.len() == ids.len()
                    && word_values::<E>(word) == parts.flatten() && forall|i: int| 0 <= i < ids.len() ==>
                        flat::lang(tests, regexes, ids[i] as nat, event_values::<E>(candidate), parts[i], component_equality::<E>());
                let parts = encoded.map(|i: int, part: Seq<Seq<ComponentValue<E>>>| word_from_values::<E>(part));
                lemma_partition_typed::<E>(encoded);
                lemma_word_from_values_flatten::<E>(encoded);
                assert forall|i: int| 0 <= i < children.len() implies dsl::lang(children[i], head, candidate, parts[i]) by {
                    lemma_typed_word_roundtrip::<E>(encoded[i]);
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
                let encoded = parts.map(|i: int, part: Seq<SourceEvent<E>>| word_values::<E>(part));
                lemma_word_values_flatten::<E>(parts);
                assert forall|i: int| 0 <= i < parts.len() implies
                    flat::lang(tests, regexes, child_id as nat, event_values::<E>(candidate), encoded[i], component_equality::<E>()) by {
                    lemma_regex_semantics::<E>(tests, regexes, child_id as nat, *child, head, candidate, parts[i]);
                }
                assert(flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()));
            }
            if flat::lang(tests, regexes, id, event_values::<E>(candidate), word_values::<E>(word), component_equality::<E>()) {
                let encoded = choose|parts: Seq<Seq<Seq<ComponentValue<E>>>>| word_values::<E>(word) == parts.flatten()
                    && forall|i: int| 0 <= i < parts.len() ==>
                        flat::lang(tests, regexes, child_id as nat, event_values::<E>(candidate), parts[i], component_equality::<E>());
                let parts = encoded.map(|i: int, part: Seq<Seq<ComponentValue<E>>>| word_from_values::<E>(part));
                lemma_partition_typed::<E>(encoded);
                lemma_word_from_values_flatten::<E>(encoded);
                assert forall|i: int| 0 <= i < parts.len() implies dsl::lang(*child, head, candidate, parts[i]) by {
                    lemma_typed_word_roundtrip::<E>(encoded[i]);
                    lemma_regex_semantics::<E>(tests, regexes, child_id as nat, *child, head, candidate, parts[i]);
                }
                assert(dsl::lang(source, head, candidate, word));
            }
        },
        _ => {},
    }
}

/// The structural result of the executable compiler implies both independent semantic equations.
pub proof fn flattening_preserves_semantics<E: Event>(rule: Rule<E>, lowered: FlatRule<ComponentValue<E>>,
    candidate: SourceEvent<E>, history: Seq<SourceEvent<E>>)
    requires flattened::<E>(rule, lowered),
    ensures
        flat::head_matches(lowered.source.head@, event_values::<E>(candidate), component_equality::<E>())
            == dsl::head_matches(rule.head@, candidate),
        flat::lang(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
            event_values::<E>(candidate), word_values::<E>(history), component_equality::<E>())
            == dsl::lang(rule.tail@, rule.head@, candidate, history),
{
    lemma_head_semantics::<E>(lowered.source.head@, rule.head@, candidate);
    lemma_regex_semantics::<E>(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
        rule.tail@, rule.head@, candidate, history);
}

/// A client of the executable body obtains the semantic bridge without a correctness precondition.
pub fn flattening_client<E: Event, L: Limits>(rule: &Rule<E>, limits: &mut L, world: &mut ObservationWorld,
    Ghost(candidate): Ghost<SourceEvent<E>>, Ghost(history): Ghost<Seq<SourceEvent<E>>>)
    -> (result: Result<FlatRule<ComponentValue<E>>, CompileError>)
    ensures result matches Ok(lowered) ==>
        dsl::head_scoped(rule.head@) && dsl::regex_scoped(rule.tail@, rule.head@)
        && flat::head_matches(lowered.source.head@, event_values::<E>(candidate), component_equality::<E>())
            == dsl::head_matches(rule.head@, candidate)
        && flat::lang(lowered.source.tests@, lowered.source.regexes@, lowered.source.root as nat,
            event_values::<E>(candidate), word_values::<E>(history), component_equality::<E>())
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

/// A named-variable proof client calls the real lowering body; no semantic premise is supplied.
pub fn named_variable_client<E: Event, L: Limits>(name: alloc::string::String, action: E::Action,
    resource: E::Resource, limits: &mut L, world: &mut ObservationWorld)
    -> (result: Result<FlatRule<ComponentValue<E>>, CompileError>)
    ensures result matches Ok(lowered) ==>
        lowered.source.head@[0] is Bind && lowered.mode == RuleMode::Require
        && match lowered.source.regexes@[lowered.source.root as int] {
            FlatRegex::Test(id) => lowered.source.tests@[id as int] == (FlatTest::Atom { field: Component::Principal,
                term: FlatTerm::Variable(Component::Principal), positive: true }),
            _ => false,
        },
{
    let source = Rule::new(RuleMode::Require,
        Head::new(ComponentPattern::Variable(name.clone()), ComponentPattern::Constant(action), ComponentPattern::Constant(resource)),
        RegexExpr::test(TestExpr::atom(history_syntax::syntax::Comparison::Eq,
            history_syntax::syntax::AtomPattern::Principal(ComponentPattern::Variable(name)))));
    let result = crate::flatten::flatten_rule(&source, limits, world);
    proof {
        reveal_with_fuel(history_syntax::verify::dsl::regex_view, 2);
        reveal_with_fuel(history_syntax::verify::dsl::test_view, 2);
        reveal_with_fuel(regex_represents, 2);
        reveal_with_fuel(test_represents, 2);
    }
    source.dispose();
    result
}
}
