// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Concrete source-policy checks, connected below to the real evaluator contract.

use super::history_algebra::{
    sim_lhs, sim_rhs, sim_valid, similar, theorem_similar_tails_same_decision, RegexRule, Sim,
    TestRule, TestSim,
};
use super::history_specs as language;
use super::history_specs::{Head, Regex, SrcTest, Subst, Term};
use super::value_specs::{history_view, value_view, Data};
use crate::builtins::history::{HistoryError, HistoryMatchState, ObservationWorld};
use crate::utils::limits::ExecutionTimer;
use crate::value::Array;
use crate::{Rc, Value};
use alloc::boxed::Box;
use vstd::prelude::*;

verus! {

broadcast use vstd::string::group_string_axioms;

pub open spec fn tag(name: Seq<char>, payload: Data) -> Data {
    Data::Object(Map::empty().insert(Data::String(name), payload))
}

pub open spec fn comparison(name: Seq<char>, path: Seq<Data>, term: Data) -> Data {
    tag(name, Data::Object(Map::empty()
        .insert(Data::String("path"@), Data::Array(path))
        .insert(Data::String("term"@), term)))
}

pub open spec fn variable() -> Data { tag("var"@, Data::String(seq!['x'])) }

pub open spec fn any_test() -> Regex<SrcTest> { Regex::Test(SrcTest::Bool(true)) }

pub open spec fn suffix(value: bool) -> Regex<SrcTest> {
    Regex::Concat(seq![Regex::All,
        Regex::Test(SrcTest::Eq(Seq::empty(), Term::Constant(Data::Bool(value))))])
}

pub open spec fn source_suffix(value: bool) -> Data {
    tag("concat"@, Data::Array(seq![tag("all"@, Data::Bool(true)),
        tag("test"@, comparison("eq"@, Seq::empty(), tag("value"@, Data::Bool(value))))]))
}

pub open spec fn example_head(case: u8) -> Head {
    if case == 0 { Head::Array(seq![Head::Variable(seq!['x']), Head::Variable(seq!['x'])]) }
    else if case == 3 || case == 9 || case == 10 { Head::Variable(seq!['x']) }
    else { Head::Any }
}

pub open spec fn example_tail(case: u8) -> Regex<SrcTest> {
    match case {
        0 | 1 => Regex::Epsilon,
        2 => any_test(),
        3 => Regex::Test(SrcTest::Eq(seq![Data::String(seq!['k'])], Term::Variable(seq!['x']))),
        4 => Regex::Test(SrcTest::Neq(seq![Data::String(seq!['k'])], Term::Constant(Data::Null))),
        5 => Regex::Not(Box::new(any_test())),
        6 => Regex::Concat(seq![Regex::Epsilon, any_test()]),
        7 => Regex::Star(Box::new(any_test())),
        8 => Regex::Intersect(seq![suffix(false), Regex::Not(Box::new(suffix(true)))]),
        _ => Regex::Test(SrcTest::Eq(Seq::empty(), Term::Variable(seq!['x']))),
    }
}

pub open spec fn example_policy(case: u8) -> Data {
    let head = if case == 0 { tag("array"@, Data::Array(seq![variable(), variable()])) }
        else if case == 3 || case == 9 || case == 10 { variable() }
        else { tag("any"@, Data::Bool(true)) };
    let tail = match case {
        0 | 1 => tag("epsilon"@, Data::Bool(true)),
        2 => tag("test"@, Data::Bool(true)),
        3 => tag("test"@, comparison("eq"@, seq![Data::String(seq!['k'])], variable())),
        4 => tag("test"@, comparison("neq"@, seq![Data::String(seq!['k'])], tag("value"@, Data::Null))),
        5 => tag("not"@, tag("test"@, Data::Bool(true))),
        6 => tag("concat"@, Data::Array(seq![tag("epsilon"@, Data::Bool(true)), tag("test"@, Data::Bool(true))])),
        7 => tag("star"@, tag("test"@, Data::Bool(true))),
        8 => tag("intersect"@, Data::Array(seq![source_suffix(false), tag("not"@, source_suffix(true))])),
        _ => tag("test"@, comparison("eq"@, Seq::empty(), variable())),
    };
    Data::Object(Map::empty().insert(Data::String("request"@), head)
        .insert(Data::String("history"@), tail))
}

pub open spec fn example_request(case: u8) -> Data {
    if case == 0 { Data::Array(seq![Data::Bool(true), Data::Bool(false)]) }
    else if case == 3 || case == 9 { Data::Bool(true) }
    else if case == 10 { Data::Bool(false) }
    else { Data::Null }
}

pub open spec fn example_history(case: u8) -> Seq<Data> {
    match case {
        0 | 1 | 2 => Seq::empty(),
        3 => seq![Data::Object(Map::empty().insert(Data::String(seq!['k']), Data::Bool(true)))],
        4 => seq![Data::Object(Map::empty())],
        5 => seq![Data::Null, Data::Null],
        6 => seq![Data::Null],
        7 => seq![Data::Null, Data::Bool(false)],
        8 => seq![Data::Null, Data::Bool(false)],
        _ => seq![Data::Bool(true)],
    }
}

pub open spec fn example_expected(case: u8) -> bool {
    case != 0 && case != 2 && case != 4 && case != 10
}

proof fn lemma_example_decodes(case: u8)
    requires case <= 10,
    ensures language::decodes_policy(example_policy(case), example_head(case), example_tail(case)),
{
    language::lemma_source_literals();
    reveal_with_fuel(language::decodes_head, 3);
    reveal_with_fuel(language::decodes_tail, 5);
    reveal_with_fuel(language::decodes_test, 3);
    match case {
        0 => {}, 1 => {}, 2 => {}, 3 => {}, 4 => {}, 5 => {},
        6 => {}, 7 => {}, 8 => {}, 9 => {}, _ => {},
    }
}

proof fn lemma_suffix_truth(theta: Subst, value: bool)
    ensures language::lang(|test: SrcTest, event: Data| language::src_test_holds(theta, test, event),
        suffix(value), seq![Data::Null, Data::Bool(false)]) == !value,
{
    let sem = |test: SrcTest, event: Data| language::src_test_holds(theta, test, event);
    let last = Regex::Test(SrcTest::Eq(Seq::empty(), Term::Constant(Data::Bool(value))));
    let word = seq![Data::Null, Data::Bool(false)];
    language::lemma_concat_pair(sem, Regex::All, last, word);
    if language::lang(sem, suffix(value), word) {
        let (prefix, rest) = choose|prefix: Seq<Data>, rest: Seq<Data>|
            word == prefix + rest && language::lang(sem, Regex::All, prefix)
                && language::lang(sem, last, rest);
        assert(rest.len() == 1);
        assert(prefix.len() == 1);
        assert(rest[0] == word[1]);
        assert(!value);
    }
    if !value {
        let prefix = seq![Data::Null];
        let rest = seq![Data::Bool(false)];
        assert(word =~= prefix + rest);
        assert(language::lang(sem, Regex::All, prefix) && language::lang(sem, last, rest));
        assert(language::lang(sem, suffix(value), word));
    }
}

proof fn lemma_example(case: u8)
    requires case <= 10,
    ensures
        language::pair_lang(example_head(case), example_tail(case), example_request(case), example_history(case))
            == example_expected(case),
        language::policy_lang(example_policy(case), example_request(case), example_history(case))
            == example_expected(case),
{
    lemma_example_decodes(case);
    let head = example_head(case);
    let tail = example_tail(case);
    let request = example_request(case);
    let history = example_history(case);
    if case == 0 {
        assert forall|theta: Subst| !language::head_match(head, request, theta) by {
            if language::head_match(head, request, theta) {
                assert(language::head_match(Head::Variable(seq!['x']), Data::Bool(true), theta));
                assert(language::head_match(Head::Variable(seq!['x']), Data::Bool(false), theta));
            }
        }
    } else {
        let theta: Subst = if case == 3 || case == 9 || case == 10 {
            Map::empty().insert(seq!['x'], request)
        } else { Map::empty() };
        language::lemma_pair_lang_substitutions(head, tail, request, history, theta);
        let sem = |test: SrcTest, event: Data| language::src_test_holds(theta, test, event);
        match case {
            6 => {
                language::lemma_concat_pair(sem, Regex::Epsilon, any_test(), history);
                assert(history == Seq::<Data>::empty() + history);
                assert(language::lang(sem, tail, history));
            },
            7 => {
                let parts = seq![seq![Data::Null], seq![Data::Bool(false)]];
                assert(parts.drop_first() =~= seq![seq![Data::Bool(false)]]);
                parts.drop_first().lemma_flatten_one_element();
                assert(parts.flatten() =~= history);
                assert forall|i: int| 0 <= i < parts.len()
                    implies language::lang(sem, any_test(), parts[i]) by { }
                assert(language::lang(sem, tail, history));
            },
            8 => {
                lemma_suffix_truth(theta, false);
                lemma_suffix_truth(theta, true);
                let children = seq![suffix(false), Regex::Not(Box::new(suffix(true)))];
                assert forall|i: int| 0 <= i < children.len()
                    implies language::lang(sem, children[i], history) by {
                    if i == 0 { assert(children[i] == suffix(false)); }
                    else {
                        assert(i == 1);
                        assert(children[i] == Regex::Not(Box::new(suffix(true))));
                    }
                }
                assert(language::lang(sem, tail, history));
            },
            _ => {
                reveal_with_fuel(language::lang, 3);
                reveal_with_fuel(language::select, 3);
                assert(language::lang(sem, tail, history) == example_expected(case));
            },
        }
        assert(language::lang(sem, tail, history) == example_expected(case));
    }
    language::lemma_policy_lang_decoded(example_policy(case), head, tail, request, history);
}

pub proof fn repeated_variable_failure()
    ensures !language::policy_lang(example_policy(0), example_request(0), example_history(0)),
{
    lemma_example(0);
    assert(!language::pair_lang(example_head(0), example_tail(0), example_request(0), example_history(0)));
}

pub proof fn epsilon_versus_test_true_on_empty_history()
    ensures language::policy_lang(example_policy(1), Data::Null, Seq::empty()),
        !language::policy_lang(example_policy(2), Data::Null, Seq::empty()),
{
    lemma_example(1); lemma_example(2);
    assert(language::pair_lang(example_head(1), example_tail(1), Data::Null, Seq::empty()));
    assert(!language::pair_lang(example_head(2), example_tail(2), Data::Null, Seq::empty()));
}

pub proof fn scoped_eq()
    ensures language::policy_lang(example_policy(3), example_request(3), example_history(3)),
{
    lemma_example(3);
    assert(language::pair_lang(example_head(3), example_tail(3), example_request(3), example_history(3)));
}

pub proof fn missing_path_neq_is_false()
    ensures !language::policy_lang(example_policy(4), example_request(4), example_history(4)),
{
    lemma_example(4);
    assert(!language::pair_lang(example_head(4), example_tail(4), example_request(4), example_history(4)));
}

pub proof fn two_event_not()
    ensures language::policy_lang(example_policy(5), example_request(5), example_history(5)),
{
    lemma_example(5);
    assert(language::pair_lang(example_head(5), example_tail(5), example_request(5), example_history(5)));
}

pub proof fn nullable_concat()
    ensures language::policy_lang(example_policy(6), example_request(6), example_history(6)),
{
    lemma_example(6);
    assert(language::pair_lang(example_head(6), example_tail(6), example_request(6), example_history(6)));
}

pub proof fn star()
    ensures language::policy_lang(example_policy(7), example_request(7), example_history(7)),
{
    lemma_example(7);
    assert(language::pair_lang(example_head(7), example_tail(7), example_request(7), example_history(7)));
}

pub proof fn intersect_with_not_suffix()
    ensures language::policy_lang(example_policy(8), example_request(8), example_history(8)),
{
    lemma_example(8);
    assert(language::pair_lang(example_head(8), example_tail(8), example_request(8), example_history(8)));
}

pub proof fn one_event_under_two_substitutions()
    ensures example_policy(9) == example_policy(10), example_history(9) == example_history(10),
        language::policy_lang(example_policy(9), Data::Bool(true), example_history(9)),
        !language::policy_lang(example_policy(10), Data::Bool(false), example_history(10)),
{
    lemma_example(9); lemma_example(10);
    assert(language::pair_lang(example_head(9), example_tail(9), Data::Bool(true), example_history(9)));
    assert(!language::pair_lang(example_head(10), example_tail(10), Data::Bool(false), example_history(10)));
}

/// `union[test true, test false]` and `test true` decide identically for every head.
pub proof fn union_of_tests_is_a_test(head: Head, request: Data, history: Seq<Data>)
    ensures language::pair_lang(head, Regex::Union(seq![any_test(), Regex::Test(SrcTest::Bool(false))]), request, history)
        == language::pair_lang(head, any_test(), request, history),
{
    reveal_with_fuel(sim_valid, 3);
    reveal_with_fuel(sim_lhs, 3);
    reveal_with_fuel(sim_rhs, 3);
    reveal_with_fuel(super::history_algebra::test_sim_valid, 2);
    let phis = seq![SrcTest::Bool(true), SrcTest::Bool(false)];
    let d = Sim::Trans(Box::new(Sim::Rule(RegexRule::TestUnion(phis))),
        Box::new(Sim::Test(TestSim::Rule(TestRule::OrTrue(phis, 0)))));
    assert(sim_valid(d));
    assert(sim_lhs(d) is Union);
    assert(sim_lhs(d)->Union_0 =~= seq![any_test(), Regex::Test(SrcTest::Bool(false))]);
    assert(sim_rhs(d) == any_test());
    assert(similar(sim_lhs(d), sim_rhs(d)));
    theorem_similar_tails_same_decision(head, sim_lhs(d), sim_rhs(d), request, history);
}

/// Instantiate the actual top-level theorem for every concrete policy above.
/// This calls the production evaluator; it does not implement another evaluator.
pub fn evaluate_example(
    state: &mut HistoryMatchState, policy: &Value, history: &Rc<Array>, request: &Value,
    timer: &mut ExecutionTimer, world: &mut ObservationWorld, case: Ghost<u8>,
) -> (result: Result<bool, HistoryError>)
    requires old(state).state_wf(), case@ <= 10,
        value_view(*policy) == example_policy(case@),
        value_view(*request) == example_request(case@),
        history_view(*history) == example_history(case@),
    ensures final(state).state_wf(),
        result matches Ok(answer) ==> answer == example_expected(case@),
{
    proof { lemma_example(case@); }
    state.evaluate(policy, history, request, timer, world)
}

}
