#![cfg(feature = "runtime")]

use std::sync::Arc;

use history_semantics::CompiledRule;
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode, TestExpr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Action {
    Read,
    Edit,
    Release,
    Remove,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Record {
    principal: u32,
    action: Action,
    resource: u32,
}

impl Event for Record {
    type Principal = u32;
    type Action = Action;
    type Resource = u32;

    fn principal(self) -> u32 {
        self.principal
    }
    fn action(self) -> Action {
        self.action
    }
    fn resource(self) -> u32 {
        self.resource
    }
}

fn event(principal: u32, action: Action, resource: u32) -> Record {
    Record {
        principal,
        action,
        resource,
    }
}

fn rule(tail: RegexExpr<Record>) -> Rule<Record> {
    Rule::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("actor"),
            ComponentPattern::variable("action"),
            ComponentPattern::variable("resource"),
        ),
        tail,
    )
}

fn action_test(comparison: Comparison, value: Action) -> TestExpr<Record> {
    TestExpr::atom(
        comparison,
        AtomPattern::Action(ComponentPattern::constant(value)),
    )
}

fn action(value: Action) -> RegexExpr<Record> {
    RegexExpr::test(action_test(Comparison::Eq, value))
}

fn principal(comparison: Comparison, value: u32) -> TestExpr<Record> {
    TestExpr::atom(
        comparison,
        AtomPattern::Principal(ComponentPattern::constant(value)),
    )
}

fn resource(value: u32) -> TestExpr<Record> {
    TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Resource(ComponentPattern::constant(value)),
    )
}

// Compare languages, not the removed arena's canonical handles or minterm layout.
fn equivalent(left: RegexExpr<Record>, right: RegexExpr<Record>) {
    let store = Arc::new(Store::new().unwrap());
    let mut left = CompiledRule::new(store.clone(), rule(left)).unwrap();
    let mut right = CompiledRule::new(store.clone(), rule(right)).unwrap();
    let alphabet = [
        event(100, Action::Read, 0),
        event(101, Action::Edit, 1),
        event(100, Action::Release, 1),
        event(101, Action::Remove, 0),
    ];
    let candidate = event(102, Action::Release, 3);
    for length in 0..=3 {
        for mut word in 0..alphabet.len().pow(length) {
            let events = (0..length).map(|_| {
                let event = alphabet[word % alphabet.len()];
                word /= alphabet.len();
                event
            });
            let history = History::from_events(store.clone(), events).unwrap();
            let expected = right.accepts_history(&history, &candidate).unwrap();
            assert_eq!(
                left.accepts_history(&history, &candidate).unwrap(),
                expected,
                "{history:?}"
            );
            assert_eq!(
                left.accepts_history(&history, &candidate).unwrap(),
                expected,
                "warm {history:?}"
            );
        }
    }
}

#[test]
fn associative_commutative_idempotent_and_identity_languages_are_preserved() {
    equivalent(
        RegexExpr::union([
            action(Action::Read),
            RegexExpr::empty(),
            action(Action::Edit),
            action(Action::Read),
        ]),
        RegexExpr::union([action(Action::Edit), action(Action::Read)]),
    );
    equivalent(
        RegexExpr::concat([
            RegexExpr::epsilon(),
            action(Action::Read),
            RegexExpr::epsilon(),
        ]),
        action(Action::Read),
    );
    let edit = action(Action::Edit);
    equivalent(
        RegexExpr::intersect([edit.clone(), RegexExpr::complement(edit)]),
        RegexExpr::empty(),
    );
}

#[test]
fn boolean_absorption_and_distinct_component_equalities_keep_their_languages() {
    let read = action_test(Comparison::Eq, Action::Read);
    let edit = action_test(Comparison::Eq, Action::Edit);
    let not_read = action_test(Comparison::Neq, Action::Read);
    let not_edit = action_test(Comparison::Neq, Action::Edit);
    equivalent(
        RegexExpr::test(TestExpr::and([
            read.clone(),
            TestExpr::or([read.clone(), edit.clone()]),
        ])),
        action(Action::Read),
    );
    equivalent(
        RegexExpr::test(TestExpr::and([read.clone(), edit])),
        RegexExpr::empty(),
    );
    equivalent(
        RegexExpr::test(TestExpr::and([read.clone(), not_edit.clone()])),
        action(Action::Read),
    );
    equivalent(
        RegexExpr::test(TestExpr::or([read, not_edit.clone()])),
        RegexExpr::test(not_edit.clone()),
    );
    for tests in [
        vec![not_read.clone(), not_edit.clone()],
        vec![not_edit, not_read],
        vec![
            principal(Comparison::Neq, 100),
            principal(Comparison::Neq, 101),
        ],
        vec![
            TestExpr::atom(
                Comparison::Neq,
                AtomPattern::Resource(ComponentPattern::constant(0u32)),
            ),
            TestExpr::atom(
                Comparison::Neq,
                AtomPattern::Resource(ComponentPattern::constant(1u32)),
            ),
        ],
    ] {
        equivalent(
            RegexExpr::test(TestExpr::or(tests)),
            RegexExpr::test(TestExpr::true_test()),
        );
    }
    equivalent(
        RegexExpr::star(RegexExpr::test(TestExpr::true_test())),
        RegexExpr::all(),
    );
}

#[test]
fn compound_boolean_rewrites_are_construction_order_independent() {
    let p = principal(Comparison::Eq, 100);
    let a = action_test(Comparison::Eq, Action::Read);
    let r = resource(0);
    let compound = TestExpr::and([p.clone(), a.clone()]);
    let complement = TestExpr::or([
        principal(Comparison::Neq, 100),
        action_test(Comparison::Neq, Action::Read),
    ]);
    equivalent(
        RegexExpr::test(TestExpr::and([compound.clone(), complement.clone()])),
        RegexExpr::empty(),
    );
    equivalent(
        RegexExpr::test(TestExpr::or([compound.clone(), complement])),
        RegexExpr::test(TestExpr::true_test()),
    );
    let larger = TestExpr::and([p.clone(), a.clone(), r.clone()]);
    for tests in [
        vec![compound.clone(), larger.clone()],
        vec![larger, compound.clone()],
    ] {
        equivalent(
            RegexExpr::test(TestExpr::or(tests)),
            RegexExpr::test(compound.clone()),
        );
    }
    let smaller = TestExpr::or([p.clone(), a.clone()]);
    let larger = TestExpr::or([p, a, r]);
    for tests in [
        vec![smaller.clone(), larger.clone()],
        vec![larger, smaller.clone()],
    ] {
        equivalent(
            RegexExpr::test(TestExpr::and(tests)),
            RegexExpr::test(smaller.clone()),
        );
    }
}

#[test]
fn epsilon_set_languages_preserve_nullability() {
    let nullable = RegexExpr::star(action(Action::Read));
    equivalent(
        RegexExpr::union([RegexExpr::epsilon(), nullable.clone()]),
        nullable.clone(),
    );
    equivalent(
        RegexExpr::intersect([RegexExpr::epsilon(), nullable]),
        RegexExpr::epsilon(),
    );
    let nonnullable = action(Action::Edit);
    equivalent(
        RegexExpr::intersect([RegexExpr::epsilon(), nonnullable.clone()]),
        RegexExpr::empty(),
    );
    equivalent(
        RegexExpr::intersect([
            nonnullable.clone(),
            RegexExpr::complement(RegexExpr::epsilon()),
        ]),
        nonnullable,
    );
}

#[test]
fn mixed_regex_operands_and_absorption_keep_their_languages() {
    let other = RegexExpr::star(action(Action::Release));
    let grouped = RegexExpr::union([
        RegexExpr::test(TestExpr::or([
            action_test(Comparison::Eq, Action::Read),
            action_test(Comparison::Eq, Action::Edit),
        ])),
        other.clone(),
    ]);
    for source in [
        RegexExpr::union([action(Action::Read), other.clone(), action(Action::Edit)]),
        RegexExpr::union([other.clone(), action(Action::Edit), action(Action::Read)]),
        RegexExpr::union([
            action(Action::Read),
            RegexExpr::union([action(Action::Edit), other.clone()]),
        ]),
    ] {
        equivalent(source, grouped.clone());
    }
    equivalent(
        RegexExpr::intersect([action(Action::Read), other.clone(), action(Action::Edit)]),
        RegexExpr::empty(),
    );
    let read = action(Action::Read);
    equivalent(
        RegexExpr::union([
            read.clone(),
            RegexExpr::intersect([read.clone(), other.clone()]),
        ]),
        read.clone(),
    );
    equivalent(
        RegexExpr::intersect([read.clone(), RegexExpr::union([read.clone(), other])]),
        read,
    );
}

#[test]
fn every_regex_form_has_the_expected_complete_word_language() {
    let store = Arc::new(Store::new().unwrap());
    let read = action(Action::Read);
    let edit = action(Action::Edit);
    let sources = [
        RegexExpr::empty(),
        RegexExpr::all(),
        RegexExpr::epsilon(),
        read.clone(),
        RegexExpr::union([read.clone(), RegexExpr::star(edit.clone())]),
        RegexExpr::intersect([
            RegexExpr::star(read.clone()),
            RegexExpr::complement(RegexExpr::epsilon()),
        ]),
        RegexExpr::concat([
            RegexExpr::star(read.clone()),
            edit.clone(),
            RegexExpr::all(),
        ]),
        RegexExpr::star(RegexExpr::union([read.clone(), edit.clone()])),
        RegexExpr::complement(RegexExpr::concat([read, edit])),
    ];
    let mut compiled: Vec<_> = sources
        .into_iter()
        .map(|source| CompiledRule::new(store.clone(), rule(source)).unwrap())
        .collect();
    for word in [
        vec![],
        vec![Action::Read],
        vec![Action::Edit],
        vec![Action::Release],
        vec![Action::Read, Action::Edit],
        vec![Action::Read, Action::Read],
        vec![Action::Edit, Action::Release],
        vec![Action::Read, Action::Edit, Action::Release],
    ] {
        let history =
            History::from_events(store.clone(), word.iter().map(|&a| event(100, a, 0))).unwrap();
        let read_edit_prefix = word
            .iter()
            .position(|&a| a != Action::Read)
            .is_some_and(|index| word[index] == Action::Edit);
        let expected = [
            false,
            true,
            word.is_empty(),
            word == [Action::Read],
            word == [Action::Read] || word.iter().all(|&a| a == Action::Edit),
            !word.is_empty() && word.iter().all(|&a| a == Action::Read),
            read_edit_prefix,
            word.iter()
                .all(|&a| matches!(a, Action::Read | Action::Edit)),
            word != [Action::Read, Action::Edit],
        ];
        for (compiled, expected) in compiled.iter_mut().zip(expected) {
            for _ in 0..2 {
                assert_eq!(
                    compiled
                        .accepts_history(&history, &event(100, Action::Read, 0))
                        .unwrap(),
                    Some(expected),
                    "{word:?}"
                );
            }
        }
    }
}

#[test]
fn candidate_bindings_and_wide_constant_alphabets_remain_exact() {
    let store = Arc::new(Store::new().unwrap());
    let mut bound_action = CompiledRule::new(
        store.clone(),
        rule(RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Action(ComponentPattern::variable("action")),
        ))),
    )
    .unwrap();
    for probe in [event(100, Action::Read, 0), event(101, Action::Edit, 1)] {
        let history = History::from_events(store.clone(), [probe]).unwrap();
        assert_eq!(
            bound_action.accepts_history(&history, &probe).unwrap(),
            Some(true)
        );
        let different = event(probe.principal, Action::Remove, probe.resource);
        assert_eq!(
            bound_action.accepts_history(&history, &different).unwrap(),
            Some(false)
        );
    }
    let alternatives = (0..=64).map(|value| RegexExpr::test(principal(Comparison::Eq, value)));
    let mut wide = CompiledRule::new(store.clone(), rule(RegexExpr::union(alternatives))).unwrap();
    for (actor, expected) in [(7, true), (104, false)] {
        let history = History::from_events(store.clone(), [event(actor, Action::Read, 2)]).unwrap();
        assert_eq!(
            wide.accepts_history(&history, &event(102, Action::Edit, 3))
                .unwrap(),
            Some(expected)
        );
    }
}

#[test]
fn appended_suffixes_replacements_and_forks_keep_exact_residual_answers() {
    let store = Arc::new(Store::new().unwrap());
    let tail = RegexExpr::concat([action(Action::Read), RegexExpr::all(), action(Action::Edit)]);
    let mut compiled = CompiledRule::new(store.clone(), rule(tail)).unwrap();
    let candidate = event(100, Action::Release, 0);
    let mut history = History::new(store).unwrap();
    for (appended, expected) in [
        (None, false),
        (Some(Action::Read), false),
        (Some(Action::Edit), true),
        (Some(Action::Edit), true),
        (Some(Action::Remove), false),
        (Some(Action::Edit), true),
    ] {
        if let Some(action) = appended {
            history.push(event(101, action, 1)).unwrap();
        }
        for _ in 0..2 {
            assert_eq!(
                compiled.accepts_history(&history, &candidate).unwrap(),
                Some(expected)
            );
        }
    }
    history.truncate(1).unwrap();
    history.push(event(100, Action::Remove, 0)).unwrap();
    assert_eq!(
        compiled.accepts_history(&history, &candidate).unwrap(),
        Some(false)
    );
    let checkpoint = history.checkpoint();
    history.push(event(100, Action::Edit, 0)).unwrap();
    assert_eq!(
        compiled.accepts_history(&history, &candidate).unwrap(),
        Some(true)
    );
    history.rollback(checkpoint).unwrap();
    assert_eq!(
        compiled.accepts_history(&history, &candidate).unwrap(),
        Some(false)
    );
    history.truncate(1).unwrap();
    let mut first = history.try_clone().unwrap();
    let mut second = history.try_clone().unwrap();
    first.push(event(100, Action::Edit, 0)).unwrap();
    second.push(event(100, Action::Remove, 0)).unwrap();
    assert_eq!(
        compiled.accepts_history(&first, &candidate).unwrap(),
        Some(true)
    );
    assert_eq!(
        compiled.accepts_history(&second, &candidate).unwrap(),
        Some(false)
    );
    assert_eq!(
        compiled.accepts_history(&first, &candidate).unwrap(),
        Some(true)
    );
}
