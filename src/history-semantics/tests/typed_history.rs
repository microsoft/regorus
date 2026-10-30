#![cfg(feature = "runtime")]

use core::cell::Cell;
use core::hash::{Hash, Hasher};
use history_semantics::CompiledRule;
use history_store::{History, Store};
use history_syntax::{
    AtomPattern, Comparison, ComponentPattern as P, Coprod, Coproduct, Event, Head, RegexExpr as R,
    Rule, RuleMode, TestExpr as T,
};
use junco_core::HistoryError;
use std::sync::Arc;

std::thread_local! {
    static HISTORY_PROJECTIONS: Cell<usize> = const { Cell::new(0) };
}

#[derive(Clone, Copy, Debug)]
struct Part {
    identity: u8,
    payload: u8,
}

impl PartialEq for Part {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for Part {}
impl Hash for Part {
    fn hash<H: Hasher>(&self, state: &mut H) {
        0u8.hash(state);
    }
}

#[derive(Clone, Copy, Debug)]
struct Record {
    principal: Part,
    action: Part,
    resource: Part,
    payload: u16,
}

impl Record {
    fn raw_key(self) -> (u8, u8, u8, u8, u8, u8, u16) {
        (
            self.principal.identity,
            self.principal.payload,
            self.action.identity,
            self.action.payload,
            self.resource.identity,
            self.resource.payload,
            self.payload,
        )
    }

    fn observe_history_projection(self) {
        if self.payload < 1000 {
            HISTORY_PROJECTIONS.with(|count| count.set(count.get() + 1));
        }
    }
}
impl PartialEq for Record {
    fn eq(&self, other: &Self) -> bool {
        self.raw_key() == other.raw_key()
    }
}
impl Eq for Record {}
impl Hash for Record {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.raw_key().hash(state);
    }
}
impl Event for Record {
    type Principal = Part;
    type Action = Part;
    type Resource = Part;
    fn principal(self) -> Part {
        self.observe_history_projection();
        self.principal
    }
    fn action(self) -> Part {
        self.observe_history_projection();
        self.action
    }
    fn resource(self) -> Part {
        self.observe_history_projection();
        self.resource
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Approval(Record);
impl Event for Approval {
    type Principal = Part;
    type Action = Part;
    type Resource = Part;
    fn principal(self) -> Part {
        self.0.principal()
    }
    fn action(self) -> Part {
        self.0.action()
    }
    fn resource(self) -> Part {
        self.0.resource()
    }
}

type Mixed = Coprod![Record, Approval];

fn record(actor: u8, action: u8, resource: u8, representation: u8, payload: u16) -> Record {
    Record {
        principal: Part {
            identity: actor,
            payload: representation,
        },
        action: Part {
            identity: action,
            payload: representation,
        },
        resource: Part {
            identity: resource,
            payload: representation,
        },
        payload,
    }
}

fn head<E: Event<Principal = Part, Action = Part, Resource = Part>>() -> Head<E> {
    Head::new(
        P::variable("actor"),
        P::constant(Part {
            identity: 2,
            payload: 99,
        }),
        P::variable("resource"),
    )
}

fn prior_edit<E: Event<Principal = Part, Action = Part, Resource = Part>>() -> Rule<E> {
    Rule::new(
        RuleMode::Require,
        head(),
        R::concat([
            R::all(),
            R::test(T::and([
                T::atom(Comparison::Eq, AtomPattern::Principal(P::variable("actor"))),
                T::atom(
                    Comparison::Eq,
                    AtomPattern::Action(P::constant(Part {
                        identity: 1,
                        payload: 99,
                    })),
                ),
                T::atom(
                    Comparison::Eq,
                    AtomPattern::Resource(P::variable("resource")),
                ),
            ])),
            R::all(),
        ]),
    )
}

fn reads_only() -> Rule<Record> {
    Rule::new(
        RuleMode::Require,
        head(),
        R::star(R::test(T::atom(
            Comparison::Eq,
            AtomPattern::Action(P::constant(Part {
                identity: 0,
                payload: 99,
            })),
        ))),
    )
}

#[test]
fn non_structural_equality_and_hash_collisions_preserve_payloads_and_variants() {
    let store = Arc::new(Store::<Mixed>::new().unwrap());
    let mut rule = CompiledRule::new(store.clone(), prior_edit()).unwrap();
    let first = record(7, 1, 9, 1, 11);
    let second = record(7, 1, 9, 2, 22);
    let events: [Mixed; 2] = [
        Coproduct::Inl(first),
        Coproduct::Inr(Coproduct::Inl(Approval(second))),
    ];
    let history = History::from_events(store, events).unwrap();
    assert_eq!(history.as_slice(), &events);
    assert_ne!(history.as_slice()[0], history.as_slice()[1]);
    assert!(matches!(history.as_slice()[0], Coproduct::Inl(value) if value.principal.payload == 1));
    assert!(
        matches!(history.as_slice()[1], Coproduct::Inr(Coproduct::Inl(value)) if value.0.principal.payload == 2)
    );
    for representation in [1, 2] {
        let candidate = Coproduct::Inl(record(7, 2, 9, representation, 2000));
        assert_eq!(
            rule.accepts_history(&history, &candidate).unwrap(),
            Some(true)
        );
    }
    let unequal_same_hash = Coproduct::Inl(record(8, 2, 9, 2, 2000));
    assert_eq!(
        rule.accepts_history(&history, &unequal_same_hash).unwrap(),
        Some(false)
    );
    let different_resource = Coproduct::Inl(record(7, 2, 10, 2, 2000));
    assert_eq!(
        rule.accepts_history(&history, &different_resource).unwrap(),
        Some(false)
    );
    assert_eq!(history.as_slice(), &events);
}

#[test]
fn a_fork_cannot_inherit_another_owners_terminal_residual() {
    let store = Arc::new(Store::<Record>::new().unwrap());
    let mut rule = CompiledRule::new(store.clone(), reads_only()).unwrap();
    let mut original = History::from_events(store, [record(7, 0, 9, 1, 1); 2]).unwrap();
    let probe = record(7, 2, 9, 2, 2000);
    assert_eq!(rule.accepts_history(&original, &probe).unwrap(), Some(true));
    let mut fork = original.try_clone().unwrap();
    original.push(record(7, 1, 9, 1, 2)).unwrap();
    assert_eq!(
        rule.accepts_history(&original, &probe).unwrap(),
        Some(false)
    );
    fork.push(record(7, 0, 9, 2, 3)).unwrap();
    assert_eq!(original.len(), fork.len());
    assert_eq!(rule.accepts_history(&fork, &probe).unwrap(), Some(true));
    assert_eq!(
        rule.accepts_history(&original, &probe).unwrap(),
        Some(false)
    );
    fork.truncate(1).unwrap();
    assert_eq!(rule.accepts_history(&fork, &probe).unwrap(), Some(true));
}

#[test]
fn checkpoint_errors_are_owner_specific_and_fail_before_mutation() {
    let store = Arc::new(Store::<Record>::new().unwrap());
    let event = record(7, 0, 9, 1, 1);
    let mut history = History::from_events(store.clone(), [event, event]).unwrap();
    let checkpoint = history.checkpoint();
    let mut sibling = History::from_events(store, [event, event]).unwrap();
    assert!(matches!(
        sibling.rollback(checkpoint),
        Err(HistoryError::WrongCheckpointOwner)
    ));
    assert_eq!(sibling.as_slice(), &[event, event]);
    history.truncate(1).unwrap();
    assert!(matches!(
        history.rollback(checkpoint),
        Err(HistoryError::CheckpointBeyondHistory)
    ));
    assert_eq!(history.as_slice(), &[event]);
    history.push(event).unwrap();
    history.rollback(checkpoint).unwrap();
    assert_eq!(history.as_slice(), &[event, event]);
    let another_store = Arc::new(Store::<Record>::new().unwrap());
    let same_raw = History::from_events(another_store, [event, event]).unwrap();
    assert_eq!(history, same_raw);
    assert_eq!(format!("{history:?}"), format!("{same_raw:?}"));
    assert!(matches!(
        sibling.rollback(same_raw.checkpoint()),
        Err(HistoryError::WrongCheckpointOwner)
    ));
}

#[test]
fn foreign_store_fails_before_candidate_projection_or_cache_lookup() {
    let store = Arc::new(Store::<Record>::new().unwrap());
    let mut rule = CompiledRule::new(store, prior_edit()).unwrap();
    let foreign = History::new(Arc::new(Store::<Record>::new().unwrap())).unwrap();
    HISTORY_PROJECTIONS.with(|count| count.set(0));
    let candidate = record(7, 2, 9, 1, 1);
    assert!(matches!(
        rule.accepts_history(&foreign, &candidate),
        Err(HistoryError::WrongHistoryOwner)
    ));
    HISTORY_PROJECTIONS.with(|count| assert_eq!(count.get(), 0));
    assert!(foreign.is_empty());
}

#[test]
fn decisions_and_forks_do_not_reencode_committed_events() {
    let store = Arc::new(Store::<Record>::new().unwrap());
    let mut rule = CompiledRule::new(store.clone(), prior_edit()).unwrap();
    let history = History::from_events(store, [record(7, 1, 9, 1, 1); 4]).unwrap();
    HISTORY_PROJECTIONS.with(|count| count.set(0));
    let candidate = record(7, 2, 9, 2, 2000);
    for _ in 0..3 {
        assert_eq!(
            rule.accepts_history(&history, &candidate).unwrap(),
            Some(true)
        );
    }
    let fork = history.try_clone().unwrap();
    assert_eq!(fork.as_slice(), history.as_slice());
    assert_eq!(rule.accepts_history(&fork, &candidate).unwrap(), Some(true));
    HISTORY_PROJECTIONS.with(|count| assert_eq!(count.get(), 0));
    assert_eq!(history.len(), 4);
}
