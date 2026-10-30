//! A miniature non-lock policy, assembled only from kernel pieces.
//!
//! The lock table is not the contract under test here: this file exists to pin that [`super::atoms`],
//! [`super::language`], [`super::rule`] and [`super::evaluate`] carry no lock assumptions, by
//! building a policy over a different vocabulary and running it through the same loop.

use alloc::{
    boxed::Box,
    format,
    rc::Rc,
    string::{String, ToString},
    sync::Arc,
    vec,
    vec::Vec,
};
use core::{cell::Cell, fmt};

use super::CompiledPolicy;
use super::atoms::{action_is, principal_is, resource_is};
use super::decision::PolicyDecision;
use super::language::last_state_change;
use super::rule::{PolicyRule, forbid};
use history_store::{History, Store};
use history_syntax::{Comparison, Event, TestExpr};

/// Principals of the miniature policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Editor {
    Alice,
    Bob,
}

impl fmt::Display for Editor {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Alice => "alice",
            Self::Bob => "bob",
        })
    }
}

/// The one resource the miniature policy guards.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SrcX;

impl fmt::Display for SrcX {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("src/x")
    }
}

/// Operations of the miniature policy; deliberately distinct from a lock-policy vocabulary.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum DocAction {
    Read,
    Edit,
}

/// One event of the miniature policy.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DocEvent {
    principal: Editor,
    action: DocAction,
    resource: SrcX,
}

impl Event for DocEvent {
    type Principal = Editor;
    type Action = DocAction;
    type Resource = SrcX;

    fn principal(self) -> Editor {
        self.principal
    }

    fn action(self) -> DocAction {
        self.action
    }

    fn resource(self) -> SrcX {
        self.resource
    }
}

/// Context of the miniature policy: the resource and who last edited it.
struct LastEditor {
    resource: String,
    editor: String,
}

/// The whole table: reading a resource whose last state change was a foreign edit is forbidden.
fn rules() -> Vec<PolicyRule<DocEvent, LastEditor>> {
    let setter = TestExpr::and([
        resource_is(Comparison::Eq),
        action_is(DocAction::Edit, Comparison::Eq),
        principal_is(Comparison::Neq),
    ]);
    let stable = TestExpr::or([
        resource_is(Comparison::Neq),
        action_is(DocAction::Read, Comparison::Eq),
    ]);
    vec![forbid(
        DocAction::Read,
        last_state_change(setter, stable),
        Box::new(|context| {
            let LastEditor { resource, editor } = context;
            (
                format!("{resource} was last edited by {editor}"),
                vec![format!("{editor} release {resource}")],
            )
        }),
    )]
}

/// Builds the context for `candidate`: the last principal to edit its resource, or `"nobody"`.
fn context(history: &[DocEvent], candidate: &DocEvent) -> LastEditor {
    let editor = history
        .iter()
        .rfind(|event| event.resource == candidate.resource && event.action == DocAction::Edit)
        .map_or_else(|| "nobody".to_string(), |event| event.principal.to_string());
    LastEditor {
        resource: candidate.resource.to_string(),
        editor,
    }
}

#[test]
fn a_non_lock_policy_reuses_the_kernel_loop() {
    let candidate = DocEvent {
        principal: Editor::Bob,
        action: DocAction::Read,
        resource: SrcX,
    };

    let store = Arc::new(Store::new().unwrap());
    let mut policy = CompiledPolicy::new(Arc::clone(&store), rules()).unwrap();
    let history = History::new(Arc::clone(&store)).unwrap();
    assert_eq!(
        policy
            .decide(&history, &candidate, || context(
                history.as_slice(),
                &candidate
            ))
            .unwrap(),
        PolicyDecision::Grant,
    );

    let history = History::from_events(
        store,
        [DocEvent {
            principal: Editor::Alice,
            action: DocAction::Edit,
            resource: SrcX,
        }],
    )
    .unwrap();
    assert_eq!(
        policy
            .decide(&history, &candidate, || context(
                history.as_slice(),
                &candidate
            ))
            .unwrap(),
        PolicyDecision::Deny {
            failed_precondition: "src/x was last edited by alice".to_string(),
            allowed_fixes: vec!["alice release src/x".to_string()],
        },
    );
}

fn candidate(action: DocAction) -> DocEvent {
    DocEvent {
        principal: Editor::Bob,
        action,
        resource: SrcX,
    }
}

fn counted_rule(
    mode: history_syntax::RuleMode,
    tail: history_syntax::RegexExpr<DocEvent>,
    calls: Rc<Cell<usize>>,
    label: &'static str,
) -> PolicyRule<DocEvent, usize> {
    let mut rule = forbid(
        DocAction::Read,
        tail,
        Box::new(move |context| {
            assert_eq!(*context, 7);
            calls.set(calls.get() + 1);
            (label.into(), vec![label.into()])
        }),
    );
    rule.rule.mode = mode;
    rule
}

#[test]
fn empty_tables_check_owner_before_context() {
    let store = Arc::new(Store::new().unwrap());
    let mut policy = CompiledPolicy::<DocEvent, ()>::new(Arc::clone(&store), vec![]).unwrap();
    let history = History::new(store).unwrap();
    let foreign = History::new(Arc::new(Store::new().unwrap())).unwrap();
    let probe = candidate(DocAction::Read);
    assert_eq!(
        policy.decide(&history, &probe, || panic!("grant has no context")),
        Ok(PolicyDecision::Grant)
    );
    assert_eq!(
        policy.decide(&foreign, &probe, || panic!(
            "foreign history has no context"
        )),
        Err(junco_core::HistoryError::WrongHistoryOwner)
    );
    assert!(history.is_empty());
    assert!(foreign.is_empty());
}

#[test]
fn callbacks_run_once_for_the_first_actual_violation_only() {
    use history_syntax::{RegexExpr, RuleMode};
    let store = Arc::new(Store::new().unwrap());
    let history = History::from_events(Arc::clone(&store), [candidate(DocAction::Edit)]).unwrap();
    let original = history.as_slice().to_vec();
    let first = Rc::new(Cell::new(0));
    let second = Rc::new(Cell::new(0));
    let contexts = Cell::new(0);
    let mut policy = CompiledPolicy::new(
        Arc::clone(&store),
        vec![
            counted_rule(
                RuleMode::Require,
                RegexExpr::all(),
                Rc::clone(&first),
                "grant",
            ),
            counted_rule(
                RuleMode::Forbid,
                RegexExpr::empty(),
                Rc::clone(&second),
                "grant",
            ),
        ],
    )
    .unwrap();
    assert_eq!(
        policy.decide(&history, &candidate(DocAction::Read), || panic!(
            "grant has no context"
        )),
        Ok(PolicyDecision::Grant)
    );
    assert_eq!(
        policy.decide(&history, &candidate(DocAction::Edit), || panic!(
            "head mismatch has no context"
        )),
        Ok(PolicyDecision::Grant)
    );
    assert_eq!((first.get(), second.get()), (0, 0));

    for mode in [RuleMode::Require, RuleMode::Forbid] {
        let tail = match mode {
            RuleMode::Require => RegexExpr::empty(),
            RuleMode::Forbid => RegexExpr::all(),
        };
        let mut policy = CompiledPolicy::new(
            Arc::clone(&store),
            vec![
                counted_rule(mode, tail, Rc::clone(&first), "first"),
                counted_rule(
                    RuleMode::Forbid,
                    RegexExpr::all(),
                    Rc::clone(&second),
                    "second",
                ),
            ],
        )
        .unwrap();
        assert_eq!(
            policy.decide(&history, &candidate(DocAction::Read), || {
                contexts.set(contexts.get() + 1);
                7
            }),
            Ok(PolicyDecision::Deny {
                failed_precondition: "first".into(),
                allowed_fixes: vec!["first".into()],
            })
        );
    }
    assert_eq!((contexts.get(), first.get(), second.get()), (2, 2, 0));
    assert_eq!(history.as_slice(), original);
}

struct FailPublication;

impl junco_core::limits::Limits for FailPublication {
    fn checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
        Ok(())
    }
    fn publication_checkpoint(&mut self) -> Result<(), junco_core::limits::LimitError> {
        Err(junco_core::limits::LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
    }
    fn enforce_memory(&mut self) -> Result<(), junco_core::limits::LimitError> {
        Ok(())
    }
}

#[test]
fn runtime_errors_never_render_denials_or_change_history() {
    use history_syntax::{RegexExpr, RuleMode};
    use junco_core::HistoryError;
    let store = Arc::new(Store::new().unwrap());
    let mut history = History::new(Arc::clone(&store)).unwrap();
    let calls = Rc::new(Cell::new(0));
    let mut policy = CompiledPolicy::new(
        store,
        vec![counted_rule(
            RuleMode::Forbid,
            RegexExpr::all(),
            Rc::clone(&calls),
            "denied",
        )],
    )
    .unwrap();
    let probe = candidate(DocAction::Read);
    assert!(matches!(
        policy.decide(&history, &probe, || 7),
        Ok(PolicyDecision::Deny { .. })
    ));
    calls.set(0);
    history.push(candidate(DocAction::Edit)).unwrap();
    let raw = history.as_slice().to_vec();
    let numeric = history.numeric().as_slice().to_vec();
    let revision = history.numeric().revision();
    assert!(matches!(
        policy.decide_with_limits(
            &history,
            &probe,
            || panic!("runtime error has no context"),
            &mut FailPublication,
            &mut junco_core::observation::ObservationWorld
        ),
        Err(HistoryError::Limit(_))
    ));
    assert_eq!(calls.get(), 0);
    assert_eq!(history.as_slice(), raw);
    assert_eq!(history.numeric().as_slice(), numeric);
    assert_eq!(history.numeric().revision(), revision);

    let failure = junco_core::observation::fail_reservations_after(0);
    let new_probe = DocEvent {
        principal: Editor::Alice,
        ..probe
    };
    assert_eq!(
        policy.decide(&history, &new_probe, || panic!(
            "allocation error has no context"
        )),
        Err(HistoryError::AllocationFailed)
    );
    drop(failure);
    assert_eq!(calls.get(), 0);
    assert_eq!(history.as_slice(), raw);
    assert_eq!(history.numeric().as_slice(), numeric);
    assert_eq!(history.numeric().revision(), revision);
    assert!(matches!(
        policy.decide(&history, &probe, || 7),
        Ok(PolicyDecision::Deny { .. })
    ));
    assert_eq!(calls.get(), 1);
}

fn deep_rule() -> history_syntax::Rule<DocEvent> {
    let mut tail = history_syntax::RegexExpr::all();
    for _ in 0..4096 {
        tail = history_syntax::RegexExpr::star(tail);
    }
    forbid(
        DocAction::Read,
        tail,
        Box::new(|_: &()| (String::new(), vec![])),
    )
    .rule
}

fn invalid_rule() -> history_syntax::Rule<DocEvent> {
    forbid(
        DocAction::Read,
        history_syntax::RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            history_syntax::AtomPattern::Principal(history_syntax::ComponentPattern::variable(
                "missing",
            )),
        )),
        Box::new(|_: &()| (String::new(), vec![])),
    )
    .rule
}

#[test]
fn failed_constructors_drain_deep_remaining_source_rules() {
    use super::{TracePolicy, TraceRule};
    let store = Arc::new(Store::<DocEvent>::new().unwrap());
    let rules = vec![deep_rule(), deep_rule()]
        .into_iter()
        .map(|rule| PolicyRule {
            rule,
            diagnostic: Box::new(|_: &()| (String::new(), vec![])),
        })
        .collect();
    let failure = junco_core::observation::fail_reservations_after(0);
    assert!(matches!(
        CompiledPolicy::new(Arc::clone(&store), rules),
        Err(junco_core::CompileError::Runtime(
            junco_core::HistoryError::AllocationFailed
        ))
    ));
    drop(failure);

    let rules = vec![invalid_rule(), deep_rule(), deep_rule()]
        .into_iter()
        .map(|rule| PolicyRule {
            rule,
            diagnostic: Box::new(|_: &()| (String::new(), vec![])),
        })
        .collect();
    assert!(matches!(
        CompiledPolicy::new(Arc::clone(&store), rules),
        Err(junco_core::CompileError::UnboundVariable { .. })
    ));

    let rules = [deep_rule(), deep_rule()]
        .into_iter()
        .map(|rule| TraceRule::new(rule, |_| (String::new(), vec![])));
    let failure = junco_core::observation::fail_reservations_after(0);
    assert!(matches!(
        TracePolicy::new(Arc::clone(&store), rules),
        Err(junco_core::CompileError::Runtime(
            junco_core::HistoryError::AllocationFailed
        ))
    ));
    drop(failure);
    let rules = [invalid_rule(), deep_rule(), deep_rule()]
        .into_iter()
        .map(|rule| TraceRule::new(rule, |_| (String::new(), vec![])));
    assert!(matches!(
        TracePolicy::new(store, rules),
        Err(junco_core::CompileError::UnboundVariable { .. })
    ));
}

#[test]
fn trace_policy_uses_the_same_store_without_mutating_external_history() {
    use super::{TracePolicy, TraceRule};
    let store = Arc::new(Store::new().unwrap());
    let history = History::new(Arc::clone(&store)).unwrap();
    let rule = forbid(
        DocAction::Read,
        history_syntax::RegexExpr::all(),
        Box::new(|_: &()| (String::new(), vec![])),
    )
    .rule;
    let calls = Arc::new(core::sync::atomic::AtomicUsize::new(0));
    let diagnostic_calls = Arc::clone(&calls);
    let rule = TraceRule::new(rule, move |event: &DocEvent| {
        diagnostic_calls.fetch_add(1, core::sync::atomic::Ordering::SeqCst);
        (event.principal.to_string(), vec![])
    });
    let cloned = rule.clone();
    assert!(format!("{cloned:?}").starts_with("TraceRule"));
    let mut policy = TracePolicy::new(store, [cloned]).unwrap();
    assert_eq!(
        policy.decide(&history, &candidate(DocAction::Edit)),
        Ok(PolicyDecision::Grant)
    );
    assert_eq!(calls.load(core::sync::atomic::Ordering::SeqCst), 0);
    assert_eq!(
        policy.decide(&history, &candidate(DocAction::Read)),
        Ok(PolicyDecision::Deny {
            failed_precondition: "bob".into(),
            allowed_fixes: vec![],
        })
    );
    assert_eq!(calls.load(core::sync::atomic::Ordering::SeqCst), 1);
    let foreign = History::new(Arc::new(Store::new().unwrap())).unwrap();
    assert_eq!(
        policy.decide(&foreign, &candidate(DocAction::Read)),
        Err(junco_core::HistoryError::WrongHistoryOwner)
    );
    assert_eq!(calls.load(core::sync::atomic::Ordering::SeqCst), 1);
    assert!(history.is_empty());
}
