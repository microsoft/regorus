use history_syntax::{
    AtomPattern, Comparison, Component, ComponentPattern, Event, Head, RegexExpr, Rule, RuleMode,
    TestExpr,
};
use junco_core::scope::VariableScope;
use junco_core::{CompileError, Grant, Request};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DocumentEvent {
    principal: u8,
    action: u8,
    resource: u8,
    payload: u16,
}

impl Event for DocumentEvent {
    type Principal = u8;
    type Action = u8;
    type Resource = u8;
    fn principal(self) -> u8 {
        self.principal
    }
    fn action(self) -> u8 {
        self.action
    }
    fn resource(self) -> u8 {
        self.resource
    }
}

fn head() -> Head<DocumentEvent> {
    Head::new(
        ComponentPattern::variable("actor"),
        ComponentPattern::constant(2_u8),
        ComponentPattern::variable("document"),
    )
}

fn action(value: u8) -> RegexExpr<DocumentEvent> {
    RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Action(ComponentPattern::constant(value)),
    ))
}

#[test]
fn borrowed_scope_binds_same_coordinate_and_rejects_cross_domain_reuse() {
    let mut scope = VariableScope::new();
    scope.bind(Component::Principal, "actor").unwrap();
    scope.bind(Component::Action, "operation").unwrap();
    scope.bind(Component::Resource, "document").unwrap();
    scope.bind(Component::Principal, "actor").unwrap();
    assert_eq!(
        scope.resolve(Component::Principal, "actor"),
        Ok(Component::Principal)
    );
    assert_eq!(
        scope.resolve(Component::Action, "operation"),
        Ok(Component::Action)
    );
    assert_eq!(
        scope.resolve(Component::Resource, "document"),
        Ok(Component::Resource)
    );
    assert_eq!(
        scope.bind(Component::Resource, "actor"),
        Err(CompileError::VariableComponentConflict {
            name: "actor".into(),
        })
    );
    assert_eq!(scope.name(Component::Resource), Some("document"));
    assert_eq!(
        scope.resolve(Component::Resource, "actor"),
        Err(CompileError::VariableComponentConflict {
            name: "actor".into(),
        })
    );
    assert_eq!(
        scope.resolve(Component::Principal, "missing"),
        Err(CompileError::UnboundVariable {
            name: "missing".into(),
        })
    );
}

#[test]
fn request_and_grant_preserve_event_and_opaque_metadata() {
    let event = DocumentEvent {
        principal: 1,
        action: 2,
        resource: 3,
        payload: 99,
    };
    let right = event;
    let request = Request::new(right, String::from("opaque"));
    let grant = Grant {
        event: request.event,
        metadata: request.metadata,
    };
    assert_eq!(grant.event, right);
    assert_eq!(grant.metadata, "opaque");
}

fn flatten(
    rule: &Rule<DocumentEvent>,
) -> Result<junco_core::flat::FlatRule<junco_core::ComponentValue<DocumentEvent>>, CompileError> {
    junco_core::flatten_rule(
        rule,
        &mut junco_core::limits::Unmetered,
        &mut junco_core::observation::ObservationWorld,
    )
}

#[test]
fn flattening_resolves_names_and_retains_concrete_component_tags() {
    use junco_core::ComponentValue;
    use junco_core::flat::{FlatHead, FlatRegex, FlatTerm, FlatTest};
    let rule = Rule::new(
        RuleMode::Forbid,
        head(),
        RegexExpr::test(TestExpr::and([
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Principal(ComponentPattern::variable("actor")),
            ),
            TestExpr::atom(
                Comparison::Neq,
                AtomPattern::Resource(ComponentPattern::variable("document")),
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(1_u8)),
            ),
        ])),
    );
    let flat = flatten(&rule).unwrap();
    assert_eq!(flat.mode, RuleMode::Forbid);
    assert_eq!(
        flat.source.head,
        [
            FlatHead::Bind,
            FlatHead::Constant(ComponentValue::Action(2)),
            FlatHead::Bind
        ]
    );
    assert_eq!(
        flat.source.tests,
        vec![
            FlatTest::Atom {
                field: Component::Principal,
                term: FlatTerm::Variable(Component::Principal),
                positive: true
            },
            FlatTest::Atom {
                field: Component::Resource,
                term: FlatTerm::Variable(Component::Resource),
                positive: false
            },
            FlatTest::Atom {
                field: Component::Action,
                term: FlatTerm::Constant(ComponentValue::Action(1)),
                positive: true
            },
            FlatTest::And(vec![0, 1, 2]),
        ]
    );
    assert_eq!(flat.source.regexes, vec![FlatRegex::Test(3)]);
    assert_eq!(flat.source.root, 0);
    assert_eq!(flat.source.validate(), Ok(()));
    assert_eq!(
        rule.tail,
        RegexExpr::test(TestExpr::and([
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Principal(ComponentPattern::variable("actor"))
            ),
            TestExpr::atom(
                Comparison::Neq,
                AtomPattern::Resource(ComponentPattern::variable("document"))
            ),
            TestExpr::atom(
                Comparison::Eq,
                AtomPattern::Action(ComponentPattern::constant(1_u8))
            ),
        ]))
    );
}

#[test]
fn flattening_reports_scope_errors_without_consuming_the_rule() {
    let unbound = Rule::new(
        RuleMode::Require,
        head(),
        RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Principal(ComponentPattern::variable("missing")),
        )),
    );
    assert_eq!(
        flatten(&unbound),
        Err(CompileError::UnboundVariable {
            name: "missing".into()
        })
    );
    let wrong_coordinate = Rule::new(
        RuleMode::Require,
        head(),
        RegexExpr::test(TestExpr::atom(
            Comparison::Eq,
            AtomPattern::Resource(ComponentPattern::variable("actor")),
        )),
    );
    assert_eq!(
        flatten(&wrong_coordinate),
        Err(CompileError::VariableComponentConflict {
            name: "actor".into()
        })
    );
    let conflicting_head = Rule::<DocumentEvent>::new(
        RuleMode::Require,
        Head::new(
            ComponentPattern::variable("same"),
            ComponentPattern::variable("same"),
            ComponentPattern::variable("same"),
        ),
        RegexExpr::empty(),
    );
    assert_eq!(
        flatten(&conflicting_head),
        Err(CompileError::VariableComponentConflict {
            name: "same".into()
        })
    );
    assert_eq!(unbound.mode, RuleMode::Require);
    assert_eq!(wrong_coordinate.head, head());
    unbound.dispose();
    wrong_coordinate.dispose();
    conflicting_head.dispose();
}

#[test]
fn flattening_keeps_empty_identities_complement_and_concat_source_order() {
    use junco_core::flat::{FlatRegex, FlatTest};
    let rule = Rule::new(
        RuleMode::Require,
        head(),
        RegexExpr::concat([
            RegexExpr::test(TestExpr::and([])),
            RegexExpr::test(TestExpr::or([])),
            RegexExpr::concat([]),
            RegexExpr::union([]),
            RegexExpr::intersect([]),
            RegexExpr::complement(RegexExpr::epsilon()),
            RegexExpr::star(RegexExpr::all()),
            RegexExpr::empty(),
        ]),
    );
    let flat = flatten(&rule).unwrap();
    assert_eq!(
        flat.source.tests,
        vec![FlatTest::And(vec![]), FlatTest::Or(vec![])]
    );
    assert_eq!(
        flat.source.regexes,
        vec![
            FlatRegex::Test(0),
            FlatRegex::Test(1),
            FlatRegex::Concat(vec![]),
            FlatRegex::Union(vec![]),
            FlatRegex::Intersect(vec![]),
            FlatRegex::Epsilon,
            FlatRegex::Complement(5),
            FlatRegex::All,
            FlatRegex::Star(7),
            FlatRegex::Empty,
            FlatRegex::Concat(vec![0, 1, 2, 3, 4, 6, 8, 9]),
        ]
    );
    assert_eq!(flat.source.root, 10);
    assert_eq!(flat.source.validate(), Ok(()));
    let ordered = Rule::new(
        RuleMode::Require,
        head(),
        RegexExpr::concat([action(1), action(2)]),
    );
    let reversed = Rule::new(
        RuleMode::Require,
        head(),
        RegexExpr::concat([action(2), action(1)]),
    );
    assert_ne!(flatten(&ordered).unwrap(), flatten(&reversed).unwrap());
}

#[test]
fn component_equality_uses_native_identity_not_representation() {
    use core::hash::{Hash, Hasher};
    #[derive(Clone, Copy, Debug)]
    struct Identity {
        key: u8,
        payload: u8,
    }
    impl PartialEq for Identity {
        fn eq(&self, other: &Self) -> bool {
            self.key == other.key
        }
    }
    impl Eq for Identity {}
    impl Hash for Identity {
        fn hash<H: Hasher>(&self, state: &mut H) {
            0_u8.hash(state);
        }
    }
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    struct IdentityEvent(Identity);
    impl Event for IdentityEvent {
        type Principal = Identity;
        type Action = Identity;
        type Resource = Identity;
        fn principal(self) -> Identity {
            self.0
        }
        fn action(self) -> Identity {
            self.0
        }
        fn resource(self) -> Identity {
            self.0
        }
    }
    use junco_core::ComponentValue;
    let original = Identity { key: 7, payload: 1 };
    let equal = Identity { key: 7, payload: 2 };
    let unequal = Identity { key: 8, payload: 1 };
    assert_ne!(original.payload, equal.payload);
    assert_eq!(
        ComponentValue::<IdentityEvent>::Principal(original),
        ComponentValue::Principal(equal)
    );
    assert_ne!(
        ComponentValue::<IdentityEvent>::Principal(original),
        ComponentValue::Principal(unequal)
    );
    assert_ne!(
        ComponentValue::<IdentityEvent>::Principal(original),
        ComponentValue::Resource(original)
    );
}

#[test]
fn deep_borrowed_lowering_keeps_success_and_failure_teardown_iterative() {
    let mut valid = RegexExpr::epsilon();
    let mut invalid = RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::Principal(ComponentPattern::variable("missing")),
    ));
    for _ in 0..4096 {
        valid = RegexExpr::complement(valid);
        invalid = RegexExpr::star(invalid);
    }
    let valid = Rule::new(RuleMode::Require, head(), valid);
    let invalid = Rule::new(RuleMode::Require, head(), invalid);
    let flat = flatten(&valid).unwrap();
    assert_eq!(flat.source.regexes.len(), 4097);
    assert_eq!(flat.source.root, 4096);
    assert_eq!(
        flatten(&invalid),
        Err(CompileError::UnboundVariable {
            name: "missing".into()
        })
    );
    valid.dispose();
    invalid.dispose();
}

#[test]
fn lowering_propagates_resource_errors_without_consuming_source() {
    use junco_core::limits::{LimitError, Limits};
    use junco_core::{HistoryError, flatten_rule};
    struct Exhausted;
    impl Limits for Exhausted {
        fn checkpoint(&mut self) -> Result<(), LimitError> {
            Err(LimitError::MemoryLimitExceeded { usage: 2, limit: 1 })
        }
        fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
            self.checkpoint()
        }
        fn enforce_memory(&mut self) -> Result<(), LimitError> {
            self.checkpoint()
        }
    }
    let rule = Rule::new(RuleMode::Require, head(), action(1));
    let result = flatten_rule(
        &rule,
        &mut Exhausted,
        &mut junco_core::observation::ObservationWorld,
    );
    assert_eq!(
        result,
        Err(CompileError::Runtime(HistoryError::Limit(
            LimitError::MemoryLimitExceeded { usage: 2, limit: 1 }
        )))
    );
    assert_eq!(rule.tail, action(1));
    rule.dispose();
}

#[test]
fn flattening_boolean_leaves_and_nested_operands_keep_postorder() {
    use junco_core::flat::{FlatRegex, FlatTest};
    let rule = Rule::new(
        RuleMode::Require,
        head(),
        RegexExpr::test(TestExpr::or([
            TestExpr::and([TestExpr::true_test(), TestExpr::false_test()]),
            TestExpr::true_test(),
        ])),
    );
    let flat = flatten(&rule).unwrap();
    assert_eq!(
        flat.source.tests,
        vec![
            FlatTest::Bool(true),
            FlatTest::Bool(false),
            FlatTest::And(vec![0, 1]),
            FlatTest::Bool(true),
            FlatTest::Or(vec![2, 3])
        ]
    );
    assert_eq!(flat.source.regexes, vec![FlatRegex::Test(4)]);
    assert_eq!(flat.source.validate(), Ok(()));
}
