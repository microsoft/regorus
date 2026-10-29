use history_syntax::{
    AtomPattern, CNil, Comparison, Component, ComponentPattern, Coproduct, Event, Head, RegexExpr,
    Rule, RuleMode, TestExpr,
};

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
fn typed_constructors_keep_values_names_and_field_order() {
    assert_eq!(
        ComponentPattern::<u32>::constant(7_u8),
        ComponentPattern::Constant(7_u32)
    );
    assert_eq!(
        ComponentPattern::<u32>::variable("actor"),
        ComponentPattern::Variable("actor".into())
    );
    let rule = Rule::new(RuleMode::Require, head(), action(1));
    assert_eq!(rule.mode, RuleMode::Require);
    assert_eq!(
        rule.head.principal,
        ComponentPattern::Variable("actor".into())
    );
    assert_eq!(rule.head.action, ComponentPattern::Constant(2));
    assert_eq!(
        rule.head.resource,
        ComponentPattern::Variable("document".into())
    );
    assert_eq!(rule.tail, action(1));
}

#[test]
fn comparisons_and_atoms_preserve_the_selected_domain() {
    assert_eq!(!Comparison::Eq, Comparison::Neq);
    assert_eq!(!Comparison::Neq, Comparison::Eq);
    let principal: AtomPattern<DocumentEvent> =
        AtomPattern::Principal(ComponentPattern::constant(1_u8));
    let action: AtomPattern<DocumentEvent> = AtomPattern::Action(ComponentPattern::constant(1_u8));
    let resource: AtomPattern<DocumentEvent> =
        AtomPattern::Resource(ComponentPattern::constant(1_u8));
    assert_eq!(principal.component(), Component::Principal);
    assert_eq!(action.component(), Component::Action);
    assert_eq!(resource.component(), Component::Resource);
    assert_ne!(principal, action);
    assert_ne!(action, resource);
}

#[test]
fn boolean_constructors_retain_empty_operators_and_iterator_order() {
    type Test = TestExpr<DocumentEvent>;
    assert_eq!(Test::true_test(), Test::True);
    assert_eq!(Test::false_test(), Test::False);
    assert_eq!(Test::and([]), Test::And(vec![]));
    assert_eq!(Test::or([]), Test::Or(vec![]));
    assert_eq!(
        Test::and([Test::True, Test::False]),
        Test::And(vec![Test::True, Test::False])
    );
    assert_eq!(
        Test::or([Test::False, Test::True]),
        Test::Or(vec![Test::False, Test::True])
    );
}

#[test]
fn regex_constructors_keep_whole_word_complement_and_concat_order() {
    type Regex = RegexExpr<DocumentEvent>;
    assert_eq!(Regex::empty(), Regex::Empty);
    assert_eq!(Regex::all(), Regex::All);
    assert_eq!(Regex::epsilon(), Regex::Epsilon);
    assert_eq!(Regex::concat([]), Regex::Concat(vec![]));
    assert_eq!(Regex::union([]), Regex::Union(vec![]));
    assert_eq!(Regex::intersect([]), Regex::Intersect(vec![]));
    assert_eq!(
        Regex::concat([action(1), action(2)]),
        Regex::Concat(vec![action(1), action(2)])
    );
    assert_ne!(
        Regex::concat([action(1), action(2)]),
        Regex::concat([action(2), action(1)])
    );
    assert_eq!(Regex::star(action(1)), Regex::Star(Box::new(action(1))));
    assert_eq!(
        Regex::complement(action(1)),
        Regex::Not(Box::new(action(1)))
    );
    assert_eq!(
        Regex::union([action(1), action(2)]),
        Regex::Union(vec![action(1), action(2)])
    );
    assert_eq!(
        Regex::intersect([action(1), action(2)]),
        Regex::Intersect(vec![action(1), action(2)])
    );
}

#[test]
fn conversions_use_the_callers_actual_conversion() {
    struct Offset(u8);
    impl From<Offset> for u16 {
        fn from(value: Offset) -> u16 {
            u16::from(value.0) + 10
        }
    }
    assert_eq!(
        ComponentPattern::<u16>::constant(Offset(3)),
        ComponentPattern::Constant(13)
    );
}

#[test]
fn coproducts_forward_projections_without_changing_event_identity() {
    type Events = Coproduct<DocumentEvent, Coproduct<DocumentEvent, CNil>>;
    let event = DocumentEvent {
        principal: 1,
        action: 2,
        resource: 3,
        payload: 99,
    };
    let left: Events = Coproduct::Inl(event);
    let right: Events = Coproduct::Inr(Coproduct::Inl(event));
    assert_eq!(
        (left.principal(), left.action(), left.resource()),
        (1, 2, 3)
    );
    assert_eq!(
        (right.principal(), right.action(), right.resource()),
        (1, 2, 3)
    );
    assert_ne!(left, right);
}

#[test]
fn iterative_disposal_handles_deep_owned_trees() {
    let mut tail: RegexExpr<DocumentEvent> = RegexExpr::epsilon();
    for _ in 0..4096 {
        tail = RegexExpr::complement(tail);
    }
    Rule::new(RuleMode::Require, head(), tail).dispose();
    let mut test: TestExpr<DocumentEvent> = TestExpr::true_test();
    for _ in 0..4096 {
        test = TestExpr::and([test]);
    }
    Rule::new(RuleMode::Require, head(), RegexExpr::test(test)).dispose();
}
