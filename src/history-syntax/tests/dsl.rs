use history_syntax::{
    AtomPattern, CNil, Comparison, Component, Component3, ComponentPattern, Coproduct, Event, Head,
    N3, RegexExpr, Rule, RuleMode, TestExpr,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct DocumentEvent {
    principal: u8,
    action: u8,
    resource: u8,
    payload: u16,
}

impl Event for DocumentEvent {
    type Component = Component3<u8, u8, u8>;
    type Arity = N3;

    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component3::C0(self.principal),
            1 => Component3::C1(self.action),
            _ => Component3::C2(self.resource),
        }
    }

    fn coordinate(component: Self::Component) -> usize {
        match component {
            Component3::C0(_) => 0,
            Component3::C1(_) => 1,
            Component3::C2(_) => 2,
        }
    }
}

fn head() -> Head<DocumentEvent> {
    Head::new([
        ComponentPattern::variable("actor"),
        ComponentPattern::constant(Component3::C1(2)),
        ComponentPattern::variable("document"),
    ])
}

fn action(value: u8) -> RegexExpr<DocumentEvent> {
    RegexExpr::test(TestExpr::atom(
        Comparison::Eq,
        AtomPattern::new(
            Component(1),
            ComponentPattern::constant(Component3::C1(value)),
        ),
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
        rule.head.slots()[0],
        ComponentPattern::Variable("actor".into())
    );
    assert_eq!(
        rule.head.slots()[1],
        ComponentPattern::Constant(Component3::C1(2))
    );
    assert_eq!(
        rule.head.slots()[2],
        ComponentPattern::Variable("document".into())
    );
    assert_eq!(rule.tail, action(1));
}

#[test]
fn comparisons_and_atoms_preserve_the_selected_domain() {
    assert_eq!(!Comparison::Eq, Comparison::Neq);
    assert_eq!(!Comparison::Neq, Comparison::Eq);
    let principal: AtomPattern<DocumentEvent> =
        AtomPattern::new(Component(0), ComponentPattern::constant(Component3::C0(1)));
    let action: AtomPattern<DocumentEvent> =
        AtomPattern::new(Component(1), ComponentPattern::constant(Component3::C1(1)));
    let resource: AtomPattern<DocumentEvent> =
        AtomPattern::new(Component(2), ComponentPattern::constant(Component3::C2(1)));
    assert_eq!(principal.component(), Component(0));
    assert_eq!(action.component(), Component(1));
    assert_eq!(resource.component(), Component(2));
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
    for (index, expected) in [Component3::C0(1), Component3::C1(2), Component3::C2(3)]
        .into_iter()
        .enumerate()
    {
        assert_eq!(left.component(index), expected);
        assert_eq!(right.component(index), expected);
        assert_eq!(Events::coordinate(expected), index);
    }
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
