use history_syntax::{Component, RuleMode};
use junco_core::HistoryError;
use junco_core::flat::{FlatBuilder, FlatHead, FlatPair, FlatRegex, FlatRule, FlatTerm, FlatTest};
use junco_core::limits::{LimitError, Limits, Unmetered};
use junco_core::observation::ObservationWorld;

fn pair<C>() -> FlatPair<C> {
    FlatPair {
        head: [FlatHead::Any, FlatHead::Any, FlatHead::Any],
        tests: Vec::new(),
        regexes: vec![FlatRegex::Epsilon],
        root: 0,
    }
}

#[test]
fn rejects_forward_cycles_and_missing_tests() {
    let mut source = pair::<String>();
    assert_eq!(source.validate(), Ok(()));
    source.regexes = vec![FlatRegex::Star(0)];
    assert!(source.validate().is_err());
    source.regexes = vec![FlatRegex::Test(0)];
    assert!(source.validate().is_err());
    source.tests = vec![FlatTest::And(vec![0])];
    assert!(source.validate().is_err());
    source.tests = vec![FlatTest::Bool(true)];
    assert_eq!(source.validate(), Ok(()));
    source.root = 1;
    assert!(source.validate().is_err());
}

#[test]
fn rejects_cross_domain_and_unbound_variables() {
    let mut source = pair::<String>();
    source.tests.push(FlatTest::Atom {
        field: Component::Action,
        term: FlatTerm::Variable(Component::Principal),
        positive: true,
    });
    assert!(source.validate().is_err());
    source.tests.clear();
    source.tests.push(FlatTest::Atom {
        field: Component::Principal,
        term: FlatTerm::Variable(Component::Principal),
        positive: false,
    });
    assert!(source.validate().is_err());
    source.head[0] = FlatHead::Bind;
    assert_eq!(source.validate(), Ok(()));
}

#[test]
fn validation_preserves_exact_errors_and_precedence() {
    let mut source = pair::<()>();
    source.root = u32::MAX;
    source.regexes = vec![FlatRegex::Test(u32::MAX)];
    source.tests = vec![FlatTest::Or(vec![0])];
    assert_eq!(
        source.validate().unwrap_err(),
        "history test reference must point to an earlier node"
    );
    source.tests = vec![FlatTest::Atom {
        field: Component::Resource,
        term: FlatTerm::Variable(Component::Resource),
        positive: true,
    }];
    assert_eq!(
        source.validate().unwrap_err(),
        "history variable must bind its own head domain"
    );
    source.head[2] = FlatHead::Bind;
    assert_eq!(
        source.validate().unwrap_err(),
        "history regex test reference is out of bounds"
    );
    source.regexes = vec![FlatRegex::Complement(1), FlatRegex::Star(0)];
    assert_eq!(
        source.validate().unwrap_err(),
        "history regex reference must point to an earlier node"
    );
    source.regexes = vec![FlatRegex::Epsilon];
    assert_eq!(
        source.validate().unwrap_err(),
        "history regex root is out of bounds"
    );
}

#[test]
fn checks_every_reference_variant() {
    for test in [FlatTest::<()>::And(vec![1]), FlatTest::Or(vec![u32::MAX])] {
        let mut source = pair();
        source.tests = vec![test, FlatTest::Bool(true)];
        assert_eq!(
            source.validate().unwrap_err(),
            "history test reference must point to an earlier node"
        );
    }
    for regex in [
        FlatRegex::Concat(vec![1]),
        FlatRegex::Union(vec![u32::MAX]),
        FlatRegex::Intersect(vec![0]),
        FlatRegex::Star(0),
        FlatRegex::Complement(1),
    ] {
        let mut source = pair::<()>();
        source.regexes = vec![regex, FlatRegex::Epsilon];
        assert_eq!(
            source.validate().unwrap_err(),
            "history regex reference must point to an earlier node"
        );
    }
    for field in [Component::Principal, Component::Action, Component::Resource] {
        for variable in [Component::Principal, Component::Action, Component::Resource] {
            let mut source = pair::<()>();
            source.head = [FlatHead::Bind, FlatHead::Bind, FlatHead::Bind];
            source.tests = vec![FlatTest::Atom {
                field,
                term: FlatTerm::Variable(variable),
                positive: false,
            }];
            assert_eq!(source.validate().is_ok(), field == variable);
        }
    }
}

#[test]
fn accepts_repeated_edges_unused_nodes_and_non_last_root() {
    let source = FlatPair::<()> {
        head: [FlatHead::Any, FlatHead::Bind, FlatHead::Any],
        tests: vec![
            FlatTest::Bool(true),
            FlatTest::And(vec![0, 0]),
            FlatTest::Or(vec![0, 1, 0]),
        ],
        regexes: vec![
            FlatRegex::Epsilon,
            FlatRegex::Concat(vec![0, 0]),
            FlatRegex::Union(vec![0, 1, 0]),
            FlatRegex::Test(2),
            FlatRegex::Intersect(vec![0, 1]),
            FlatRegex::Star(4),
            FlatRegex::Complement(5),
        ],
        root: 1,
    };
    assert_eq!(source.validate(), Ok(()));
    assert_eq!(source.regexes.len(), 7);
    assert_eq!(source.regexes[1], FlatRegex::Concat(vec![0, 0]));
}

#[test]
fn empty_operators_and_generic_constants_need_no_runtime_or_equality() {
    struct Opaque;
    let source = FlatPair {
        head: [FlatHead::Constant(Opaque), FlatHead::Any, FlatHead::Bind],
        tests: vec![
            FlatTest::And(vec![]),
            FlatTest::Or(vec![]),
            FlatTest::Atom {
                field: Component::Action,
                term: FlatTerm::Constant(Opaque),
                positive: false,
            },
        ],
        regexes: vec![
            FlatRegex::Empty,
            FlatRegex::All,
            FlatRegex::Epsilon,
            FlatRegex::Concat(vec![]),
            FlatRegex::Union(vec![]),
            FlatRegex::Intersect(vec![]),
        ],
        root: 3,
    };
    assert_eq!(source.validate(), Ok(()));
    let rule = FlatRule {
        mode: RuleMode::Require,
        source,
    };
    assert_eq!(rule.mode, RuleMode::Require);
    let empty = FlatPair::<Opaque> {
        regexes: vec![],
        ..pair()
    };
    assert_eq!(
        empty.validate().unwrap_err(),
        "history regex root is out of bounds"
    );
}

#[derive(Default)]
struct ProbeLimits {
    fail_checkpoint: bool,
    fail_memory: bool,
}

impl Limits for ProbeLimits {
    fn checkpoint(&mut self) -> Result<(), LimitError> {
        if self.fail_checkpoint {
            Err(LimitError::RegexSizeLimitExceeded { limit: 0 })
        } else {
            Ok(())
        }
    }

    fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
        panic!("flat construction must not publish a decision")
    }

    fn enforce_memory(&mut self) -> Result<(), LimitError> {
        if self.fail_memory {
            Err(LimitError::MemoryLimitExceeded { usage: 1, limit: 0 })
        } else {
            Ok(())
        }
    }
}

#[test]
fn builder_preserves_supplied_topology_and_allows_any_valid_root() {
    let mut builder = FlatBuilder::<()>::new([FlatHead::Any, FlatHead::Any, FlatHead::Any]);
    let mut limits = ProbeLimits::default();
    let mut world = ObservationWorld;
    assert_eq!(
        builder.test(FlatTest::Bool(true), &mut limits, &mut world),
        Ok(0)
    );
    assert_eq!(
        builder.test(FlatTest::And(vec![0, 0]), &mut limits, &mut world),
        Ok(1)
    );
    assert_eq!(
        builder.regex(FlatRegex::Epsilon, &mut limits, &mut world),
        Ok(0)
    );
    assert_eq!(
        builder.regex(FlatRegex::Concat(vec![0, 0]), &mut limits, &mut world),
        Ok(1)
    );
    assert_eq!(
        builder.regex(FlatRegex::Test(1), &mut limits, &mut world),
        Ok(2)
    );
    let source = builder.finish(1).unwrap();
    assert_eq!(source.validate(), Ok(()));
    assert_eq!(
        source.tests,
        vec![FlatTest::Bool(true), FlatTest::And(vec![0, 0])]
    );
    assert_eq!(
        source.regexes,
        vec![
            FlatRegex::Epsilon,
            FlatRegex::Concat(vec![0, 0]),
            FlatRegex::Test(1)
        ]
    );
}

#[test]
fn builder_rejects_bad_nodes_without_mutating_prefixes() {
    let mut builder = FlatBuilder::<()>::new([FlatHead::Any, FlatHead::Bind, FlatHead::Any]);
    let mut limits = Unmetered;
    let mut world = ObservationWorld;
    let invalid = HistoryError::InvalidPolicy {
        path: "$".into(),
        message: "invalid portable history source",
    };
    for node in [
        FlatTest::And(vec![0]),
        FlatTest::Or(vec![u32::MAX]),
        FlatTest::Atom {
            field: Component::Action,
            term: FlatTerm::Variable(Component::Principal),
            positive: true,
        },
        FlatTest::Atom {
            field: Component::Resource,
            term: FlatTerm::Variable(Component::Resource),
            positive: false,
        },
    ] {
        assert_eq!(
            builder.test(node, &mut limits, &mut world),
            Err(invalid.clone())
        );
        assert!(builder.tests().is_empty());
        assert!(builder.regexes().is_empty());
        assert_eq!(
            builder.head(),
            &[FlatHead::Any, FlatHead::Bind, FlatHead::Any]
        );
    }
    for node in [
        FlatRegex::Test(0),
        FlatRegex::Concat(vec![0]),
        FlatRegex::Union(vec![1]),
        FlatRegex::Intersect(vec![0]),
        FlatRegex::Star(0),
        FlatRegex::Complement(0),
    ] {
        assert_eq!(
            builder.regex(node, &mut limits, &mut world),
            Err(invalid.clone())
        );
        assert!(builder.tests().is_empty());
        assert!(builder.regexes().is_empty());
    }
    assert_eq!(
        builder.test(
            FlatTest::Atom {
                field: Component::Action,
                term: FlatTerm::Variable(Component::Action),
                positive: true,
            },
            &mut limits,
            &mut world
        ),
        Ok(0)
    );
    assert_eq!(
        builder.regex(FlatRegex::Test(0), &mut limits, &mut world),
        Ok(0)
    );
    assert_eq!(builder.finish(1), Err(invalid));
}

#[test]
fn builder_limit_failures_preserve_all_existing_nodes() {
    let mut builder = FlatBuilder::<()>::new([FlatHead::Any, FlatHead::Any, FlatHead::Any]);
    let mut limits = ProbeLimits::default();
    let mut world = ObservationWorld;
    builder
        .test(FlatTest::Bool(true), &mut limits, &mut world)
        .unwrap();
    builder
        .regex(FlatRegex::Epsilon, &mut limits, &mut world)
        .unwrap();
    for checkpoint in [true, false] {
        limits.fail_checkpoint = checkpoint;
        limits.fail_memory = !checkpoint;
        assert!(matches!(
            builder.test(FlatTest::Or(vec![0]), &mut limits, &mut world),
            Err(HistoryError::Limit(_))
        ));
        assert!(matches!(
            builder.regex(FlatRegex::Star(0), &mut limits, &mut world),
            Err(HistoryError::Limit(_))
        ));
        assert_eq!(builder.tests(), &vec![FlatTest::Bool(true)]);
        assert_eq!(builder.regexes(), &vec![FlatRegex::Epsilon]);
    }
    limits.fail_checkpoint = false;
    limits.fail_memory = false;
    assert_eq!(
        builder.test(FlatTest::And(vec![0, 0]), &mut limits, &mut world),
        Ok(1)
    );
    assert_eq!(
        builder.regex(FlatRegex::Concat(vec![0, 0]), &mut limits, &mut world),
        Ok(1)
    );
    assert_eq!(builder.finish(0).unwrap().validate(), Ok(()));
}

#[test]
fn deep_shared_dag_stays_flat() {
    let mut builder = FlatBuilder::<()>::new([FlatHead::Any, FlatHead::Any, FlatHead::Any]);
    let mut limits = Unmetered;
    let mut world = ObservationWorld;
    builder
        .regex(FlatRegex::Epsilon, &mut limits, &mut world)
        .unwrap();
    for index in 1..4096 {
        assert_eq!(
            builder.regex(
                FlatRegex::Concat(vec![index - 1, index - 1]),
                &mut limits,
                &mut world
            ),
            Ok(index)
        );
    }
    let source = builder.finish(4095).unwrap();
    assert_eq!(source.validate(), Ok(()));
    assert_eq!(source.regexes.len(), 4096);
    assert_eq!(
        source
            .regexes
            .iter()
            .map(|node| match node {
                FlatRegex::Concat(ids) => ids.len(),
                _ => 0,
            })
            .sum::<usize>(),
        8190
    );
}

#[cfg(feature = "serde")]
#[test]
fn serde_keeps_version_eight_names_variant_order_and_field_order() {
    let source = FlatPair {
        head: [
            FlatHead::Any,
            FlatHead::Constant(String::from("x")),
            FlatHead::Bind,
        ],
        tests: vec![
            FlatTest::Bool(true),
            FlatTest::Atom {
                field: Component::Action,
                term: FlatTerm::Constant(String::from("a")),
                positive: false,
            },
            FlatTest::And(vec![0, 1]),
            FlatTest::Or(vec![]),
        ],
        regexes: vec![
            FlatRegex::Empty,
            FlatRegex::All,
            FlatRegex::Epsilon,
            FlatRegex::Test(1),
            FlatRegex::Concat(vec![2, 3]),
            FlatRegex::Union(vec![]),
            FlatRegex::Intersect(vec![]),
            FlatRegex::Star(4),
            FlatRegex::Complement(7),
        ],
        root: 3,
    };
    assert_eq!(source.validate(), Ok(()));
    let json = r#"{"head":["Any",{"Constant":"x"},"Bind"],"tests":[{"Bool":true},{"Atom":{"field":"Action","term":{"Constant":"a"},"positive":false}},{"And":[0,1]},{"Or":[]}],"regexes":["Empty","All","Epsilon",{"Test":1},{"Concat":[2,3]},{"Union":[]},{"Intersect":[]},{"Star":4},{"Complement":7}],"root":3}"#;
    assert_eq!(serde_json::to_string(&source).unwrap(), json);
    assert_eq!(
        serde_json::from_str::<FlatPair<String>>(json).unwrap(),
        source
    );
    // Literal old-layout bytes, not an expectation generated by the serializer under test.
    let bytes = [
        0, 1, 1, b'x', 2, 4, 0, 1, 1, 1, 0, 1, b'a', 0, 2, 2, 0, 1, 3, 0, 9, 0, 1, 2, 3, 1, 4, 2,
        2, 3, 5, 0, 6, 0, 7, 4, 8, 7, 3,
    ];
    assert_eq!(postcard::to_allocvec(&source).unwrap(), bytes);
    assert_eq!(
        postcard::from_bytes::<FlatPair<String>>(&bytes).unwrap(),
        source
    );
    for (field, ordinal) in [
        (Component::Principal, 0),
        (Component::Action, 1),
        (Component::Resource, 2),
    ] {
        assert_eq!(
            postcard::to_allocvec(&FlatTerm::<String>::Variable(field)).unwrap(),
            vec![1, ordinal]
        );
    }
    for (mode, ordinal) in [(RuleMode::Require, 0), (RuleMode::Forbid, 1)] {
        let rule = FlatRule {
            mode,
            source: source.clone(),
        };
        let mut expected = vec![ordinal];
        expected.extend_from_slice(&bytes);
        assert_eq!(postcard::to_allocvec(&rule).unwrap(), expected);
        assert_eq!(
            postcard::from_bytes::<FlatRule<String>>(&expected).unwrap(),
            rule
        );
    }
}
