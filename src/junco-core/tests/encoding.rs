use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use history_syntax::{Component, Component3, Event, N3};
use junco_core::HistoryError;
use junco_core::compile::{FlatEncoder, lower_flat, validate_component};
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use junco_core::limits::{LimitError, Limits, Unmetered};
use junco_core::observation::ObservationWorld;

// Deliberately neither Copy nor Clone: lowering must borrow stored constants.
#[derive(Debug)]
struct Value {
    identity: u8,
    payload: u8,
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}
impl Eq for Value {}
impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        0u8.hash(state);
    }
}

fn value(identity: u8, payload: u8) -> Value {
    Value { identity, payload }
}

// A deterministic test fixture, not a production codebook implementation.
#[derive(Default)]
struct Encoder {
    maps: [HashMap<Value, u64>; 3],
    calls: Vec<(Component, u8, u8)>,
    fail_at: Option<usize>,
}

impl FlatEncoder<Value> for Encoder {
    fn encode(&mut self, field: Component, value: &Value) -> Result<u64, HistoryError> {
        self.calls.push((field, value.identity, value.payload));
        if self.fail_at == Some(self.calls.len()) {
            return Err(HistoryError::AllocationFailed);
        }
        let map = &mut self.maps[field.index()];
        if let Some(id) = map.get(value) {
            return Ok(*id);
        }
        // Disjoint numeric ranges make an accidental coordinate mix-up observable.
        let id = (field.index() as u64 + 1) * 100 + map.len() as u64 + 1;
        map.insert(
            Value {
                identity: value.identity,
                payload: value.payload,
            },
            id,
        );
        Ok(id)
    }
}

#[test]
fn custom_encoder_may_report_structural_errors() {
    struct CustomEncoder;
    impl FlatEncoder<Value> for CustomEncoder {
        fn encode(&mut self, _: Component, _: &Value) -> Result<u64, HistoryError> {
            Err(HistoryError::invariant("custom encoder failure"))
        }
    }
    assert_eq!(
        lower_flat(
            &source(),
            &mut CustomEncoder,
            &mut Unmetered,
            &mut ObservationWorld
        ),
        Err(HistoryError::invariant("custom encoder failure")),
    );
}

fn source() -> FlatPair<Value> {
    FlatPair {
        head: vec![
            FlatHead::Constant(value(7, 1)),
            FlatHead::Constant(value(7, 11)),
            FlatHead::Bind,
        ],
        tests: vec![
            FlatTest::Atom {
                field: Component(0),
                term: FlatTerm::Constant(value(7, 2)),
                positive: true,
            },
            FlatTest::Atom {
                field: Component(0),
                term: FlatTerm::Constant(value(8, 3)),
                positive: false,
            },
            FlatTest::Atom {
                field: Component(1),
                term: FlatTerm::Constant(value(7, 12)),
                positive: true,
            },
            FlatTest::Atom {
                field: Component(2),
                term: FlatTerm::Variable(Component(2)),
                positive: false,
            },
            FlatTest::And(vec![0, 0, 1]),
            FlatTest::Or(vec![]),
            // Unreachable stored constants still pass through the single encoding pass.
            FlatTest::Atom {
                field: Component(2),
                term: FlatTerm::Constant(value(7, 21)),
                positive: true,
            },
        ],
        regexes: vec![
            FlatRegex::Epsilon,
            FlatRegex::Test(4),
            FlatRegex::Concat(vec![0, 0]),
            FlatRegex::Complement(2),
            FlatRegex::Star(3),
            FlatRegex::Union(vec![1, 4, 1]),
            FlatRegex::Intersect(vec![]),
        ],
        root: 5,
    }
}

#[test]
fn one_pass_preserves_equality_domains_and_exact_topology() {
    let source = source();
    let mut encoder = Encoder::default();
    let numeric = lower_flat(&source, &mut encoder, &mut Unmetered, &mut ObservationWorld).unwrap();
    assert_eq!(
        numeric.head,
        vec![
            FlatHead::Constant(101),
            FlatHead::Constant(201),
            FlatHead::Bind
        ]
    );
    assert_eq!(
        numeric.tests,
        vec![
            FlatTest::Atom {
                field: Component(0),
                term: FlatTerm::Constant(101),
                positive: true
            },
            FlatTest::Atom {
                field: Component(0),
                term: FlatTerm::Constant(102),
                positive: false
            },
            FlatTest::Atom {
                field: Component(1),
                term: FlatTerm::Constant(201),
                positive: true
            },
            FlatTest::Atom {
                field: Component(2),
                term: FlatTerm::Variable(Component(2)),
                positive: false
            },
            FlatTest::And(vec![0, 0, 1]),
            FlatTest::Or(vec![]),
            FlatTest::Atom {
                field: Component(2),
                term: FlatTerm::Constant(301),
                positive: true
            },
        ]
    );
    assert_eq!(numeric.regexes, source.regexes);
    assert_eq!(numeric.root, 5);
    assert_eq!(
        encoder.calls,
        vec![
            (Component(0), 7, 1),
            (Component(1), 7, 11),
            (Component(0), 7, 2),
            (Component(0), 8, 3),
            (Component(1), 7, 12),
            (Component(2), 7, 21),
        ]
    );
    assert_eq!(encoder.maps[0].len(), 2);
    assert_eq!(encoder.maps[1].len(), 1);
    assert_eq!(encoder.maps[2].len(), 1);
    match &source.head[0] {
        FlatHead::Constant(value) => assert_eq!(value.payload, 1),
        _ => panic!("source head changed"),
    }
}

#[test]
fn every_structural_failure_precedes_interning() {
    for invalid in 0..6 {
        let mut source = source();
        match invalid {
            0 => source.tests[0] = FlatTest::And(vec![0]),
            1 => source.regexes[0] = FlatRegex::Star(1),
            2 => source.regexes[0] = FlatRegex::Test(99),
            3 => source.root = 99,
            4 => {
                source.tests[0] = FlatTest::Atom {
                    field: Component(0),
                    term: FlatTerm::Variable(Component(2)),
                    positive: true,
                }
            }
            _ => {
                source.tests[0] = FlatTest::Atom {
                    field: Component(0),
                    term: FlatTerm::Variable(Component(0)),
                    positive: true,
                }
            }
        }
        let mut encoder = Encoder::default();
        assert_eq!(
            lower_flat(&source, &mut encoder, &mut Unmetered, &mut ObservationWorld),
            Err(HistoryError::InvalidPolicy {
                path: "$".into(),
                message: "invalid portable history source"
            })
        );
        assert!(encoder.calls.is_empty());
        assert!(encoder.maps.iter().all(HashMap::is_empty));
    }
}

#[test]
fn failure_keeps_old_associations_and_later_values_do_not_renumber_constants() {
    let mut encoder = Encoder::default();
    assert_eq!(encoder.encode(Component(0), &value(42, 0)), Ok(101));
    encoder.fail_at = Some(3);
    assert_eq!(
        lower_flat(
            &source(),
            &mut encoder,
            &mut Unmetered,
            &mut ObservationWorld
        ),
        Err(HistoryError::AllocationFailed)
    );
    assert_eq!(encoder.maps[0].get(&value(42, 99)), Some(&101));
    assert_eq!(encoder.maps[0].get(&value(7, 99)), Some(&102));
    encoder.fail_at = None;
    let numeric = lower_flat(
        &source(),
        &mut encoder,
        &mut Unmetered,
        &mut ObservationWorld,
    )
    .unwrap();
    let compiled = numeric.head[0].clone();
    assert_eq!(encoder.encode(Component(0), &value(99, 0)), Ok(104));
    assert_eq!(encoder.encode(Component(0), &value(7, 255)), Ok(102));
    assert_eq!(numeric.head[0], compiled);
}

struct RejectMemory;
impl Limits for RejectMemory {
    fn checkpoint(&mut self) -> Result<(), LimitError> {
        Ok(())
    }
    fn publication_checkpoint(&mut self) -> Result<(), LimitError> {
        Ok(())
    }
    fn enforce_memory(&mut self) -> Result<(), LimitError> {
        Err(LimitError::MemoryLimitExceeded { usage: 2, limit: 1 })
    }
}

#[test]
fn builder_limit_errors_remain_errors_and_keep_existing_encodings() {
    let mut encoder = Encoder::default();
    assert_eq!(encoder.encode(Component(0), &value(7, 0)), Ok(101));
    let error = lower_flat(
        &source(),
        &mut encoder,
        &mut RejectMemory,
        &mut ObservationWorld,
    )
    .unwrap_err();
    assert_eq!(
        error,
        HistoryError::Limit(LimitError::MemoryLimitExceeded { usage: 2, limit: 1 })
    );
    assert_eq!(encoder.maps[0].get(&value(7, 255)), Some(&101));
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
struct Product;
impl Event for Product {
    type Component = Component3<u8, u8, u8>;
    type Arity = N3;
    fn component(self, index: usize) -> Self::Component {
        match index {
            0 => Component3::C0(1),
            1 => Component3::C1(2),
            _ => Component3::C2(3),
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

#[test]
fn typed_constants_reject_every_mismatched_coordinate() {
    let values = [
        Component3::<u8, u8, u8>::C0(7),
        Component3::C1(7),
        Component3::C2(7),
    ];
    for (field_index, field) in [Component(0), Component(1), Component(2)]
        .into_iter()
        .enumerate()
    {
        for (value_index, value) in values.iter().enumerate() {
            if field_index == value_index {
                assert_eq!(validate_component::<Product>(field, value), Ok(()));
            } else {
                assert_eq!(
                    validate_component::<Product>(field, value),
                    Err(HistoryError::InvalidPolicy {
                        path: "$".into(),
                        message: "constant belongs to another component",
                    })
                );
            }
        }
    }
}
