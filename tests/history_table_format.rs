// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.
#![cfg(feature = "rvm")]

use history_syntax::{Component, RuleMode};
use junco_core::flat::{FlatHead, FlatPair, FlatRegex, FlatTerm, FlatTest};
use regorus::rvm::program::{DeserializationResult, Program};
use serde_json::{json, Value as Json};

// Captured before the shared-core cutover, not produced by these tests.
const BINARY: &[u8] = include_bytes!("fixtures/history_table_v8.bin");
const JSON: &str = include_str!("fixtures/history_table_v8.json");

fn binary_program(bytes: &[u8]) -> Program {
    match Program::deserialize_binary(bytes).unwrap() {
        DeserializationResult::Complete(program) => program,
        DeserializationResult::Partial(_) => panic!("version-8 fixture must decode completely"),
    }
}

fn fixture() -> Program {
    Program::deserialize_json(JSON).unwrap()
}

#[test]
fn pre_cutover_v8_fixtures_preserve_bytes_schema_and_topology() {
    assert_eq!(Program::SERIALIZATION_VERSION, 8);
    assert_eq!(BINARY.len(), 163);
    assert_eq!(JSON.len(), 2800);
    assert_eq!(&BINARY[4..8], &8u32.to_le_bytes());
    let expected = FlatPair {
        head: [
            FlatHead::Bind,
            FlatHead::Constant("release".to_owned()),
            FlatHead::Bind,
        ],
        tests: vec![
            FlatTest::Atom {
                field: Component::Principal,
                term: FlatTerm::Variable(Component::Principal),
                positive: true,
            },
            FlatTest::Atom {
                field: Component::Action,
                term: FlatTerm::Constant("edit".to_owned()),
                positive: true,
            },
            FlatTest::Atom {
                field: Component::Resource,
                term: FlatTerm::Variable(Component::Resource),
                positive: true,
            },
            FlatTest::And(vec![0, 1, 2]),
        ],
        regexes: vec![
            FlatRegex::All,
            FlatRegex::Test(3),
            FlatRegex::All,
            FlatRegex::Concat(vec![0, 1, 2]),
        ],
        root: 3,
    };
    for program in [binary_program(BINARY), fixture()] {
        assert_eq!(program.history_tables.len(), 1);
        assert_eq!(program.history_tables[0].rules.len(), 1);
        let rule = &program.history_tables[0].rules[0];
        assert_eq!(rule.mode, RuleMode::Require);
        assert_eq!(rule.source, expected);
        let step = &program.instruction_data.history_step_params[0];
        assert_eq!((step.table, step.rule, step.batch_size), (0, 0, 1));
        assert_eq!(program.serialize_binary().unwrap(), BINARY);
        assert_eq!(program.serialize_json().unwrap(), JSON);
        let schema: Json = serde_json::from_str(&program.serialize_json().unwrap()).unwrap();
        assert_eq!(
            schema["history_tables"][0]["rules"][0],
            json!({"mode": "Require", "source": {
                "head": ["Bind", {"Constant": "release"}, "Bind"],
                "tests": [
                    {"Atom": {"field": "Principal", "term": {"Variable": "Principal"}, "positive": true}},
                    {"Atom": {"field": "Action", "term": {"Constant": "edit"}, "positive": true}},
                    {"Atom": {"field": "Resource", "term": {"Variable": "Resource"}, "positive": true}},
                    {"And": [0, 1, 2]}
                ],
                "regexes": ["All", {"Test": 3}, "All", {"Concat": [0, 1, 2]}],
                "root": 3
            }})
        );
    }
}

// Replace only the postcard payload; preserve the fixture's real v8 header and sections.
// Program's public serializers deliberately refuse malformed sources.
fn unchecked_binary(program: &Program) -> Vec<u8> {
    let section_bytes: usize = (8..24)
        .step_by(4)
        .map(|offset| u32::from_le_bytes(BINARY[offset..offset + 4].try_into().unwrap()) as usize)
        .sum();
    let mut bytes = BINARY[..25 + section_bytes].to_vec();
    let payload = postcard::to_allocvec(program).unwrap();
    bytes.extend_from_slice(&u32::try_from(payload.len()).unwrap().to_le_bytes());
    bytes.extend_from_slice(&payload);
    bytes
}

fn unchecked_json(program: &Program) -> String {
    let mut document: Json = serde_json::from_str(JSON).unwrap();
    document["history_tables"] = serde_json::to_value(&program.history_tables).unwrap();
    document.to_string()
}

fn pair(tests: Vec<FlatTest<String>>, regexes: Vec<FlatRegex>, root: u32) -> FlatPair<String> {
    FlatPair {
        head: [FlatHead::Bind, FlatHead::Any, FlatHead::Bind],
        tests,
        regexes,
        root,
    }
}

#[test]
fn untrusted_artifacts_reject_invalid_sources_without_history_runtime() {
    let cases = [
        ("empty regex table", pair(vec![], vec![], 0)),
        (
            "root out of bounds",
            pair(vec![], vec![FlatRegex::Epsilon], 1),
        ),
        ("maximum root", pair(vec![], vec![FlatRegex::All], u32::MAX)),
        ("self reference", pair(vec![], vec![FlatRegex::Star(0)], 0)),
        (
            "forward reference",
            pair(vec![], vec![FlatRegex::Complement(1), FlatRegex::All], 0),
        ),
        (
            "cycle",
            pair(
                vec![],
                vec![FlatRegex::Union(vec![1]), FlatRegex::Concat(vec![0])],
                1,
            ),
        ),
        (
            "concat self reference",
            pair(vec![], vec![FlatRegex::Concat(vec![0])], 0),
        ),
        (
            "intersection forward reference",
            pair(
                vec![],
                vec![FlatRegex::Intersect(vec![1]), FlatRegex::All],
                1,
            ),
        ),
        ("missing test", pair(vec![], vec![FlatRegex::Test(0)], 0)),
        (
            "test out of bounds",
            pair(vec![FlatTest::Bool(true)], vec![FlatRegex::Test(1)], 0),
        ),
        (
            "test self reference",
            pair(vec![FlatTest::And(vec![0])], vec![FlatRegex::Test(0)], 0),
        ),
        (
            "test forward reference",
            pair(
                vec![FlatTest::Or(vec![1]), FlatTest::Bool(true)],
                vec![FlatRegex::Test(1)],
                0,
            ),
        ),
        (
            "test cycle",
            pair(
                vec![FlatTest::And(vec![1]), FlatTest::Or(vec![0])],
                vec![FlatRegex::Test(1)],
                0,
            ),
        ),
        (
            "wrong coordinate",
            pair(
                vec![FlatTest::Atom {
                    field: Component::Principal,
                    term: FlatTerm::Variable(Component::Resource),
                    positive: true,
                }],
                vec![FlatRegex::Test(0)],
                0,
            ),
        ),
        (
            "unbound wildcard head",
            pair(
                vec![FlatTest::Atom {
                    field: Component::Action,
                    term: FlatTerm::Variable(Component::Action),
                    positive: false,
                }],
                vec![FlatRegex::Test(0)],
                0,
            ),
        ),
        (
            "invalid unreachable regex",
            pair(vec![], vec![FlatRegex::Epsilon, FlatRegex::Star(1)], 0),
        ),
        (
            "invalid unused test",
            pair(vec![FlatTest::And(vec![0])], vec![FlatRegex::Epsilon], 0),
        ),
    ];
    let mut invalid = cases.to_vec();
    let mut constant_head = pair(
        vec![FlatTest::Atom {
            field: Component::Principal,
            term: FlatTerm::Variable(Component::Principal),
            positive: true,
        }],
        vec![FlatRegex::Test(0)],
        0,
    );
    constant_head.head[0] = FlatHead::Constant("alice".to_owned());
    invalid.push(("unbound constant head", constant_head));
    for (name, source) in invalid {
        let mut program = fixture();
        program.history_tables[0].rules[0].source = source;
        assert!(program.validate_limits().is_err(), "{name}");
        assert!(program.serialize_json().is_err(), "{name}");
        assert!(program.serialize_binary().is_err(), "{name}");
        assert!(
            Program::deserialize_json(&unchecked_json(&program)).is_err(),
            "{name}"
        );
        assert!(
            Program::deserialize_binary(&unchecked_binary(&program)).is_err(),
            "{name}"
        );
    }
}

#[test]
fn valid_shared_dags_empty_operators_and_non_last_roots_roundtrip_unchanged() {
    let source = pair(
        vec![
            FlatTest::Bool(false),
            FlatTest::And(vec![]),
            FlatTest::Or(vec![]),
            FlatTest::And(vec![0, 0]),
            FlatTest::Or(vec![1, 2, 1]),
        ],
        vec![
            FlatRegex::Epsilon,
            FlatRegex::Empty,
            FlatRegex::All,
            FlatRegex::Concat(vec![]),
            FlatRegex::Union(vec![]),
            FlatRegex::Intersect(vec![]),
            FlatRegex::Test(3),
            FlatRegex::Test(4),
            FlatRegex::Concat(vec![0, 0]),
            FlatRegex::Union(vec![8, 8]),
            FlatRegex::Intersect(vec![9, 9]),
            FlatRegex::Star(10),
            FlatRegex::Complement(11),
        ],
        0,
    );
    let mut sources = vec![pair(vec![], vec![FlatRegex::Epsilon], 0)];
    for root in 0..source.regexes.len() {
        let mut rooted = source.clone();
        rooted.root = u32::try_from(root).unwrap();
        sources.push(rooted);
    }
    for source in sources {
        let mut program = fixture();
        program.history_tables[0].rules[0].mode = RuleMode::Forbid;
        program.history_tables[0].rules[0].source = source.clone();
        program.validate_limits().unwrap();
        let binary = program.serialize_binary().unwrap();
        let json = program.serialize_json().unwrap();
        for restored in [
            binary_program(&binary),
            Program::deserialize_json(&json).unwrap(),
        ] {
            assert_eq!(restored.history_tables[0].rules[0].source, source);
            assert_eq!(restored.history_tables[0].rules[0].mode, RuleMode::Forbid);
            assert_eq!(restored.serialize_binary().unwrap(), binary);
            assert_eq!(restored.serialize_json().unwrap(), json);
        }
    }
}

#[test]
fn canonical_enum_discriminants_and_atom_fields_keep_v8_order() {
    for (index, head) in [FlatHead::Any, FlatHead::Constant("x"), FlatHead::Bind]
        .iter()
        .enumerate()
    {
        assert_eq!(
            postcard::to_allocvec(head).unwrap()[0],
            u8::try_from(index).unwrap()
        );
    }
    for (index, term) in [
        FlatTerm::Constant("x"),
        FlatTerm::Variable(Component::Principal),
    ]
    .iter()
    .enumerate()
    {
        assert_eq!(
            postcard::to_allocvec(term).unwrap()[0],
            u8::try_from(index).unwrap()
        );
    }
    for (index, component) in [Component::Principal, Component::Action, Component::Resource]
        .iter()
        .enumerate()
    {
        assert_eq!(
            postcard::to_allocvec(component).unwrap(),
            [u8::try_from(index).unwrap()]
        );
    }
    assert_eq!(postcard::to_allocvec(&RuleMode::Require).unwrap(), [0]);
    assert_eq!(postcard::to_allocvec(&RuleMode::Forbid).unwrap(), [1]);
    let atom = FlatTest::Atom {
        field: Component::Resource,
        term: FlatTerm::<String>::Variable(Component::Resource),
        positive: true,
    };
    // Atom discriminant, field, term discriminant, variable coordinate, polarity.
    assert_eq!(postcard::to_allocvec(&atom).unwrap(), [1, 2, 1, 2, 1]);
    for (index, test) in [
        FlatTest::Bool(false),
        atom,
        FlatTest::And(vec![]),
        FlatTest::Or(vec![]),
    ]
    .iter()
    .enumerate()
    {
        assert_eq!(
            postcard::to_allocvec(test).unwrap()[0],
            u8::try_from(index).unwrap()
        );
    }
    for (index, regex) in [
        FlatRegex::Empty,
        FlatRegex::All,
        FlatRegex::Epsilon,
        FlatRegex::Test(0),
        FlatRegex::Concat(vec![]),
        FlatRegex::Union(vec![]),
        FlatRegex::Intersect(vec![]),
        FlatRegex::Star(0),
        FlatRegex::Complement(0),
    ]
    .iter()
    .enumerate()
    {
        assert_eq!(
            postcard::to_allocvec(regex).unwrap()[0],
            u8::try_from(index).unwrap()
        );
    }
}
