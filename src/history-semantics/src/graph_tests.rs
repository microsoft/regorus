// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
#![allow(clippy::panic_in_result_fn)]
use crate::normalize::RegexNormalize;
use crate::progress::TransitionAtoms;
use crate::symbolic::{RegexDerivative, TransitionInterpret};
use alloc::vec::Vec;
use history_store::graph::{ArenaStorage, CanonicalStore, RuntimeKernel};
use junco_core::kernel::*;
use junco_core::observation::ObservationWorld;
#[test]
fn interned_nodes_keep_ids_bytes_and_derivative_semantics() -> KernelResult<()> {
    let mut world = ObservationWorld;
    let mut limits = junco_core::limits::Unmetered;
    let mut graph = CanonicalStore::new(ArenaStorage::new()?, &mut world)?;
    let mut store = RuntimeKernel {
        store: &mut graph,
        limits: &mut limits,
        world: &mut world,
    };
    let node = TestView::Atom {
        primitive: Primitive::Eq {
            field: history_syntax::syntax::Component::Principal,
            term: Term::Constant(0),
        },
        positive: true,
    };
    let test = store.intern_test(node)?;
    let regex = store.intern_regex(RegexKindView::Test(test), false)?;
    let transition_node = TransitionView::If {
        test,
        then_transition: store.constants().transition_epsilon,
        else_transition: store.constants().transition_empty,
    };
    let transition = store.intern_transition(transition_node)?;
    let and = store.intern_test(TestView::And(&[test, store.constants().test_true]))?;
    let lists = store.store.table_counts().map(|counts| counts.0);
    let or = store.intern_test(TestView::Or(&[test, store.constants().test_true]))?;
    assert_ne!(and, or);
    assert_eq!(store.store.table_counts().map(|counts| counts.0), lists);
    assert_eq!(
        store.test(or)?,
        TestView::Or(&[test, store.constants().test_true])
    );
    let bytes = store.store.charged_bytes();
    let rows = store.store.table_counts().map(|counts| counts.1);
    assert_eq!(store.intern_test(node)?, test);
    assert_eq!(store.intern_regex(RegexKindView::Test(test), false)?, regex);
    assert_eq!(store.intern_transition(transition_node)?, transition);
    assert_eq!(
        store.intern_test(TestView::And(&[test, store.constants().test_true]),)?,
        and
    );
    assert_eq!(store.store.charged_bytes(), bytes);
    assert_eq!(store.store.table_counts().map(|counts| counts.1), rows);
    let mut kernel = store;
    let mut derivatives = Vec::new();
    assert_eq!(
        RegexId::derivative(regex, &mut kernel, &mut derivatives)?,
        transition
    );
    let atoms = AtomSet::from_transition(&mut kernel, transition)?;
    let accepted = TransitionId::interpret(transition, &mut kernel, &atoms, &[1])?;
    assert!(RegexId::nullable(accepted, &kernel)?);
    Ok(())
}
