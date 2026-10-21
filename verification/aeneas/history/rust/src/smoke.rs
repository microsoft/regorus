// Copyright (c) Microsoft Corporation. All rights reserved.
// Licensed under the MIT License.
use crate::kernel::*;
use crate::store::VecStore;
use crate::{normalize, symbolic};
use alloc::vec;
use alloc::vec::Vec;

pub(crate) fn extraction_smoke() -> KernelResult<bool> {
    let mut backend = VecStore::new()?;
    let presence = backend.intern_test(TestView::Atom {
        primitive: Primitive::HasValue(PathId(0)),
        positive: true,
    })?;
    let equality = backend.intern_test(TestView::Atom {
        primitive: Primitive::EqCore(PathId(0), Term::Constant(ConstId(0))),
        positive: true,
    })?;
    let guarded = normalize::test_and(&mut backend, &[presence, equality])?;
    let atoms = atom_set(&mut backend, vec![presence, equality])?;
    let regex = normalize::regex_test(&mut backend, guarded)?;
    let transition = symbolic::symbolic_derivative(&mut backend, &mut Vec::new(), regex)?;
    let present = symbolic::interpret_transition(&mut backend, transition, &atoms, &[0b11])?;
    let missing = symbolic::interpret_transition(&mut backend, transition, &atoms, &[0b00])?;
    let complement = normalize::regex_not(&mut backend, regex)?;
    Ok(normalize::nullable(&backend, present)?
        && !normalize::nullable(&backend, missing)?
        && normalize::nullable(&backend, complement)?)
}
