//! Rule-local variable validation over indexed event coordinates.

use crate::errors::CompileError;
#[cfg(verus_keep_ghost)]
use crate::verify::history_specs::no_invariant_compile_failure;
use alloc::borrow::ToOwned;
use history_syntax::{Component, MAX_ARITY};
use vstd::prelude::*;

/// Borrowed head-name slots; names are local to one rule.
#[verus_verify]
pub struct VariableScope<'a> {
    names: [Option<&'a str>; MAX_ARITY],
    arity: usize,
}

#[verus_verify]
impl<'a> VariableScope<'a> {
    /// Creates an empty rule scope of the event type's arity.
    #[verus_spec(result => requires 1 <= arity <= MAX_ARITY,
        ensures result.wf(), result.arity_spec() == arity,
            forall|field: Component| result.name_spec(field) is None)]
    pub fn new(arity: usize) -> Self {
        proof! { reveal(VariableScope::name_spec); reveal(VariableScope::arity_spec); reveal(VariableScope::wf); }
        Self {
            names: [None; MAX_ARITY],
            arity,
        }
    }

    /// Number of coordinates in this scope.
    #[verus_spec(result => ensures result == self.arity_spec())]
    pub fn arity(&self) -> usize {
        proof! { reveal(VariableScope::arity_spec); }
        self.arity
    }

    /// Returns the name bound in one coordinate, or `None` outside the scope.
    #[verus_spec(result => requires self.wf(), ensures result == self.name_spec(component))]
    pub fn name(&self, component: Component) -> Option<&'a str> {
        proof! { reveal(VariableScope::name_spec); reveal(VariableScope::wf); }
        let index = component.index();
        if index < self.arity {
            self.names[index]
        } else {
            None
        }
    }

    /// Binds a head name, rejecting its use in any other coordinate.
    #[verus_spec(result => requires old(self).wf(), component.0 < old(self).arity_spec(),
        ensures final(self).wf(), final(self).arity_spec() == old(self).arity_spec(),
        result is Ok <==> !old(self).conflicts(component, name@),
        result is Err ==> *final(self) == *old(self),
        result is Ok ==> final(self).name_spec(component) == Some(name),
        forall|field: Component| field != component ==>
            final(self).name_spec(field) == old(self).name_spec(field),
        result matches Err(CompileError::VariableComponentConflict { name: bad }) ==> bad@ == name@,
        result is Err ==> result matches Err(CompileError::VariableComponentConflict { .. }),
        no_invariant_compile_failure(result),
    )]
    pub fn bind(&mut self, component: Component, name: &'a str) -> Result<(), CompileError> {
        proof! { reveal(VariableScope::name_spec); reveal(VariableScope::arity_spec); reveal(VariableScope::wf); }
        if self.has_conflict(component, name) {
            return Err(CompileError::VariableComponentConflict {
                name: name.to_owned(),
            });
        }
        self.names[component.index()] = Some(name);
        Ok(())
    }

    /// Resolves a tail name only in its own coordinate.
    #[verus_spec(result => requires self.wf(), component.0 < self.arity_spec(),
        ensures result == Ok(component) <==> self.has_name(component, name@),
        result is Ok ==> result == Ok(component),
        result matches Err(CompileError::VariableComponentConflict { name: bad }) ==> bad@ == name@,
        result matches Err(CompileError::UnboundVariable { name: bad }) ==> bad@ == name@,
        result matches Err(CompileError::VariableComponentConflict { .. }) <==>
            !self.has_name(component, name@) && self.conflicts(component, name@),
        result matches Err(CompileError::UnboundVariable { .. }) <==>
            !self.has_name(component, name@) && !self.conflicts(component, name@),
        no_invariant_compile_failure(result),
        result is Err ==> result matches Err(CompileError::VariableComponentConflict { .. })
            || result matches Err(CompileError::UnboundVariable { .. }),
    )]
    pub fn resolve(&self, component: Component, name: &str) -> Result<Component, CompileError> {
        if Self::same_name(self.name(component), name) {
            Ok(component)
        } else if self.has_conflict(component, name) {
            Err(CompileError::VariableComponentConflict {
                name: name.to_owned(),
            })
        } else {
            Err(CompileError::UnboundVariable {
                name: name.to_owned(),
            })
        }
    }

    #[verus_spec(result => requires self.wf(), ensures result == self.conflicts(component, name@))]
    fn has_conflict(&self, component: Component, name: &str) -> bool {
        proof! { reveal(VariableScope::name_spec); reveal(VariableScope::arity_spec); reveal(VariableScope::wf); }
        let mut index = 0;
        #[cfg_attr(verus_keep_ghost, verus_spec(
            invariant self.wf(), index <= self.arity <= MAX_ARITY,
                forall|i: int| 0 <= i < index && i != component.0 ==>
                    !#[trigger] self.has_name(Component(i as u8), name@),
            decreases self.arity - index,
        ))]
        while index < self.arity {
            if index != component.index() && Self::same_name(self.names[index], name) {
                proof! { assert(self.has_name(Component(index as u8), name@)); }
                return true;
            }
            index += 1;
        }
        false
    }

    #[verus_spec(result => ensures result == match bound {
        Some(existing) => existing@ == name@, None => false,
    })]
    fn same_name(bound: Option<&str>, name: &str) -> bool {
        match bound {
            Some(existing) => existing == name,
            None => false,
        }
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl VariableScope<'_> {
    pub closed spec fn arity_spec(&self) -> nat { self.arity as nat }
    pub closed spec fn wf(&self) -> bool { 1 <= self.arity <= MAX_ARITY }

    pub closed spec fn name_spec(&self, component: Component) -> Option<&str> {
        if component.0 < self.arity { self.names@[component.0 as int] } else { None }
    }

    pub open spec fn has_name(&self, component: Component, name: Seq<char>) -> bool {
        match self.name_spec(component) { Some(bound) => bound@ == name, None => false }
    }

    pub open spec fn conflicts(&self, component: Component, name: Seq<char>) -> bool {
        exists|i: int| 0 <= i < self.arity_spec() && i != component.0
            && #[trigger] self.has_name(Component(i as u8), name)
    }
}
}
