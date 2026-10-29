//! Rule-local variable validation over the capability product.

use crate::error::CompileError;
use alloc::borrow::ToOwned;
use history_syntax::Component;
use vstd::prelude::*;

/// Three borrowed head-name slots; names are local to one rule.
#[verus_verify]
pub struct VariableScope<'a> {
    principal: Option<&'a str>,
    action: Option<&'a str>,
    resource: Option<&'a str>,
}

#[verus_verify]
impl<'a> Default for VariableScope<'a> {
    #[verus_spec(result => ensures result.name_spec(Component::Principal) is None,
        result.name_spec(Component::Action) is None, result.name_spec(Component::Resource) is None)]
    fn default() -> Self {
        Self::new()
    }
}

#[verus_verify]
impl<'a> VariableScope<'a> {
    /// Creates an empty rule scope.
    #[verus_spec(result => ensures result.name_spec(Component::Principal) is None,
        result.name_spec(Component::Action) is None, result.name_spec(Component::Resource) is None)]
    pub fn new() -> Self {
        proof! { reveal(VariableScope::name_spec); }
        Self {
            principal: None,
            action: None,
            resource: None,
        }
    }

    /// Returns the name bound in one coordinate.
    #[verus_spec(result => ensures result == self.name_spec(component))]
    pub fn name(&self, component: Component) -> Option<&'a str> {
        proof! { reveal(VariableScope::name_spec); }
        match component {
            Component::Principal => self.principal,
            Component::Action => self.action,
            Component::Resource => self.resource,
        }
    }

    /// Binds a head name, rejecting its use in any other coordinate.
    #[verus_spec(result => ensures
        result is Ok <==> !old(self).conflicts(component, name@),
        result is Err ==> *final(self) == *old(self),
        result is Ok ==> final(self).name_spec(component) == Some(name),
        forall|field: Component| field != component ==>
            final(self).name_spec(field) == old(self).name_spec(field),
        result matches Err(CompileError::VariableComponentConflict { name: bad }) ==> bad@ == name@,
        result is Err ==> result matches Err(CompileError::VariableComponentConflict { .. }),
    )]
    pub fn bind(&mut self, component: Component, name: &'a str) -> Result<(), CompileError> {
        proof! { reveal(VariableScope::name_spec); }
        if self.has_conflict(component, name) {
            return Err(CompileError::VariableComponentConflict {
                name: name.to_owned(),
            });
        }
        match component {
            Component::Principal => self.principal = Some(name),
            Component::Action => self.action = Some(name),
            Component::Resource => self.resource = Some(name),
        }
        Ok(())
    }

    /// Resolves a tail name only in its own coordinate.
    #[verus_spec(result => ensures
        result == Ok(component) <==> self.has_name(component, name@),
        result is Ok ==> result == Ok(component),
        result matches Err(CompileError::VariableComponentConflict { name: bad }) ==> bad@ == name@,
        result matches Err(CompileError::UnboundVariable { name: bad }) ==> bad@ == name@,
        result matches Err(CompileError::VariableComponentConflict { .. }) <==>
            !self.has_name(component, name@) && self.conflicts(component, name@),
        result matches Err(CompileError::UnboundVariable { .. }) <==>
            !self.has_name(component, name@) && !self.conflicts(component, name@),
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

    #[verus_spec(result => ensures result == self.conflicts(component, name@))]
    fn has_conflict(&self, component: Component, name: &str) -> bool {
        proof! { reveal(VariableScope::name_spec); }
        match component {
            Component::Principal => {
                Self::same_name(self.action, name) || Self::same_name(self.resource, name)
            }
            Component::Action => {
                Self::same_name(self.principal, name) || Self::same_name(self.resource, name)
            }
            Component::Resource => {
                Self::same_name(self.principal, name) || Self::same_name(self.action, name)
            }
        }
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
    pub closed spec fn name_spec(&self, component: Component) -> Option<&str> {
        match component {
            Component::Principal => self.principal,
            Component::Action => self.action,
            Component::Resource => self.resource,
        }
    }

    pub open spec fn has_name(&self, component: Component, name: Seq<char>) -> bool {
        match self.name_spec(component) { Some(bound) => bound@ == name, None => false }
    }

    pub open spec fn conflicts(&self, component: Component, name: Seq<char>) -> bool {
        match component {
            Component::Principal => self.has_name(Component::Action, name) || self.has_name(Component::Resource, name),
            Component::Action => self.has_name(Component::Principal, name) || self.has_name(Component::Resource, name),
            Component::Resource => self.has_name(Component::Principal, name) || self.has_name(Component::Action, name),
        }
    }
}
}
