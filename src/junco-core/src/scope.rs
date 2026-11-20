//! Rule-local variable validation over indexed event coordinates.

use crate::errors::CompileError;
use alloc::borrow::ToOwned;
use history_syntax::{Component, MAX_ARITY};

/// Borrowed head-name slots; names are local to one rule.
pub struct VariableScope<'a> {
    names: [Option<&'a str>; MAX_ARITY],
    arity: usize,
}

impl<'a> VariableScope<'a> {
    /// Creates an empty rule scope of the event type's arity.
    pub fn new(arity: usize) -> Self {
        Self {
            names: [None; MAX_ARITY],
            arity,
        }
    }

    /// Number of coordinates in this scope.
    pub fn arity(&self) -> usize {
        self.arity
    }

    /// Returns the name bound in one coordinate, or `None` outside the scope.
    pub fn name(&self, component: Component) -> Option<&'a str> {
        let index = component.index();
        if index < self.arity {
            self.names[index]
        } else {
            None
        }
    }

    /// Binds a head name, rejecting its use in any other coordinate.
    pub fn bind(&mut self, component: Component, name: &'a str) -> Result<(), CompileError> {
        if self.has_conflict(component, name) {
            return Err(CompileError::VariableComponentConflict {
                name: name.to_owned(),
            });
        }
        self.names[component.index()] = Some(name);
        Ok(())
    }

    /// Resolves a tail name only in its own coordinate.
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

    fn has_conflict(&self, component: Component, name: &str) -> bool {
        let mut index = 0;
        while index < self.arity {
            if index != component.index() && Self::same_name(self.names[index], name) {
                return true;
            }
            index += 1;
        }
        false
    }

    fn same_name(bound: Option<&str>, name: &str) -> bool {
        match bound {
            Some(existing) => existing == name,
            None => false,
        }
    }
}
