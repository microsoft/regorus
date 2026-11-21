//! Portable, store-independent source tables and their checked construction boundary.

use crate::errors::HistoryError;
use crate::limits::Limits;
use crate::observation::ObservationWorld;
use alloc::string::String;
use alloc::vec::Vec;
use history_syntax::{
    MAX_ARITY,
    syntax::{Component, RuleMode},
};

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatHead<C> {
    Any,
    Constant(C),
    Bind,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatTerm<C> {
    Constant(C),
    Variable(Component),
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatTest<C> {
    Bool(bool),
    Atom {
        field: Component,
        term: FlatTerm<C>,
        positive: bool,
    },
    And(Vec<u32>),
    Or(Vec<u32>),
}

// Variant order and names are the version-7 portable wire format.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FlatRegex {
    Empty,
    All,
    Epsilon,
    Test(u32),
    Concat(Vec<u32>),
    Union(Vec<u32>),
    Intersect(Vec<u32>),
    Star(u32),
    Complement(u32),
}

/// References are backward within their own table; the root need not be last.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatPair<C> {
    pub head: Vec<FlatHead<C>>,
    pub tests: Vec<FlatTest<C>>,
    pub regexes: Vec<FlatRegex>,
    pub root: u32,
}

#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatRule<C> {
    pub mode: RuleMode,
    pub source: FlatPair<C>,
}

fn references_before(children: &[u32], bound: usize) -> bool {
    let mut index = 0;
    while index < children.len() {
        let child = children[index];
        let child = match usize::try_from(child) {
            Ok(child) => child,
            Err(_) => return false,
        };
        if child >= bound {
            return false;
        }
        index += 1;
    }
    true
}

fn test_valid<C>(head: &[FlatHead<C>], test: &FlatTest<C>, index: usize) -> bool {
    match test {
        FlatTest::Bool(_) => true,
        FlatTest::Atom {
            field,
            term: FlatTerm::Variable(variable),
            ..
        } => {
            if field != variable {
                return false;
            }
            matches!(head.get(field.index()), Some(&FlatHead::Bind))
        }
        FlatTest::Atom { field, .. } => field.index() < head.len(),
        FlatTest::And(children) | FlatTest::Or(children) => references_before(children, index),
    }
}

fn regex_valid(regex: &FlatRegex, index: usize, tests: usize) -> bool {
    match regex {
        FlatRegex::Empty | FlatRegex::All | FlatRegex::Epsilon => true,
        FlatRegex::Test(test) => match usize::try_from(*test) {
            Ok(test) => test < tests,
            Err(_) => false,
        },
        FlatRegex::Concat(children)
        | FlatRegex::Union(children)
        | FlatRegex::Intersect(children) => references_before(children, index),
        FlatRegex::Star(child) | FlatRegex::Complement(child) => match usize::try_from(*child) {
            Ok(child) => child < index,
            Err(_) => false,
        },
    }
}

impl<C> FlatPair<C> {
    /// Validate even when no evaluator or runtime feature is enabled.
    pub fn validate(&self) -> Result<(), String> {
        if self.head.is_empty() || self.head.len() > MAX_ARITY {
            return Err(String::from(
                "history head arity is outside the supported range",
            ));
        }
        let mut index = 0;
        while index < self.tests.len() {
            let test = &self.tests[index];
            if !test_valid(&self.head, test, index) {
                return Err(String::from(match test {
                    FlatTest::Atom { .. } => "history variable must bind its own head domain",
                    _ => "history test reference must point to an earlier node",
                }));
            }
            index += 1;
        }
        index = 0;
        while index < self.regexes.len() {
            let regex = &self.regexes[index];
            if !regex_valid(regex, index, self.tests.len()) {
                return Err(String::from(match regex {
                    FlatRegex::Test(_) => "history regex test reference is out of bounds",
                    _ => "history regex reference must point to an earlier node",
                }));
            }
            index += 1;
        }
        let root = match usize::try_from(self.root) {
            Ok(root) => root,
            Err(_) => return Err(String::from("history regex root is out of bounds")),
        };
        if root >= self.regexes.len() {
            return Err(String::from("history regex root is out of bounds"));
        }
        Ok(())
    }
}

/// Checked, topology-preserving construction shared by both source frontends.
pub struct FlatBuilder<C> {
    head: Vec<FlatHead<C>>,
    tests: Vec<FlatTest<C>>,
    regexes: Vec<FlatRegex>,
}

fn invalid_source() -> HistoryError {
    HistoryError::InvalidPolicy {
        path: String::from("$"),
        message: "invalid portable history source",
    }
}

impl<C> FlatBuilder<C> {
    pub fn new(head: Vec<FlatHead<C>>) -> Self {
        Self {
            head,
            tests: Vec::new(),
            regexes: Vec::new(),
        }
    }

    pub fn head(&self) -> &[FlatHead<C>] {
        &self.head
    }

    pub fn tests(&self) -> &Vec<FlatTest<C>> {
        &self.tests
    }

    pub fn regexes(&self) -> &Vec<FlatRegex> {
        &self.regexes
    }

    pub fn test<L: Limits>(
        &mut self,
        node: FlatTest<C>,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<u32, HistoryError> {
        limits.checkpoint()?;
        if !test_valid(&self.head, &node, self.tests.len()) {
            return Err(invalid_source());
        }
        let id = match u32::try_from(self.tests.len()) {
            Ok(id) => id,
            Err(_) => return Err(HistoryError::graph_index_overflow()),
        };
        if world.try_reserve_vec(&mut self.tests, 1).is_err() {
            return Err(HistoryError::AllocationFailed);
        }
        limits.enforce_memory()?;
        self.tests.push(node);
        Ok(id)
    }

    pub fn regex<L: Limits>(
        &mut self,
        node: FlatRegex,
        limits: &mut L,
        world: &mut ObservationWorld,
    ) -> Result<u32, HistoryError> {
        limits.checkpoint()?;
        if !regex_valid(&node, self.regexes.len(), self.tests.len()) {
            return Err(invalid_source());
        }
        let id = match u32::try_from(self.regexes.len()) {
            Ok(id) => id,
            Err(_) => return Err(HistoryError::graph_index_overflow()),
        };
        if world.try_reserve_vec(&mut self.regexes, 1).is_err() {
            return Err(HistoryError::AllocationFailed);
        }
        limits.enforce_memory()?;
        self.regexes.push(node);
        Ok(id)
    }

    pub fn finish(self, root: u32) -> Result<FlatPair<C>, HistoryError> {
        let pair = FlatPair {
            head: self.head,
            tests: self.tests,
            regexes: self.regexes,
            root,
        };
        if pair.validate().is_err() {
            return Err(invalid_source());
        }
        Ok(pair)
    }
}
