// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::{String, ToString as _};
use alloc::vec::Vec;
use serde::{Deserialize, Serialize};
use vstd::prelude::*;

/// The three independent identity domains of a history event.
#[verus_verify]
#[verus_verify(external_derive)]
#[cfg_attr(verus_keep_ghost, derive(Structural))]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash, Serialize, Deserialize)]
pub enum HistoryField {
    Principal,
    Action,
    Resource,
}

impl HistoryField {
    #[verus_verify]
    #[verus_spec(result => ensures result == match self {
        Self::Principal => 0usize, Self::Action => 1usize, Self::Resource => 2usize,
    })]
    pub(crate) const fn index(self) -> usize {
        match self {
            Self::Principal => 0,
            Self::Action => 1,
            Self::Resource => 2,
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum HistoryHeadSource {
    Any,
    Constant(String),
    Bind,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum HistoryTermSource {
    Constant(String),
    Variable(HistoryField),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum HistoryTestSource {
    Bool(bool),
    Atom {
        field: HistoryField,
        term: HistoryTermSource,
        positive: bool,
    },
    And(Vec<u32>),
    Or(Vec<u32>),
}

#[verus_verify]
#[verus_verify(external_derive)]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum HistoryRegexSource {
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

/// Portable cold policy source. No store identity or interned ID is serialized.
/// Same-table references are strictly backward, so decoding and drop are flat.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HistoryPairSource {
    pub head: [HistoryHeadSource; 3],
    pub tests: Vec<HistoryTestSource>,
    pub regexes: Vec<HistoryRegexSource>,
    pub root: u32,
}

impl HistoryPairSource {
    /// Validate even when the history execution feature is disabled.
    pub fn validate(&self) -> Result<(), String> {
        for (index, test) in self.tests.iter().enumerate() {
            match *test {
                HistoryTestSource::Bool(_) => {}
                HistoryTestSource::Atom {
                    field,
                    term: HistoryTermSource::Variable(variable),
                    ..
                } => {
                    if field != variable
                        || !matches!(self.head.get(field.index()), Some(&HistoryHeadSource::Bind))
                    {
                        return Err("history variable must bind its own head domain".to_string());
                    }
                }
                HistoryTestSource::Atom { .. } => {}
                HistoryTestSource::And(ref children) | HistoryTestSource::Or(ref children) => {
                    if children
                        .iter()
                        .any(|child| usize::try_from(*child).map_or(true, |child| child >= index))
                    {
                        return Err(
                            "history test reference must point to an earlier node".to_string()
                        );
                    }
                }
            }
        }
        for (index, regex) in self.regexes.iter().enumerate() {
            match *regex {
                HistoryRegexSource::Empty
                | HistoryRegexSource::All
                | HistoryRegexSource::Epsilon => {}
                HistoryRegexSource::Test(test) => {
                    if usize::try_from(test).map_or(true, |test| test >= self.tests.len()) {
                        return Err("history regex test reference is out of bounds".to_string());
                    }
                }
                HistoryRegexSource::Concat(ref children)
                | HistoryRegexSource::Union(ref children)
                | HistoryRegexSource::Intersect(ref children) => {
                    if children
                        .iter()
                        .any(|child| usize::try_from(*child).map_or(true, |child| child >= index))
                    {
                        return Err(
                            "history regex reference must point to an earlier node".to_string()
                        );
                    }
                }
                HistoryRegexSource::Star(child) | HistoryRegexSource::Complement(child) => {
                    if usize::try_from(child).map_or(true, |child| child >= index) {
                        return Err(
                            "history regex reference must point to an earlier node".to_string()
                        );
                    }
                }
            }
        }
        if usize::try_from(self.root).map_or(true, |root| root >= self.regexes.len()) {
            return Err("history regex root is out of bounds".to_string());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pair() -> HistoryPairSource {
        HistoryPairSource {
            head: [
                HistoryHeadSource::Any,
                HistoryHeadSource::Any,
                HistoryHeadSource::Any,
            ],
            tests: Vec::new(),
            regexes: alloc::vec![HistoryRegexSource::Epsilon],
            root: 0,
        }
    }

    #[test]
    fn rejects_forward_cycles_and_missing_tests() {
        let mut source = pair();
        assert_eq!(source.validate(), Ok(()));
        source.regexes = alloc::vec![HistoryRegexSource::Star(0)];
        assert!(source.validate().is_err());
        source.regexes = alloc::vec![HistoryRegexSource::Test(0)];
        assert!(source.validate().is_err());
        source.tests = alloc::vec![HistoryTestSource::And(alloc::vec![0])];
        assert!(source.validate().is_err());
        source.tests = alloc::vec![HistoryTestSource::Bool(true)];
        assert_eq!(source.validate(), Ok(()));
        source.root = 1;
        assert!(source.validate().is_err());
    }

    #[test]
    fn rejects_cross_domain_and_unbound_variables() {
        let mut source = pair();
        source.tests.push(HistoryTestSource::Atom {
            field: HistoryField::Action,
            term: HistoryTermSource::Variable(HistoryField::Principal),
            positive: true,
        });
        assert!(source.validate().is_err());
        source.tests.clear();
        source.tests.push(HistoryTestSource::Atom {
            field: HistoryField::Principal,
            term: HistoryTermSource::Variable(HistoryField::Principal),
            positive: false,
        });
        assert!(source.validate().is_err());
        source.head[0] = HistoryHeadSource::Bind;
        assert_eq!(source.validate(), Ok(()));
    }
}
