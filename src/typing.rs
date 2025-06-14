// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::ast::*;
use crate::*;
use alloc::collections::BTreeMap;
use anyhow::Result;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Deserialize, Serialize)]
#[serde(tag = "type")]
#[serde(rename_all = "camelCase")]
pub enum Type {
    Null,
    Bool,
    Number,
    String,

    // Homogenous arrays and sets
    Array { item_type: Rc<Type> },
    Set { item_type: Rc<Type> },

    // Objects with string keys
    Object { fields: BTreeMap<String, Type> },
    // TODO:
    // Heterogenous arrays and sets
    // Objects with non string keys
}

pub struct TypeCheck {
    rules: Map<String, Vec<Ref<Rule>>>,
    input: Rc<Type>,
}

impl TypeCheck {
    pub fn new(rules: Map<String, Vec<Ref<Rule>>>, input: Rc<Type>) -> Self {
        Self { rules, input }
    }

    fn check_rule(&mut self, rule: &Ref<Rule>) -> Result<Type> {
        Ok(Type::Null)
    }

    fn check_rules(&mut self, name:& String, rules: &[Ref<Rule>]) -> Result<()> {
        for rule in rules {
            let _t = self.check_rule(rule)?;
            // TODO: Recursion.
            // TODO: Rule heads with vars
        }
        Ok(())
    }
    pub fn check(&mut self) -> Result<()> {
        for (name, rules) in self.rules.clone().iter() {
            self.check_rules(name, rules)?;
        }
        Ok(())
    }
}
