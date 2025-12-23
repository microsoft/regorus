#![allow(clippy::missing_const_for_fn, clippy::pattern_type_mismatch)]
// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;
use serde::{Deserialize, Serialize};

/// Array operator descriptor (e.g. ANY, ForAnyOfAnyValues:StringEquals)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ArrayOperator {
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub modifier: Option<String>,
}

/// Condition operator for Azure RBAC expressions
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ConditionOperator {
    // String operators
    StringEquals,
    StringNotEquals,
    StringEqualsIgnoreCase,
    StringNotEqualsIgnoreCase,
    StringLike,
    StringNotLike,
    StringStartsWith,
    StringNotStartsWith,
    StringEndsWith,
    StringNotEndsWith,
    StringContains,
    StringNotContains,
    StringMatches,
    StringNotMatches,

    // Numeric operators
    NumericEquals,
    NumericNotEquals,
    NumericLessThan,
    NumericLessThanEquals,
    NumericGreaterThan,
    NumericGreaterThanEquals,
    NumericInRange,

    // Boolean operators
    BoolEquals,
    BoolNotEquals,

    // DateTime operators
    DateTimeEquals,
    DateTimeNotEquals,
    DateTimeGreaterThan,
    DateTimeGreaterThanEquals,
    DateTimeLessThan,
    DateTimeLessThanEquals,

    // Time operators
    TimeOfDayEquals,
    TimeOfDayNotEquals,
    TimeOfDayGreaterThan,
    TimeOfDayGreaterThanEquals,
    TimeOfDayLessThan,
    TimeOfDayLessThanEquals,
    TimeOfDayInRange,

    // GUID operators
    GuidEquals,
    GuidNotEquals,

    // IP operators
    IpMatch,
    IpNotMatch,
    IpInRange,

    // List operators
    ListContains,
    ListNotContains,

    // Array quantifier operators
    ForAnyOfAnyValues,
    ForAllOfAnyValues,
    ForAnyOfAllValues,
    ForAllOfAllValues,

    // Action operators
    ActionMatches,
    SubOperationMatches,
}

impl ConditionOperator {
    /// Parse a condition operator from string identifier
    pub fn from_name(s: &str) -> Option<Self> {
        match s {
            "StringEquals" => Some(Self::StringEquals),
            "StringNotEquals" => Some(Self::StringNotEquals),
            "StringEqualsIgnoreCase" => Some(Self::StringEqualsIgnoreCase),
            "StringNotEqualsIgnoreCase" => Some(Self::StringNotEqualsIgnoreCase),
            "StringLike" => Some(Self::StringLike),
            "StringNotLike" => Some(Self::StringNotLike),
            "StringStartsWith" => Some(Self::StringStartsWith),
            "StringNotStartsWith" => Some(Self::StringNotStartsWith),
            "StringEndsWith" => Some(Self::StringEndsWith),
            "StringNotEndsWith" => Some(Self::StringNotEndsWith),
            "StringContains" => Some(Self::StringContains),
            "StringNotContains" => Some(Self::StringNotContains),
            "StringMatches" => Some(Self::StringMatches),
            "StringNotMatches" => Some(Self::StringNotMatches),
            "NumericEquals" => Some(Self::NumericEquals),
            "NumericNotEquals" => Some(Self::NumericNotEquals),
            "NumericLessThan" => Some(Self::NumericLessThan),
            "NumericLessThanEquals" => Some(Self::NumericLessThanEquals),
            "NumericGreaterThan" => Some(Self::NumericGreaterThan),
            "NumericGreaterThanEquals" => Some(Self::NumericGreaterThanEquals),
            "NumericInRange" => Some(Self::NumericInRange),
            "BoolEquals" => Some(Self::BoolEquals),
            "BoolNotEquals" => Some(Self::BoolNotEquals),
            "DateTimeEquals" => Some(Self::DateTimeEquals),
            "DateTimeNotEquals" => Some(Self::DateTimeNotEquals),
            "DateTimeGreaterThan" => Some(Self::DateTimeGreaterThan),
            "DateTimeGreaterThanEquals" => Some(Self::DateTimeGreaterThanEquals),
            "DateTimeLessThan" => Some(Self::DateTimeLessThan),
            "DateTimeLessThanEquals" => Some(Self::DateTimeLessThanEquals),
            "TimeOfDayEquals" => Some(Self::TimeOfDayEquals),
            "TimeOfDayNotEquals" => Some(Self::TimeOfDayNotEquals),
            "TimeOfDayGreaterThan" => Some(Self::TimeOfDayGreaterThan),
            "TimeOfDayGreaterThanEquals" => Some(Self::TimeOfDayGreaterThanEquals),
            "TimeOfDayLessThan" => Some(Self::TimeOfDayLessThan),
            "TimeOfDayLessThanEquals" => Some(Self::TimeOfDayLessThanEquals),
            "TimeOfDayInRange" => Some(Self::TimeOfDayInRange),
            "GuidEquals" => Some(Self::GuidEquals),
            "GuidNotEquals" => Some(Self::GuidNotEquals),
            "IpMatch" => Some(Self::IpMatch),
            "IpNotMatch" => Some(Self::IpNotMatch),
            "IpInRange" => Some(Self::IpInRange),
            "ListContains" => Some(Self::ListContains),
            "ListNotContains" => Some(Self::ListNotContains),
            "ForAnyOfAnyValues" => Some(Self::ForAnyOfAnyValues),
            "ForAllOfAnyValues" => Some(Self::ForAllOfAnyValues),
            "ForAnyOfAllValues" => Some(Self::ForAnyOfAllValues),
            "ForAllOfAllValues" => Some(Self::ForAllOfAllValues),
            "ActionMatches" => Some(Self::ActionMatches),
            "SubOperationMatches" => Some(Self::SubOperationMatches),
            _ => None,
        }
    }

    /// Convert condition operator to string
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::StringEquals => "StringEquals",
            Self::StringNotEquals => "StringNotEquals",
            Self::StringEqualsIgnoreCase => "StringEqualsIgnoreCase",
            Self::StringNotEqualsIgnoreCase => "StringNotEqualsIgnoreCase",
            Self::StringLike => "StringLike",
            Self::StringNotLike => "StringNotLike",
            Self::StringStartsWith => "StringStartsWith",
            Self::StringNotStartsWith => "StringNotStartsWith",
            Self::StringEndsWith => "StringEndsWith",
            Self::StringNotEndsWith => "StringNotEndsWith",
            Self::StringContains => "StringContains",
            Self::StringNotContains => "StringNotContains",
            Self::StringMatches => "StringMatches",
            Self::StringNotMatches => "StringNotMatches",
            Self::NumericEquals => "NumericEquals",
            Self::NumericNotEquals => "NumericNotEquals",
            Self::NumericLessThan => "NumericLessThan",
            Self::NumericLessThanEquals => "NumericLessThanEquals",
            Self::NumericGreaterThan => "NumericGreaterThan",
            Self::NumericGreaterThanEquals => "NumericGreaterThanEquals",
            Self::NumericInRange => "NumericInRange",
            Self::BoolEquals => "BoolEquals",
            Self::BoolNotEquals => "BoolNotEquals",
            Self::DateTimeEquals => "DateTimeEquals",
            Self::DateTimeNotEquals => "DateTimeNotEquals",
            Self::DateTimeGreaterThan => "DateTimeGreaterThan",
            Self::DateTimeGreaterThanEquals => "DateTimeGreaterThanEquals",
            Self::DateTimeLessThan => "DateTimeLessThan",
            Self::DateTimeLessThanEquals => "DateTimeLessThanEquals",
            Self::TimeOfDayEquals => "TimeOfDayEquals",
            Self::TimeOfDayNotEquals => "TimeOfDayNotEquals",
            Self::TimeOfDayGreaterThan => "TimeOfDayGreaterThan",
            Self::TimeOfDayGreaterThanEquals => "TimeOfDayGreaterThanEquals",
            Self::TimeOfDayLessThan => "TimeOfDayLessThan",
            Self::TimeOfDayLessThanEquals => "TimeOfDayLessThanEquals",
            Self::TimeOfDayInRange => "TimeOfDayInRange",
            Self::GuidEquals => "GuidEquals",
            Self::GuidNotEquals => "GuidNotEquals",
            Self::IpMatch => "IpMatch",
            Self::IpNotMatch => "IpNotMatch",
            Self::IpInRange => "IpInRange",
            Self::ListContains => "ListContains",
            Self::ListNotContains => "ListNotContains",
            Self::ForAnyOfAnyValues => "ForAnyOfAnyValues",
            Self::ForAllOfAnyValues => "ForAllOfAnyValues",
            Self::ForAnyOfAllValues => "ForAnyOfAllValues",
            Self::ForAllOfAllValues => "ForAllOfAllValues",
            Self::ActionMatches => "ActionMatches",
            Self::SubOperationMatches => "SubOperationMatches",
        }
    }
}

impl core::str::FromStr for ConditionOperator {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_name(s).ok_or(())
    }
}
