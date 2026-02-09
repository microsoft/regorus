// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use serde::{Deserialize, Serialize};

macro_rules! rbac_builtins {
    ($( $variant:ident => { name: $name:literal, operator: $is_operator:expr } ),* $(,)?) => {
        impl RbacBuiltin {
            /// Parse a builtin name as used in the RBAC condition language.
            pub fn parse(name: &str) -> Option<Self> {
                match name {
                    $( $name => Some(Self::$variant), )*
                    _ => None,
                }
            }

            /// Parse a binary operator name (excludes function-style builtins).
            pub fn parse_operator(name: &str) -> Option<Self> {
                Self::parse(name).filter(|builtin| builtin.is_operator())
            }

            /// Returns true for infix operator-style builtins.
            pub const fn is_operator(self) -> bool {
                match self {
                    $( Self::$variant => $is_operator, )*
                }
            }

            /// RBAC builtin name.
            pub const fn name(self) -> &'static str {
                match self {
                    $( Self::$variant => $name, )*
                }
            }
        }
    };
}

/// RBAC builtin identifier.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RbacBuiltin {
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

    // Cross product operators
    ForAnyOfAnyValues,
    ForAllOfAnyValues,
    ForAnyOfAllValues,
    ForAllOfAllValues,

    // Action operators
    ActionMatches,
    SubOperationMatches,

    // Function-style builtins
    ToLower,
    ToUpper,
    Trim,
    NormalizeSet,
    NormalizeList,
    AddDays,
    ToTime,
}

rbac_builtins! {
    StringEquals => { name: "StringEquals", operator: true },
    StringNotEquals => { name: "StringNotEquals", operator: true },
    StringEqualsIgnoreCase => { name: "StringEqualsIgnoreCase", operator: true },
    StringNotEqualsIgnoreCase => { name: "StringNotEqualsIgnoreCase", operator: true },
    StringLike => { name: "StringLike", operator: true },
    StringNotLike => { name: "StringNotLike", operator: true },
    StringStartsWith => { name: "StringStartsWith", operator: true },
    StringNotStartsWith => { name: "StringNotStartsWith", operator: true },
    StringEndsWith => { name: "StringEndsWith", operator: true },
    StringNotEndsWith => { name: "StringNotEndsWith", operator: true },
    StringContains => { name: "StringContains", operator: true },
    StringNotContains => { name: "StringNotContains", operator: true },
    StringMatches => { name: "StringMatches", operator: true },
    StringNotMatches => { name: "StringNotMatches", operator: true },
    NumericEquals => { name: "NumericEquals", operator: true },
    NumericNotEquals => { name: "NumericNotEquals", operator: true },
    NumericLessThan => { name: "NumericLessThan", operator: true },
    NumericLessThanEquals => { name: "NumericLessThanEquals", operator: true },
    NumericGreaterThan => { name: "NumericGreaterThan", operator: true },
    NumericGreaterThanEquals => { name: "NumericGreaterThanEquals", operator: true },
    NumericInRange => { name: "NumericInRange", operator: true },
    BoolEquals => { name: "BoolEquals", operator: true },
    BoolNotEquals => { name: "BoolNotEquals", operator: true },
    DateTimeEquals => { name: "DateTimeEquals", operator: true },
    DateTimeNotEquals => { name: "DateTimeNotEquals", operator: true },
    DateTimeGreaterThan => { name: "DateTimeGreaterThan", operator: true },
    DateTimeGreaterThanEquals => { name: "DateTimeGreaterThanEquals", operator: true },
    DateTimeLessThan => { name: "DateTimeLessThan", operator: true },
    DateTimeLessThanEquals => { name: "DateTimeLessThanEquals", operator: true },
    TimeOfDayEquals => { name: "TimeOfDayEquals", operator: true },
    TimeOfDayNotEquals => { name: "TimeOfDayNotEquals", operator: true },
    TimeOfDayGreaterThan => { name: "TimeOfDayGreaterThan", operator: true },
    TimeOfDayGreaterThanEquals => { name: "TimeOfDayGreaterThanEquals", operator: true },
    TimeOfDayLessThan => { name: "TimeOfDayLessThan", operator: true },
    TimeOfDayLessThanEquals => { name: "TimeOfDayLessThanEquals", operator: true },
    TimeOfDayInRange => { name: "TimeOfDayInRange", operator: true },
    GuidEquals => { name: "GuidEquals", operator: true },
    GuidNotEquals => { name: "GuidNotEquals", operator: true },
    IpMatch => { name: "IpMatch", operator: true },
    IpNotMatch => { name: "IpNotMatch", operator: true },
    IpInRange => { name: "IpInRange", operator: true },
    ListContains => { name: "ListContains", operator: true },
    ListNotContains => { name: "ListNotContains", operator: true },
    ForAnyOfAnyValues => { name: "ForAnyOfAnyValues", operator: true },
    ForAllOfAnyValues => { name: "ForAllOfAnyValues", operator: true },
    ForAnyOfAllValues => { name: "ForAnyOfAllValues", operator: true },
    ForAllOfAllValues => { name: "ForAllOfAllValues", operator: true },
    ActionMatches => { name: "ActionMatches", operator: true },
    SubOperationMatches => { name: "SubOperationMatches", operator: true },
    ToLower => { name: "ToLower", operator: false },
    ToUpper => { name: "ToUpper", operator: false },
    Trim => { name: "Trim", operator: false },
    NormalizeSet => { name: "NormalizeSet", operator: false },
    NormalizeList => { name: "NormalizeList", operator: false },
    AddDays => { name: "AddDays", operator: false },
    ToTime => { name: "ToTime", operator: false },
}
