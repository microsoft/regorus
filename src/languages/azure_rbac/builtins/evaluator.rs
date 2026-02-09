// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::indexing_slicing)]

use crate::value::Value;
use alloc::format;

use super::super::ast::context::EvaluationContext;
use super::bools;
use super::datetime;
use super::functions;
use super::ids::RbacBuiltin;
use super::ip;
use super::lists;
use super::numbers;
use super::quantifiers;
use super::strings;
use super::time_of_day;

/// Builtin evaluation context.
#[derive(Debug, Clone, Copy)]
pub struct RbacBuiltinContext<'a> {
    pub evaluation: &'a EvaluationContext,
}

impl<'a> RbacBuiltinContext<'a> {
    pub const fn new(evaluation: &'a EvaluationContext) -> Self {
        Self { evaluation }
    }
}

/// Builtin evaluation error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RbacBuiltinError {
    message: alloc::string::String,
}

impl RbacBuiltinError {
    pub fn new(message: impl Into<alloc::string::String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl core::fmt::Display for RbacBuiltinError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.message)
    }
}

/// Default RBAC builtin evaluator implementation.
#[derive(Debug, Default, Clone, Copy)]
pub struct DefaultRbacBuiltinEvaluator;

impl DefaultRbacBuiltinEvaluator {
    pub const fn new() -> Self {
        Self
    }

    fn ensure_arg_count(
        builtin: RbacBuiltin,
        args: &[Value],
        expected: usize,
    ) -> Result<(), RbacBuiltinError> {
        if args.len() == expected {
            Ok(())
        } else {
            Err(RbacBuiltinError::new(format!(
                "{} expects {} arguments",
                builtin.name(),
                expected
            )))
        }
    }

    fn arg1(builtin: RbacBuiltin, args: &[Value]) -> Result<&Value, RbacBuiltinError> {
        if args.len() != 1 {
            return Err(RbacBuiltinError::new(format!(
                "{} expects 1 argument",
                builtin.name()
            )));
        }
        args.first()
            .ok_or_else(|| RbacBuiltinError::new(format!("{} expects 1 argument", builtin.name())))
    }

    fn arg2(builtin: RbacBuiltin, args: &[Value]) -> Result<(&Value, &Value), RbacBuiltinError> {
        if args.len() != 2 {
            return Err(RbacBuiltinError::new(format!(
                "{} expects 2 arguments",
                builtin.name()
            )));
        }
        let left = args.first().ok_or_else(|| {
            RbacBuiltinError::new(format!("{} expects 2 arguments", builtin.name()))
        })?;
        let right = args.get(1).ok_or_else(|| {
            RbacBuiltinError::new(format!("{} expects 2 arguments", builtin.name()))
        })?;
        Ok((left, right))
    }
    pub fn eval(
        &self,
        builtin: RbacBuiltin,
        args: &[Value],
        ctx: &RbacBuiltinContext<'_>,
    ) -> Result<Value, RbacBuiltinError> {
        match builtin {
            RbacBuiltin::StringEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(strings::string_equals(&args[0], &args[1])?))
            }
            RbacBuiltin::StringNotEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!strings::string_equals(&args[0], &args[1])?))
            }
            RbacBuiltin::StringEqualsIgnoreCase => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(strings::string_equals_ignore_case(
                    &args[0], &args[1],
                )?))
            }
            RbacBuiltin::StringNotEqualsIgnoreCase => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!strings::string_equals_ignore_case(
                    &args[0], &args[1],
                )?))
            }
            RbacBuiltin::StringLike => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(strings::string_like(&args[0], &args[1])?))
            }
            RbacBuiltin::StringNotLike => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!strings::string_like(&args[0], &args[1])?))
            }
            RbacBuiltin::StringStartsWith => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(strings::string_starts_with(
                    &args[0], &args[1],
                )?))
            }
            RbacBuiltin::StringNotStartsWith => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!strings::string_starts_with(
                    &args[0], &args[1],
                )?))
            }
            RbacBuiltin::StringEndsWith => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(strings::string_ends_with(&args[0], &args[1])?))
            }
            RbacBuiltin::StringNotEndsWith => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!strings::string_ends_with(&args[0], &args[1])?))
            }
            RbacBuiltin::StringContains => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(strings::string_contains(&args[0], &args[1])?))
            }
            RbacBuiltin::StringNotContains => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!strings::string_contains(&args[0], &args[1])?))
            }
            RbacBuiltin::StringMatches => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(strings::string_matches(&args[0], &args[1])?))
            }
            RbacBuiltin::StringNotMatches => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!strings::string_matches(&args[0], &args[1])?))
            }
            RbacBuiltin::NumericEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(numbers::numeric_compare(
                    &args[0],
                    &args[1],
                    "==",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::NumericNotEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(numbers::numeric_compare(
                    &args[0],
                    &args[1],
                    "!=",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::NumericLessThan => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(numbers::numeric_compare(
                    &args[0],
                    &args[1],
                    "<",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::NumericLessThanEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(numbers::numeric_compare(
                    &args[0],
                    &args[1],
                    "<=",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::NumericGreaterThan => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(numbers::numeric_compare(
                    &args[0],
                    &args[1],
                    ">",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::NumericGreaterThanEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(numbers::numeric_compare(
                    &args[0],
                    &args[1],
                    ">=",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::NumericInRange => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(numbers::numeric_in_range(
                    &args[0],
                    &args[1],
                    builtin.name(),
                )?))
            }
            RbacBuiltin::BoolEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(bools::bool_equals(
                    &args[0],
                    &args[1],
                    builtin.name(),
                )?))
            }
            RbacBuiltin::BoolNotEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!bools::bool_equals(
                    &args[0],
                    &args[1],
                    builtin.name(),
                )?))
            }
            RbacBuiltin::DateTimeEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(datetime::datetime_compare(
                    &args[0],
                    &args[1],
                    "==",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::DateTimeNotEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!datetime::datetime_compare(
                    &args[0],
                    &args[1],
                    "==",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::DateTimeGreaterThan => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(datetime::datetime_compare(
                    &args[0],
                    &args[1],
                    ">",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::DateTimeGreaterThanEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(datetime::datetime_compare(
                    &args[0],
                    &args[1],
                    ">=",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::DateTimeLessThan => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(datetime::datetime_compare(
                    &args[0],
                    &args[1],
                    "<",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::DateTimeLessThanEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(datetime::datetime_compare(
                    &args[0],
                    &args[1],
                    "<=",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::TimeOfDayEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(time_of_day::time_compare(
                    &args[0],
                    &args[1],
                    "==",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::TimeOfDayNotEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(!time_of_day::time_compare(
                    &args[0],
                    &args[1],
                    "==",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::TimeOfDayGreaterThan => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(time_of_day::time_compare(
                    &args[0],
                    &args[1],
                    ">",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::TimeOfDayGreaterThanEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(time_of_day::time_compare(
                    &args[0],
                    &args[1],
                    ">=",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::TimeOfDayLessThan => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(time_of_day::time_compare(
                    &args[0],
                    &args[1],
                    "<",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::TimeOfDayLessThanEquals => {
                Self::ensure_arg_count(builtin, args, 2)?;
                Ok(Value::Bool(time_of_day::time_compare(
                    &args[0],
                    &args[1],
                    "<=",
                    builtin.name(),
                )?))
            }
            RbacBuiltin::TimeOfDayInRange => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(time_of_day::time_in_range(
                    left,
                    right,
                    builtin.name(),
                )?))
            }
            RbacBuiltin::GuidEquals => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(strings::guid_equals(
                    left,
                    right,
                    builtin.name(),
                )?))
            }
            RbacBuiltin::GuidNotEquals => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(!strings::guid_equals(
                    left,
                    right,
                    builtin.name(),
                )?))
            }
            RbacBuiltin::IpMatch => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(ip::ip_match(left, right, builtin.name())?))
            }
            RbacBuiltin::IpNotMatch => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(!ip::ip_match(left, right, builtin.name())?))
            }
            RbacBuiltin::IpInRange => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(ip::ip_in_range(left, right, builtin.name())?))
            }
            RbacBuiltin::ListContains => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(lists::list_contains(left, right)?))
            }
            RbacBuiltin::ListNotContains => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(!lists::list_contains(left, right)?))
            }
            RbacBuiltin::ForAnyOfAnyValues => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(quantifiers::for_any_of_any_values(
                    left, right,
                )?))
            }
            RbacBuiltin::ForAllOfAnyValues => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(quantifiers::for_all_of_any_values(
                    left, right,
                )?))
            }
            RbacBuiltin::ForAnyOfAllValues => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(quantifiers::for_any_of_all_values(
                    left, right,
                )?))
            }
            RbacBuiltin::ForAllOfAllValues => {
                let (left, right) = Self::arg2(builtin, args)?;
                Ok(Value::Bool(quantifiers::for_all_of_all_values(
                    left, right,
                )?))
            }
            RbacBuiltin::ActionMatches => functions::action_matches(args, ctx),
            RbacBuiltin::SubOperationMatches => functions::suboperation_matches(args, ctx),
            RbacBuiltin::ToLower => {
                let value = Self::arg1(builtin, args)?;
                functions::to_lower(value)
            }
            RbacBuiltin::ToUpper => {
                let value = Self::arg1(builtin, args)?;
                functions::to_upper(value)
            }
            RbacBuiltin::Trim => {
                let value = Self::arg1(builtin, args)?;
                functions::trim(value)
            }
            RbacBuiltin::NormalizeSet => {
                let value = Self::arg1(builtin, args)?;
                functions::normalize_set(value)
            }
            RbacBuiltin::NormalizeList => {
                let value = Self::arg1(builtin, args)?;
                functions::normalize_list(value)
            }
            RbacBuiltin::AddDays => {
                let (left, right) = Self::arg2(builtin, args)?;
                functions::add_days(left, right)
            }
            RbacBuiltin::ToTime => {
                let value = Self::arg1(builtin, args)?;
                functions::to_time(value)
            }
        }
    }
}
