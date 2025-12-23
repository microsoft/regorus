// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#![allow(clippy::pattern_type_mismatch)]

//! Error definitions for the destructuring planner.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;
use anyhow::Error;
use core::error::Error as CoreError;
use core::fmt;

use crate::lexer::Span;

/// Errors produced while building binding plans.
#[derive(Debug)]
pub enum BindingPlannerError {
    /// Assignment operator := requires left-hand side to have bindable variables.
    ColonEqualsRequiresBindableLeft { span: Span },
    /// Array size mismatch in assignment destructuring.
    ArraySizeMismatch {
        left_size: usize,
        right_size: usize,
        span: Span,
    },
    /// Array length mismatch detected while planning evaluation (no assignments).
    ArrayLengthMismatch {
        expected: usize,
        actual: usize,
        span: Span,
    },
    /// Object literal keys mismatch detected while planning evaluation (no assignments).
    ObjectLiteralKeysMismatch {
        expected: Vec<String>,
        actual: Vec<String>,
        span: Span,
    },
    /// Object field count mismatch in assignment destructuring.
    ObjectFieldCountMismatch {
        left_count: usize,
        right_count: usize,
        span: Span,
    },
    /// Object key not found in destructuring.
    ObjectKeyNotFound { key: String, span: Span },
    /// Variable reuse detected when a new binding is required.
    VariableAlreadyDefined { var: String, span: Span },
    /// Incompatible destructuring patterns.
    IncompatibleDestructuringPatterns { span: Span },
    /// Failed to create destructuring plan.
    FailedToCreateDestructuringPlan { plan_type: String, span: Span },
}

/// Result alias used throughout the binding planner.
pub type Result<T> = core::result::Result<T, BindingPlannerError>;

/// Convert planner errors into diagnostic-rich anyhow errors for compiler callers.
pub fn map_binding_error(err: BindingPlannerError) -> Error {
    match err {
		BindingPlannerError::ColonEqualsRequiresBindableLeft { span } => span
			.error("assignment operator := requires left-hand side to have bindable variables"),
		BindingPlannerError::ArraySizeMismatch { span, .. }
		| BindingPlannerError::ArrayLengthMismatch { span, .. } => {
			span.error("mismatch in number of array elements")
		}
		BindingPlannerError::ObjectLiteralKeysMismatch {
			expected,
			actual,
			span,
		} => span.error(&format!(
			"object literal keys mismatch. Expected keys {:?} got {:?}.",
			expected, actual
		)),
		BindingPlannerError::ObjectFieldCountMismatch {
			left_count,
			right_count,
			span,
		} => span.error(&format!(
			"object field count mismatch in assignment: left has {left_count} fields, right has {right_count} fields"
		)),
		BindingPlannerError::ObjectKeyNotFound { key, span } => span
			.error(&format!("key \"{key}\" not found in left-hand side object during destructuring")),
		BindingPlannerError::VariableAlreadyDefined { var, span } => {
			span.error(&format!("var `{var}` used before definition below"))
		}
		BindingPlannerError::IncompatibleDestructuringPatterns { span } => span.error(
			"incompatible destructuring patterns: both sides must be arrays or objects with matching structure",
		),
		BindingPlannerError::FailedToCreateDestructuringPlan { plan_type, span } => {
			span.error(&format!("failed to create {plan_type} destructuring plan"))
		}
	}
}

impl BindingPlannerError {
    pub(crate) fn to_span_message(&self) -> String {
        match self {
			BindingPlannerError::ColonEqualsRequiresBindableLeft { span } => span
				.message(
					"error",
					"assignment operator := requires left-hand side to have bindable variables",
				),
			BindingPlannerError::ArraySizeMismatch {
				left_size,
				right_size,
				span,
			} => {
				let detail = format!(
					"mismatch in number of array elements (left has {left_size}, right has {right_size})"
				);
				span.message("error", detail.as_str())
			}
			BindingPlannerError::ArrayLengthMismatch {
				expected,
				actual,
				span,
			} => {
				let detail = format!(
					"array length mismatch. Expected {expected} got {actual}."
				);
				span.message("error", detail.as_str())
			}
			BindingPlannerError::ObjectLiteralKeysMismatch {
				expected,
				actual,
				span,
			} => {
				let detail = format!(
					"object literal keys mismatch. Expected keys {:?} got {:?}.",
					expected, actual
				);
				span.message("error", detail.as_str())
			}
			BindingPlannerError::ObjectFieldCountMismatch {
				left_count,
				right_count,
				span,
			} => {
				let detail = format!(
					"object field count mismatch in assignment: left has {left_count} fields, right has {right_count} fields"
				);
				span.message("error", detail.as_str())
			}
			BindingPlannerError::ObjectKeyNotFound { key, span } => {
				let detail = format!(
					"key \"{key}\" not found in left-hand side object during destructuring"
				);
				span.message("error", detail.as_str())
			}
			BindingPlannerError::VariableAlreadyDefined { var, span } => {
				let detail = format!("var `{var}` used before definition below");
				span.message("error", detail.as_str())
			}
			BindingPlannerError::IncompatibleDestructuringPatterns { span } => span
				.message(
					"error",
					"incompatible destructuring patterns: both sides must be arrays or objects with matching structure",
				),
			BindingPlannerError::FailedToCreateDestructuringPlan { plan_type, span } => {
				let detail = format!("failed to create {plan_type} destructuring plan");
				span.message("error", detail.as_str())
			}
		}
    }
}

impl fmt::Display for BindingPlannerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_span_message())
    }
}

impl CoreError for BindingPlannerError {}
