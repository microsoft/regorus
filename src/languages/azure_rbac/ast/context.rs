// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::string::String;
use serde::{Deserialize, Serialize};

use crate::value::Value;

/// Principal type
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum PrincipalType {
    User,
    Group,
    ServicePrincipal,
    ManagedServiceIdentity,
}

/// Evaluation context - what information is available when evaluating RBAC policies
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EvaluationContext {
    pub principal: Principal,
    pub resource: Resource,
    pub request: RequestContext,
    pub environment: EnvironmentContext,
    pub action: Option<String>,
    pub suboperation: Option<String>,
}

/// Principal information (user, group, service principal, etc.)
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Principal {
    pub id: String,
    pub principal_type: PrincipalType,
    pub custom_security_attributes: Value,
}

/// Resource information
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Resource {
    pub id: String,
    pub resource_type: String,
    pub scope: String,
    pub attributes: Value,
}

/// Request context information
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RequestContext {
    pub action: Option<String>,
    pub data_action: Option<String>,
    pub attributes: Value,
}

/// Environment context information
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct EnvironmentContext {
    pub is_private_link: Option<bool>,
    pub private_endpoint: Option<String>,
    pub subnet: Option<String>,
    pub utc_now: Option<String>,
}
