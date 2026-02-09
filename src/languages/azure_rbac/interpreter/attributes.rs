// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use alloc::format;
use alloc::string::{String, ToString as _};

use crate::languages::azure_rbac::ast::{
    AttributePathSegment, AttributeReference, AttributeSource, PrincipalType,
};
use crate::value::Value;

use super::error::ConditionEvalError;
use super::eval::Evaluator;

#[cfg(feature = "time")]
use chrono::{DateTime, Timelike as _};

impl<'a> Evaluator<'a> {
    pub(super) fn eval_attribute_reference(
        &mut self,
        attr: &AttributeReference,
    ) -> Result<Value, ConditionEvalError> {
        let mut value = match attr.source {
            AttributeSource::Request => self.resolve_request_attribute(attr),
            AttributeSource::Resource => self.resolve_resource_attribute(attr),
            AttributeSource::Principal => self.resolve_principal_attribute(attr),
            AttributeSource::Environment => self.resolve_environment_attribute(attr),
            AttributeSource::Context => Value::Undefined,
        };

        for segment in &attr.path {
            value = Self::apply_path_segment(value, segment)?;
        }

        Ok(value)
    }

    fn resolve_request_attribute(&self, attr: &AttributeReference) -> Value {
        let attributes = &self.context.request.attributes;
        let direct = Self::lookup_attribute_value(attributes, attr);
        if !matches!(direct, Value::Undefined) {
            return direct;
        }

        match attr.attribute.as_str() {
            "action" => self
                .context
                .request
                .action
                .clone()
                .map(|s: String| Value::String(s.into()))
                .unwrap_or(Value::Undefined),
            "dataAction" => self
                .context
                .request
                .data_action
                .clone()
                .map(|s: String| Value::String(s.into()))
                .unwrap_or(Value::Undefined),
            _ => Value::Undefined,
        }
    }

    fn resolve_resource_attribute(&self, attr: &AttributeReference) -> Value {
        let attributes = &self.context.resource.attributes;
        let direct = Self::lookup_attribute_value(attributes, attr);
        if !matches!(direct, Value::Undefined) {
            return direct;
        }

        match attr.attribute.as_str() {
            "id" => Value::String(self.context.resource.id.as_str().into()),
            "type" => Value::String(self.context.resource.resource_type.as_str().into()),
            "scope" => Value::String(self.context.resource.scope.as_str().into()),
            _ => Value::Undefined,
        }
    }

    fn resolve_principal_attribute(&self, attr: &AttributeReference) -> Value {
        let attributes = &self.context.principal.custom_security_attributes;
        let direct = Self::lookup_attribute_value(attributes, attr);
        if !matches!(direct, Value::Undefined) {
            return direct;
        }

        match attr.attribute.as_str() {
            "id" => Value::String(self.context.principal.id.as_str().into()),
            "principalType" => Value::String(self.principal_type_string().into()),
            _ => Value::Undefined,
        }
    }

    fn resolve_environment_attribute(&self, attr: &AttributeReference) -> Value {
        let EnvironmentContextValues {
            is_private_link,
            private_endpoint,
            subnet,
            utc_now,
            time_of_day,
        } = self.environment_values();

        match attr.attribute.as_str() {
            "isPrivateLink" => is_private_link,
            "privateEndpoint" => private_endpoint,
            "subnet" => subnet,
            "utcNow" => utc_now,
            "timeOfDay" => time_of_day,
            _ => Value::Undefined,
        }
    }

    fn environment_values(&self) -> EnvironmentContextValues {
        let is_private_link = self
            .context
            .environment
            .is_private_link
            .map(Value::Bool)
            .unwrap_or(Value::Undefined);

        let private_endpoint = self
            .context
            .environment
            .private_endpoint
            .clone()
            .map(|s: String| Value::String(s.into()))
            .unwrap_or(Value::Undefined);

        let subnet = self
            .context
            .environment
            .subnet
            .clone()
            .map(|s: String| Value::String(s.into()))
            .unwrap_or(Value::Undefined);

        let utc_now = self
            .context
            .environment
            .utc_now
            .clone()
            .map(|s: String| Value::String(s.into()))
            .unwrap_or(Value::Undefined);

        let time_of_day = self
            .context
            .environment
            .utc_now
            .as_ref()
            .and_then(|s| Self::time_of_day_from_rfc3339(s).ok())
            .map(|s: String| Value::String(s.into()))
            .unwrap_or(Value::Undefined);

        EnvironmentContextValues {
            is_private_link,
            private_endpoint,
            subnet,
            utc_now,
            time_of_day,
        }
    }

    const fn principal_type_string(&self) -> &'static str {
        match self.context.principal.principal_type {
            PrincipalType::User => "User",
            PrincipalType::Group => "Group",
            PrincipalType::ServicePrincipal => "ServicePrincipal",
            PrincipalType::ManagedServiceIdentity => "ManagedServiceIdentity",
        }
    }

    fn lookup_attribute_value(container: &Value, attr: &AttributeReference) -> Value {
        let key = attr.namespace.as_ref().map(|ns| {
            let capacity = ns
                .len()
                .saturating_add(attr.attribute.len())
                .saturating_add(1);
            let mut combined = String::with_capacity(capacity);
            combined.push_str(ns);
            combined.push(':');
            combined.push_str(&attr.attribute);
            combined
        });

        match *container {
            Value::Object(ref map) => {
                if let Some(ref ns) = attr.namespace {
                    let namespace_key = Value::String(ns.as_str().into());
                    #[allow(clippy::pattern_type_mismatch)]
                    if let Some(Value::Object(ns_obj)) = map.get(&namespace_key) {
                        let attr_key = Value::String(attr.attribute.as_str().into());
                        if let Some(value) = ns_obj.get(&attr_key) {
                            return value.clone();
                        }
                    }
                }

                if let Some(ref combined) = key {
                    let attr_key = Value::String(combined.as_str().into());
                    if let Some(value) = map.get(&attr_key) {
                        return value.clone();
                    }
                }

                let attr_key = Value::String(attr.attribute.as_str().into());
                map.get(&attr_key).cloned().unwrap_or(Value::Undefined)
            }
            _ => Value::Undefined,
        }
    }

    fn apply_path_segment(
        value: Value,
        segment: &AttributePathSegment,
    ) -> Result<Value, ConditionEvalError> {
        match *segment {
            AttributePathSegment::Key(ref key) => match value {
                Value::Object(map) => Ok(map
                    .get(&Value::String(key.as_str().into()))
                    .cloned()
                    .unwrap_or(Value::Undefined)),
                _ => Ok(Value::Undefined),
            },
            AttributePathSegment::Index(index) => match value {
                Value::Array(list) => Ok(list.get(index).cloned().unwrap_or(Value::Undefined)),
                _ => Ok(Value::Undefined),
            },
        }
    }

    fn time_of_day_from_rfc3339(value: &str) -> Result<String, ConditionEvalError> {
        #[cfg(feature = "time")]
        {
            let dt = DateTime::parse_from_rfc3339(value)
                .map_err(|err| ConditionEvalError::new(err.to_string()))?;
            let time = dt.time();
            Ok(format!(
                "{:02}:{:02}:{:02}",
                time.hour(),
                time.minute(),
                time.second()
            ))
        }

        #[cfg(not(feature = "time"))]
        {
            let _ = value;
            Err(ConditionEvalError::new(
                "time feature disabled; cannot derive timeOfDay",
            ))
        }
    }
}

struct EnvironmentContextValues {
    is_private_link: Value,
    private_endpoint: Value,
    subnet: Value,
    utc_now: Value,
    time_of_day: Value,
}
