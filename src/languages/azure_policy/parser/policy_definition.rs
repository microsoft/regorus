// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

//! Parsing for the full Azure Policy definition envelope.
//!
//! Handles the outer `{ "properties": { ... } }` wrapper, extracting typed
//! fields (`displayName`, `description`, `mode`, `parameters`, `policyRule`)
//! and collecting everything else into `extra`.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use crate::lexer::Span;

use crate::languages::azure_policy::ast::{
    JsonValue, ObjectEntry, ParameterDefinition, PolicyDefinition, PolicyRule,
};

use super::core::Parser;
use super::error::ParseError;

impl<'source> Parser<'source> {
    /// Parse a full Azure Policy definition JSON.
    ///
    /// Accepts two forms:
    /// 1. **Wrapped**: `{ "properties": { ... }, ... }` — the standard ARM resource format.
    /// 2. **Unwrapped**: `{ "displayName": ..., "policyRule": ..., ... }` — just the
    ///    `properties` contents directly.
    ///
    /// In the wrapped form, fields outside `properties` (like `id`, `name`, `type`)
    /// are collected into `extra`.
    ///
    /// Detection: if the top-level object has a `"properties"` key whose value
    /// is a JSON object, the wrapped path is taken.  (In practice, the ARM
    /// resource envelope always uses `"properties"` to wrap the definition body.)
    pub fn parse_policy_definition(&mut self) -> Result<PolicyDefinition, ParseError> {
        let open = self.expect_symbol("{")?;

        // Determine whether this looks like the wrapped ARM resource form by
        // scanning top-level keys as they are parsed.
        //
        // Because JSON keys can appear in any order, we handle the general case:
        // iterate all top-level keys; if we encounter "properties" whose value is
        // an object, take the wrapped path.  Keys outside "properties" go into
        // `extra`.
        //
        // For the unwrapped form, all top-level keys are treated as
        // properties-level fields.
        let mut display_name: Option<String> = None;
        let mut description: Option<String> = None;
        let mut mode: Option<String> = None;
        let mut metadata: Option<JsonValue> = None;
        let mut parameters: Vec<ParameterDefinition> = Vec::new();
        let mut policy_rule: Option<PolicyRule> = None;
        let mut extra = Vec::new();

        // Track whether we found a "properties" object (wrapped form).
        let mut found_properties = false;
        // Track whether we have seen any "properties" key (for duplicate detection).
        let mut seen_properties = false;
        // Track seen recognized keys for duplicate detection (unwrapped path).
        let mut seen_keys: Vec<String> = Vec::new();

        if self.token_text() != "}" {
            loop {
                let (key_span, key) = self.expect_string()?;
                self.expect_symbol(":")?;

                match key.to_lowercase().as_str() {
                    "properties" if seen_properties => {
                        return Err(ParseError::DuplicateKey {
                            span: key_span,
                            key,
                        });
                    }
                    "properties" => {
                        seen_properties = true;

                        if self.token_text() == "{" {
                            // Wrapped form: parse inner properties object structurally.
                            found_properties = true;
                            self.parse_properties_fields(
                                &mut display_name,
                                &mut description,
                                &mut mode,
                                &mut metadata,
                                &mut parameters,
                                &mut policy_rule,
                                &mut extra,
                                &mut seen_keys,
                            )?;
                        } else {
                            // Unwrapped form: "properties" is just a regular key.
                            Self::handle_properties_key(
                                self,
                                key_span,
                                &key,
                                &mut display_name,
                                &mut description,
                                &mut mode,
                                &mut metadata,
                                &mut parameters,
                                &mut policy_rule,
                                &mut extra,
                                &mut seen_keys,
                            )?;
                        }
                    }
                    _ if !found_properties => {
                        // Unwrapped form: dispatch on properties-level keys.
                        Self::handle_properties_key(
                            self,
                            key_span,
                            &key,
                            &mut display_name,
                            &mut description,
                            &mut mode,
                            &mut metadata,
                            &mut parameters,
                            &mut policy_rule,
                            &mut extra,
                            &mut seen_keys,
                        )?;
                    }
                    _ => {
                        // Wrapped form: keys outside "properties" go to extra.
                        let value = self.parse_json_value()?;
                        extra.push(ObjectEntry {
                            key_span,
                            key,
                            value,
                        });
                    }
                }

                if self.token_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        let close = self.expect_symbol("}")?;
        let span = Span {
            source: open.source.clone(),
            line: open.line,
            col: open.col,
            start: open.start,
            end: close.end,
        };

        let policy_rule = policy_rule.ok_or_else(|| ParseError::MissingKey {
            span: span.clone(),
            key: "policyRule",
        })?;

        Ok(PolicyDefinition {
            span,
            display_name,
            description,
            mode,
            metadata,
            parameters,
            policy_rule,
            extra,
        })
    }

    /// Parse the interior of a `"properties": { ... }` object, dispatching
    /// recognized keys to their typed parsers.
    #[allow(clippy::too_many_arguments)]
    fn parse_properties_fields(
        &mut self,
        display_name: &mut Option<String>,
        description: &mut Option<String>,
        mode: &mut Option<String>,
        metadata: &mut Option<JsonValue>,
        parameters: &mut Vec<ParameterDefinition>,
        policy_rule: &mut Option<PolicyRule>,
        extra: &mut Vec<ObjectEntry>,
        seen_keys: &mut Vec<String>,
    ) -> Result<(), ParseError> {
        self.expect_symbol("{")?;

        if self.token_text() != "}" {
            loop {
                let (key_span, key) = self.expect_string()?;
                self.expect_symbol(":")?;

                Self::handle_properties_key(
                    self,
                    key_span,
                    &key,
                    display_name,
                    description,
                    mode,
                    metadata,
                    parameters,
                    policy_rule,
                    extra,
                    seen_keys,
                )?;

                if self.token_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        self.expect_symbol("}")?;
        Ok(())
    }

    /// Handle a single properties-level key, dispatching to the appropriate
    /// typed parser or collecting into `extra`.
    #[allow(clippy::too_many_arguments)]
    fn handle_properties_key(
        &mut self,
        key_span: Span,
        key: &str,
        display_name: &mut Option<String>,
        description: &mut Option<String>,
        mode: &mut Option<String>,
        metadata: &mut Option<JsonValue>,
        parameters: &mut Vec<ParameterDefinition>,
        policy_rule: &mut Option<PolicyRule>,
        extra: &mut Vec<ObjectEntry>,
        seen_keys: &mut Vec<String>,
    ) -> Result<(), ParseError> {
        let lk = key.to_lowercase();

        // Reject duplicate recognized property keys regardless of value type.
        let recognized = matches!(
            lk.as_str(),
            "displayname" | "description" | "mode" | "metadata" | "parameters" | "policyrule"
        );
        if recognized {
            if seen_keys.contains(&lk) {
                return Err(ParseError::DuplicateKey {
                    span: key_span,
                    key: key.into(),
                });
            }
            seen_keys.push(lk.clone());
        }

        match lk.as_str() {
            "displayname" => {
                let value = self.parse_json_value()?;
                assign_string_or_extra(value, display_name, key_span, key, extra);
            }
            "description" => {
                let value = self.parse_json_value()?;
                assign_string_or_extra(value, description, key_span, key, extra);
            }
            "mode" => {
                let value = self.parse_json_value()?;
                assign_string_or_extra(value, mode, key_span, key, extra);
            }
            "metadata" => {
                *metadata = Some(self.parse_json_value()?);
            }
            "parameters" => {
                // Parameters must be a JSON object; if not, push to extra.
                if self.token_text() == "{" {
                    *parameters = self.parse_parameter_definitions()?;
                } else {
                    let value = self.parse_json_value()?;
                    extra.push(ObjectEntry {
                        key_span,
                        key: key.into(),
                        value,
                    });
                }
            }
            "policyrule" => {
                // Parse the policyRule directly from the token stream!
                *policy_rule = Some(self.parse_policy_rule()?);
            }
            _ => {
                let value = self.parse_json_value()?;
                extra.push(ObjectEntry {
                    key_span,
                    key: key.into(),
                    value,
                });
            }
        }
        Ok(())
    }

    /// Parse a `"parameters": { ... }` object into a list of
    /// [`ParameterDefinition`], consuming tokens directly from the stream.
    fn parse_parameter_definitions(&mut self) -> Result<Vec<ParameterDefinition>, ParseError> {
        self.expect_symbol("{")?;

        let mut defs = Vec::new();
        let mut seen_names = BTreeSet::new();

        if self.token_text() != "}" {
            loop {
                let param = self.parse_single_parameter()?;
                if !seen_names.insert(param.name.to_lowercase()) {
                    return Err(ParseError::DuplicateKey {
                        span: param.name_span.clone(),
                        key: param.name.clone(),
                    });
                }
                defs.push(param);

                if self.token_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        self.expect_symbol("}")?;
        Ok(defs)
    }

    /// Parse a single `"paramName": { ... }` entry.
    fn parse_single_parameter(&mut self) -> Result<ParameterDefinition, ParseError> {
        let (name_span, name) = self.expect_string()?;
        self.expect_symbol(":")?;

        // Parameter definitions must be JSON objects.
        if self.token_text() != "{" {
            return Err(ParseError::Custom {
                span: name_span,
                message: alloc::format!("expected object for parameter '{}'", name),
            });
        }

        let open = self.expect_symbol("{")?;

        let mut param_type: Option<String> = None;
        let mut default_value: Option<JsonValue> = None;
        let mut allowed_values: Option<Vec<JsonValue>> = None;
        let mut metadata: Option<JsonValue> = None;
        let mut extra = Vec::new();
        // Track seen recognized keys for duplicate detection.
        let mut seen_type = false;
        let mut seen_default_value = false;
        let mut seen_allowed_values = false;
        let mut seen_metadata = false;

        if self.token_text() != "}" {
            loop {
                let (ks, k) = self.expect_string()?;
                self.expect_symbol(":")?;

                match k.to_lowercase().as_str() {
                    "type" => {
                        if seen_type {
                            return Err(ParseError::DuplicateKey { span: ks, key: k });
                        }
                        seen_type = true;
                        let value = self.parse_json_value()?;
                        assign_string_or_extra(value, &mut param_type, ks, &k, &mut extra);
                    }
                    "defaultvalue" => {
                        if seen_default_value {
                            return Err(ParseError::DuplicateKey { span: ks, key: k });
                        }
                        seen_default_value = true;
                        default_value = Some(self.parse_json_value()?);
                    }
                    "allowedvalues" => {
                        if seen_allowed_values {
                            return Err(ParseError::DuplicateKey { span: ks, key: k });
                        }
                        seen_allowed_values = true;
                        let value = self.parse_json_value()?;
                        if let JsonValue::Array(_, items) = value {
                            allowed_values = Some(items);
                        } else {
                            extra.push(ObjectEntry {
                                key_span: ks,
                                key: k,
                                value,
                            });
                        }
                    }
                    "metadata" => {
                        if seen_metadata {
                            return Err(ParseError::DuplicateKey { span: ks, key: k });
                        }
                        seen_metadata = true;
                        metadata = Some(self.parse_json_value()?);
                    }
                    _ => {
                        let value = self.parse_json_value()?;
                        extra.push(ObjectEntry {
                            key_span: ks,
                            key: k,
                            value,
                        });
                    }
                }

                if self.token_text() == "," {
                    self.advance()?;
                } else {
                    break;
                }
            }
        }

        let close = self.expect_symbol("}")?;
        let span = Span {
            source: open.source.clone(),
            line: open.line,
            col: open.col,
            start: open.start,
            end: close.end,
        };

        Ok(ParameterDefinition {
            span,
            name,
            name_span,
            param_type,
            default_value,
            allowed_values,
            metadata,
            extra,
        })
    }
}

// ============================================================================
// Helpers
// ============================================================================

/// If `value` is a plain string, assign it to `target`; otherwise push
/// the entry to `extra` so callers don't have to repeat this pattern.
fn assign_string_or_extra(
    value: JsonValue,
    target: &mut Option<String>,
    key_span: Span,
    key: &str,
    extra: &mut Vec<ObjectEntry>,
) {
    if let JsonValue::Str(_, ref s) = value {
        *target = Some(s.clone());
    } else {
        extra.push(ObjectEntry {
            key_span,
            key: key.into(),
            value,
        });
    }
}
