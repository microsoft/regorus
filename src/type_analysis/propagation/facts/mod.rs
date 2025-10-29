// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

mod iteration;
mod origins;
mod schema;

pub(crate) use origins::{derived_from_pair, extend_origins_with_segment, mark_origins_derived};
pub(crate) use schema::{
    extract_schema_constant, schema_additional_properties_schema, schema_allows_value,
    schema_array_items, schema_property,
};
