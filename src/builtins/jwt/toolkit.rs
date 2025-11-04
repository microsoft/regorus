// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(feature = "jwt-openssl")]
use crate::builtins::jwt::backends::openssl::OpensslBackend;

#[cfg(feature = "jwt-openssl")]
pub type JwtBackend = OpensslBackend;
