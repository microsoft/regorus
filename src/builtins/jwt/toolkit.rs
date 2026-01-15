// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

#[cfg(feature = "jwt_openssl")]
use crate::builtins::jwt::backends::openssl::OpensslBackend;

#[cfg(feature = "jwt_openssl")]
pub type JwtBackend = OpensslBackend;
