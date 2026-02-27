// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::*;
use anyhow::Result;

pub trait Backend {
    fn encode_base64url(src: &[u8]) -> String;
    fn decode_base64url(src: &str) -> Result<Vec<u8>>;

    fn verify_hs256(token: &str, secret: &str) -> Result<bool>;
    fn verify_hs384(token: &str, secret: &str) -> Result<bool>;
    fn verify_hs512(token: &str, secret: &str) -> Result<bool>;

    fn verify_rs256(token: &str, certificate: &str) -> Result<bool>;
    fn verify_rs384(token: &str, certificate: &str) -> Result<bool>;
    fn verify_rs512(token: &str, certificate: &str) -> Result<bool>;

    fn verify_ps256(token: &str, certificate: &str) -> Result<bool>;
    fn verify_ps384(token: &str, certificate: &str) -> Result<bool>;
    fn verify_ps512(token: &str, certificate: &str) -> Result<bool>;

    fn verify_es256(token: &str, certificate: &str) -> Result<bool>;
    fn verify_es384(token: &str, certificate: &str) -> Result<bool>;
    fn verify_es512(token: &str, certificate: &str) -> Result<bool>;
}
