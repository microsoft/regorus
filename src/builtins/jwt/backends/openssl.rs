// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

use crate::builtins::jwt::backend::Backend;
use crate::builtins::jwt::utils::split_token;
use anyhow::{anyhow, Result};
use openssl::base64;
use openssl::bn::BigNum;
use openssl::ec::{EcGroup, EcKey};
use openssl::ecdsa::EcdsaSig;
use openssl::hash::MessageDigest;
use openssl::nid::Nid;
use openssl::pkey::{PKey, Public};
use openssl::rsa::{Padding, Rsa};
use openssl::sign::{Signer, Verifier};
use openssl::x509::X509;
use serde::Deserialize;

use crate::*;

#[derive(Deserialize)]
struct Jwk {
    kty: String,
    n: Option<String>,   // for RSA
    e: Option<String>,   // for RSA
    crv: Option<String>, // for EC
    x: Option<String>,   // for EC
    y: Option<String>,   // for EC
}

fn verify_hmac(token: &str, secret: &str, hash_fn: MessageDigest) -> Result<bool> {
    let (header, payload, signature) = split_token(token)?;
    let sign_payload = &token[..header.len() + 1 + payload.len()];

    let key = PKey::hmac(secret.as_bytes())?;
    let mut signer = Signer::new(hash_fn, &key)?;
    signer.update(sign_payload.as_bytes())?;

    let expected_signature = signer.sign_to_vec()?;
    let encoded_expected_signature = OpensslBackend::encode_base64url(&expected_signature);

    Ok(signature == encoded_expected_signature)
}

/// Converts JWK json to public key
fn jwk_to_pkey(jwk_json: &str) -> Result<PKey<Public>> {
    let jwk: Jwk = serde_json::from_str(jwk_json).map_err(|e| anyhow!("Invalid JWK JSON: {e}"))?;

    match jwk.kty.as_str() {
        "RSA" => {
            let n_b64 = jwk
                .n
                .ok_or_else(|| anyhow!("Missing 'n' value for RSA JWK"))?;
            let e_b64 = jwk
                .e
                .ok_or_else(|| anyhow!("Missing 'e' value for RSA JWK"))?;

            // Decode base64url modulus and exponent
            let n_bytes = OpensslBackend::decode_base64url(&n_b64)
                .map_err(|e| anyhow!("Failed to decode 'n': {e}"))?;
            let e_bytes = OpensslBackend::decode_base64url(&e_b64)
                .map_err(|e| anyhow!("Failed to decode 'e': {e}"))?;

            let n = BigNum::from_slice(&n_bytes)?;
            let e = BigNum::from_slice(&e_bytes)?;
            let rsa = Rsa::from_public_components(n, e)?;
            Ok(PKey::from_rsa(rsa)?)
        }
        "EC" => {
            let crv = jwk
                .crv
                .ok_or_else(|| anyhow!("Missing 'crv' (curve name) for EC JWK"))?;
            let x_b64 = jwk
                .x
                .ok_or_else(|| anyhow!("Missing 'x' coordinate for EC JWK"))?;
            let y_b64 = jwk
                .y
                .ok_or_else(|| anyhow!("Missing 'y' coordinate for EC JWK"))?;

            // Decode x and y base64url coordinates
            let x_bytes = OpensslBackend::decode_base64url(&x_b64)
                .map_err(|e| anyhow!("Failed to decode 'x': {e}"))?;
            let y_bytes = OpensslBackend::decode_base64url(&y_b64)
                .map_err(|e| anyhow!("Failed to decode 'y': {e}"))?;

            let x = BigNum::from_slice(&x_bytes)?;
            let y = BigNum::from_slice(&y_bytes)?;

            // Select curve by `crv`
            let nid = match crv.as_str() {
                "P-256" => Nid::X9_62_PRIME256V1,
                "P-384" => Nid::SECP384R1,
                "P-521" => Nid::SECP521R1,
                other => return Err(anyhow!("Unsupported EC curve: {}", other)),
            };

            // Build EC public key from (x, y)
            let group = EcGroup::from_curve_name(nid)?;
            let ec_key = EcKey::from_public_key_affine_coordinates(&group, &x, &y)?;
            Ok(PKey::from_ec_key(ec_key)?)
        }

        other => Err(anyhow!("Unsupported key type '{}'", other)),
    }
}

fn verify_key_footer(key: &str, footer: &'static str) -> Result<()> {
    let trimmed = key.trim_end();
    let expected_footer = format!("-----{}-----", footer.trim());

    if trimmed.ends_with(&expected_footer) {
        Ok(())
    } else {
        Err(anyhow!("Extra data after a PEM certificate block"))
    }
}

/// Tries to extract public key from PEM data
/// PEM data could be:
/// - PEM encoded certificate
/// - PEM encoded public key
/// - JWK key (set) used to verify the signature
fn extract_key(pem_data: &str) -> Result<PKey<Public>> {
    // Try parsing PEM encoded certificate
    if let Ok(cert) = X509::from_pem(pem_data.as_bytes()) {
        verify_key_footer(pem_data, "END CERTIFICATE")?;
        return cert.public_key().map_err(|e| anyhow!(e));
    }
    // Try parsing PEM encoded public key
    if let Ok(pubkey) = PKey::public_key_from_pem(pem_data.as_bytes()) {
        verify_key_footer(pem_data, "END PUBLIC KEY")?;
        return Ok(pubkey);
    }
    // Try parsing JWK key (set)
    if let Ok(pubkey) = jwk_to_pkey(pem_data) {
        return Ok(pubkey);
    }
    Err(anyhow!("Unsupported PEM format or invalid data"))
}

fn verify_rsa(
    token: &str,
    certificate: &str,
    hash_fn: MessageDigest,
    padding: Padding,
    is_es: bool,
) -> Result<bool> {
    let public_key = extract_key(certificate)?;

    let (header, payload, signature) = split_token(token)?;
    // Payload to sign: header.payload
    let sign_payload = &token[..header.len() + 1 + payload.len()];
    let mut decoded_signature = OpensslBackend::decode_base64url(signature)?;

    if is_es {
        if decoded_signature.len() % 2 != 0 {
            return Err(anyhow!("Invalid signature length"));
        }
        let half_len = decoded_signature.len() / 2;
        let r = BigNum::from_slice(&decoded_signature[..half_len])?;
        let s = BigNum::from_slice(&decoded_signature[half_len..])?;

        // Convert to DER encoding
        let ecdsa_sig = EcdsaSig::from_private_components(r, s)?;
        decoded_signature = ecdsa_sig.to_der()?;
    }

    // Create verifier
    let mut verifier = Verifier::new(hash_fn, &public_key)?;
    if padding != Padding::NONE {
        verifier.set_rsa_padding(padding)?;
    }
    verifier.update(sign_payload.as_bytes())?;

    // Verify signature
    Ok(verifier.verify(&decoded_signature)?)
}

pub struct OpensslBackend;

impl Backend for OpensslBackend {
    fn encode_base64url(src: &[u8]) -> String {
        let base64_encoded = base64::encode_block(src);
        let mut result = String::with_capacity(base64_encoded.len());
        for c in base64_encoded.chars() {
            match c {
                '+' => result.push('-'),
                '/' => result.push('_'),
                '=' => {}
                other => result.push(other),
            }
        }
        result
    }

    fn decode_base64url(src: &str) -> Result<Vec<u8>> {
        let mut to_decode = src
            .chars()
            .map(|c| match c {
                '-' => '+',
                '_' => '/',
                _ => c,
            })
            .collect::<String>();

        let pad_len = 4 - to_decode.len() % 4;
        if 0 < pad_len && pad_len < 4 {
            to_decode.push_str(&"=".repeat(pad_len));
        }

        let result = base64::decode_block(&to_decode)?;
        Ok(result)
    }

    fn verify_hs256(token: &str, secret: &str) -> Result<bool> {
        verify_hmac(token, secret, MessageDigest::sha256())
    }

    fn verify_hs384(token: &str, secret: &str) -> Result<bool> {
        verify_hmac(token, secret, MessageDigest::sha384())
    }

    fn verify_hs512(token: &str, secret: &str) -> Result<bool> {
        verify_hmac(token, secret, MessageDigest::sha512())
    }

    fn verify_rs256(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha256(),
            Padding::PKCS1,
            false,
        )
    }

    fn verify_rs384(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha384(),
            Padding::PKCS1,
            false,
        )
    }

    fn verify_rs512(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha512(),
            Padding::PKCS1,
            false,
        )
    }

    fn verify_ps256(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha256(),
            Padding::PKCS1_PSS,
            false,
        )
    }

    fn verify_ps384(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha384(),
            Padding::PKCS1_PSS,
            false,
        )
    }

    fn verify_ps512(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha512(),
            Padding::PKCS1_PSS,
            false,
        )
    }

    fn verify_es256(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha256(),
            Padding::NONE,
            true,
        )
    }

    fn verify_es384(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha384(),
            Padding::NONE,
            true,
        )
    }

    fn verify_es512(token: &str, certificate: &str) -> Result<bool> {
        verify_rsa(
            token,
            certificate,
            MessageDigest::sha512(),
            Padding::NONE,
            true,
        )
    }
}
