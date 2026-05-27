// Copyright (c) Microsoft Corporation.
// Licensed under the MIT License.

// Self-contained share-link encoding for the demo playground.
//
// Design constraints:
//   - The site is fully static (GitHub Pages); no server can store state.
//   - The shared state must round-trip through a URL the user can copy.
//   - Pasted policies may contain secrets, so we put the payload in the URL
//     fragment (`#`) — fragments are never sent to the server in HTTP
//     requests, never end up in server logs, and don't trigger a reload
//     when updated via history.replaceState.
//   - Modern browsers expose `CompressionStream`/`DecompressionStream`, so
//     we can ship gzip without bundling pako.  We feature-detect and fall
//     back to plain base64 on the (vanishing) old-browser path.
//
// Wire format:
//   #s=<version-byte><base64url(gzip(JSON))>
//
//   version-byte: a single literal character preceding the encoded payload
//                 so we can evolve the format without breaking old links.
//                 - "1" → gzip + base64url
//                 - "0" → raw  + base64url   (fallback)
//
// The payload is a JSON object with the playground state — see
// SHARE_STATE_KEYS for the exact contract.

const HASH_PREFIX = "s=";
const VERSION_GZIP = "1";
const VERSION_PLAIN = "0";

const SHARE_STATE_KEYS = [
    "policy",
    "input",
    "data",
    "query",
    "evalMode",
    "unknowns",
    "whyBindings",
    "whyFullValues",
    "whyAllConditions",
    "whyAssumeUnknown",
    "detail",
];

function pickKnownFields(state) {
    const out = {};
    for (const key of SHARE_STATE_KEYS) {
        if (state[key] !== undefined && state[key] !== null) {
            out[key] = state[key];
        }
    }
    return out;
}

function toBase64Url(bytes) {
    let bin = "";
    for (let i = 0; i < bytes.length; i++) {
        bin += String.fromCharCode(bytes[i]);
    }
    return btoa(bin)
        .replace(/\+/g, "-")
        .replace(/\//g, "_")
        .replace(/=+$/, "");
}

function fromBase64Url(token) {
    const padded = token.replace(/-/g, "+").replace(/_/g, "/");
    const bin = atob(padded);
    const out = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) {
        out[i] = bin.charCodeAt(i);
    }
    return out;
}

async function gzipCompress(text) {
    if (typeof CompressionStream === "undefined") {
        return null;
    }
    const stream = new Blob([text]).stream().pipeThrough(new CompressionStream("gzip"));
    const buf = await new Response(stream).arrayBuffer();
    return new Uint8Array(buf);
}

async function gzipDecompress(bytes) {
    if (typeof DecompressionStream === "undefined") {
        return null;
    }
    const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream("gzip"));
    return await new Response(stream).text();
}

/**
 * Encode a state object into a URL fragment token.
 *
 * Returns a string like `"s=1H4sIA..."`, suitable for assignment to
 * `location.hash`.  Use `buildShareUrl` if you want a full URL.
 */
export async function encodeShareToken(state) {
    const json = JSON.stringify(pickKnownFields(state));
    const compressed = await gzipCompress(json);
    if (compressed) {
        return `${HASH_PREFIX}${VERSION_GZIP}${toBase64Url(compressed)}`;
    }
    // Fallback: plain base64url of the JSON bytes.
    const utf8 = new TextEncoder().encode(json);
    return `${HASH_PREFIX}${VERSION_PLAIN}${toBase64Url(utf8)}`;
}

/**
 * Build a full shareable URL for the current page using the supplied state.
 */
export async function buildShareUrl(state) {
    const token = await encodeShareToken(state);
    return `${location.origin}${location.pathname}#${token}`;
}

/**
 * Decode a fragment value (everything after the leading `#`) back into the
 * state object, or return `null` if the fragment isn't a recognized share
 * token.  Throws if the token is recognized but malformed.
 */
export async function decodeShareFragment(fragment) {
    if (!fragment || !fragment.startsWith(HASH_PREFIX)) {
        return null;
    }
    const body = fragment.slice(HASH_PREFIX.length);
    if (body.length === 0) {
        return null;
    }
    const version = body[0];
    const payload = body.slice(1);
    const bytes = fromBase64Url(payload);

    let json;
    if (version === VERSION_GZIP) {
        json = await gzipDecompress(bytes);
        if (json === null) {
            throw new Error(
                "This link was produced with gzip compression, but your browser doesn't expose DecompressionStream."
            );
        }
    } else if (version === VERSION_PLAIN) {
        json = new TextDecoder().decode(bytes);
    } else {
        throw new Error(`Unsupported share-link version: '${version}'`);
    }

    return JSON.parse(json);
}

/**
 * Convenience: read the current location's fragment and decode it.
 * Returns `null` when there's nothing to load.
 */
export async function loadStateFromLocation() {
    const frag = location.hash.startsWith("#") ? location.hash.slice(1) : location.hash;
    return decodeShareFragment(frag);
}

/**
 * Write a token into `location.hash` without triggering a navigation.
 */
export function writeShareTokenToLocation(token) {
    const newUrl = `${location.pathname}${location.search}#${token}`;
    history.replaceState(null, "", newUrl);
}
