#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
WASM_DIR="$ROOT_DIR/bindings/wasm"
DEMO_PKG_DIR="$ROOT_DIR/causality-demo/pkg"

if ! command -v wasm-pack >/dev/null 2>&1; then
  echo "wasm-pack is required. Install it with: cargo install wasm-pack" >&2
  exit 1
fi

echo "Building browser wasm package into causality-demo/pkg"
mkdir -p "$DEMO_PKG_DIR"
cd "$WASM_DIR"
wasm-pack build --target web --release --out-dir ../../causality-demo/pkg