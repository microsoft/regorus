#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
DEMO_DIR="$ROOT_DIR/causality-demo"
PORT="${REGORUS_DEMO_PORT:-8000}"
PYTHON_BIN="${PYTHON_BIN:-$ROOT_DIR/.venv/bin/python}"

if [[ ! -x "$PYTHON_BIN" ]]; then
  PYTHON_BIN="$(command -v python3)"
fi

if [[ -z "$PYTHON_BIN" ]]; then
  echo "python3 is required to run the demo" >&2
  exit 1
fi

"$DEMO_DIR/build-demo.sh"

echo "Starting static demo server on http://127.0.0.1:$PORT"
if command -v open >/dev/null 2>&1; then
  (sleep 1; open "http://127.0.0.1:$PORT") &
fi

cd "$DEMO_DIR"
exec "$PYTHON_BIN" -m http.server "$PORT" --bind 127.0.0.1