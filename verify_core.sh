#!/usr/bin/env bash
# Build only the independent core library.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/static_audit.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake not installed.' >&2
  exit 2
fi
lake exe cache get
lake env lean OpenAI086.lean
echo 'Independent core entrypoint elaborated. Main theorem remains unproved.'
