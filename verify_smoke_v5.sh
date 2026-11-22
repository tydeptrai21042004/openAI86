#!/usr/bin/env bash
# Fast V5 smoke test. No kernel success claim unless Lake actually builds.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/lean_source_safety.py
python3 tools/test_v5_adaptive_noncommuting.py
python3 tools/test_v5_dyadic_prefix.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake not found, Lean kernel was NOT executed.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
echo 'Source component kernel build completed. Main Theorem 1.1 is STILL OPEN.'
