#!/usr/bin/env bash
# V10: focus on genuine manuscript-connected intermediate results.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v10_two_axis.py
python3 tools/test_v9_height_lag.py
python3 tools/test_errata_regression.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'SOURCE AND NUMERIC TESTS PASS; Lean/Lake not installed: NO KERNEL CERTIFICATE' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '\nV10 Lean entrypoint compiled; paper Theorem 1.1 remains OPEN.\n'
