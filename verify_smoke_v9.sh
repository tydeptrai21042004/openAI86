#!/usr/bin/env bash
# V9 regression + source audit. Kernel build remains mandatory for certification.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v9_height_lag.py
python3 tools/test_errata_regression.py
python3 tools/test_v8_normed_row_bessel.py
python3 tools/test_v8_coarse_prefix_variation.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: pinned Lean/Lake absent; static/numeric checks are not kernel proofs.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
echo 'Independent components compiled. Theorem 1.1 remains open in this repository.'
