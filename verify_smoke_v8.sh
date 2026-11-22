#!/usr/bin/env bash
# Focused V8 checks: finite regression checks are NOT Lean proof certificates.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v7_operator_product_expansion.py
python3 tools/test_v7_catalog_and_increments.py
python3 tools/test_v8_normed_row_bessel.py
python3 tools/test_v8_coarse_prefix_variation.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: Lean kernel was not run. Install pinned Lean/Lake or run the CI workflow.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '%s\n' 'Kernel build passed for authored components; paper Theorem 1.1 remains OPEN.'
