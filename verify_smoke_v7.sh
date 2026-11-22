#!/usr/bin/env bash
# V7 targeted checks. All Python passes are NON-CERTIFICATES.
# Exit 2 means the Lean kernel was not run.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v7_operator_product_expansion.py
python3 tools/test_v7_catalog_and_increments.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake not available. Python tests cannot certify Lean proofs.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '%s\n' 'Lean kernel accepted authored module proofs; numbered article theorems remain open.'
