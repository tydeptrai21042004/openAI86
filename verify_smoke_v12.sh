#!/usr/bin/env bash
# Independent V12 candidate source/numeric checks; kernel pass is mandatory for certification.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v12_exact_log_chain.py
python3 tools/test_v11_paper_bridges.py
python3 tools/test_v10_two_axis.py
python3 tools/test_v9_height_lag.py
python3 tools/test_errata_regression.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'V12 source and finite regression checks passed, but Lean/Lake is unavailable; KERNEL BUILD NOT VERIFIED' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '\nLean kernel build completed. Full paper result certification remains a separate task.\n'
