#!/usr/bin/env bash
# V11: source audits + exact finite regressions, followed by kernel build if installed.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v11_paper_bridges.py
python3 tools/test_v10_two_axis.py
python3 tools/test_v9_height_lag.py
python3 tools/test_errata_regression.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'V11 source/numeric audits passed; Lean/Lake unavailable: KERNEL BUILD NOT VERIFIED' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '\nV11 entrypoint compiled by Lean; named paper result completion remains independent of this build.\n'
