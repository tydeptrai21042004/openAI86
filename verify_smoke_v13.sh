#!/usr/bin/env bash
# Independent V13 source/numeric checks; successful Lean build mandatory for certification.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v13_chronological_rank.py
python3 tools/test_v12_exact_log_chain.py
python3 tools/test_v11_paper_bridges.py
python3 tools/test_v10_two_axis.py
python3 tools/test_v9_height_lag.py
python3 tools/test_errata_regression.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'V13 source/finite regressions passed; NO Lean/Lake: KERNEL CERTIFICATION UNAVAILABLE' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '\nV13 Lean source compiled. Complete paper proofs remain open.\n'
