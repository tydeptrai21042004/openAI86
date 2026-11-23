#!/usr/bin/env bash
# V15: static + exact rational model checks, THEN mandatory Lean kernel build.
# WARNING: source tests are NEVER a substitute for `lake build`.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v15_actual_projection_blocks.py
python3 tools/test_v14_full_height.py
python3 tools/test_v13_chronological_rank.py
python3 tools/test_v12_exact_log_chain.py
python3 tools/test_v11_paper_bridges.py
python3 tools/test_v10_two_axis.py
python3 tools/test_v9_height_lag.py
python3 tools/test_errata_regression.py
if ! command -v lake >/dev/null 2>&1 || ! command -v lean >/dev/null 2>&1; then
  echo 'V15 static and exact-model tests passed, but Lean/Lake are unavailable. NO KERNEL CERTIFICATE.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '\nV15 Lean entrypoint compiled. Manuscript Theorem 1.1 still open.\n'
