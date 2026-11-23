#!/usr/bin/env bash
# V17: source/numerical checks and a separate mandatory Lean kernel gate.
# Exit 0: the checked code was actually compiled by the pinned Lean toolchain.
# Exit 2: source/model tests passed, but no Lean/Lake toolchain was available.
# Any other nonzero exit: an audit, mathematical model, or build failed.
set -euo pipefail
cd "$(dirname "$0")"

python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
V17_FAST=1 python3 tools/test_v17_actual_selected_width.py

if [[ "${V17_EXTENDED:-0}" == '1' ]]; then
  python3 tools/test_v17_actual_selected_width.py
  python3 tools/test_v16_width_grouping.py
  python3 tools/test_v15_actual_projection_blocks.py
fi

if ! command -v lake >/dev/null 2>&1 || ! command -v lean >/dev/null 2>&1; then
  echo 'V17 SOURCE/MODEL AUDITS PASSED. LEAN KERNEL COMPILATION UNAVAILABLE.' >&2
  exit 2
fi
if [[ "${LEAN_V17_DOWNLOAD_CACHE:-0}" == '1' ]]; then
  lake exe cache get
fi
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
echo 'V17 Lean entrypoint compiled. THIS IS NOT a proof of manuscript Theorem 1.1.'
