#!/usr/bin/env bash
# V16: must never report source/numerical checks as a Lean certificate.
set -euo pipefail
cd "$(dirname "$0")"

python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v16_width_grouping.py
# V15's larger exact-model suite is optional; it is expensive and already
# exists unchanged in the repository. Invoke with V16_EXTENDED=1 when needed.
if [[ "${V16_EXTENDED:-0}" == '1' ]]; then
  python3 tools/test_v15_actual_projection_blocks.py
fi

if ! command -v lake >/dev/null 2>&1 || ! command -v lean >/dev/null 2>&1; then
  echo 'V16 SOURCE/MODEL CHECKS PASSED. NO LEAN KERNEL CERTIFICATE (lean/lake unavailable).' >&2
  exit 2
fi

# For a fresh Mathlib checkout, opt in with LEAN_V16_DOWNLOAD_CACHE=1.
if [[ "${LEAN_V16_DOWNLOAD_CACHE:-0}" == '1' ]]; then
  lake exe cache get
fi

lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
printf '\nV16: Lean compiled the imported project. This does NOT prove manuscript Theorem 1.1.\n'
