#!/usr/bin/env bash
# V6: source + exact-number tests, then real kernel if Lake is installed.
# Exit code 2 means KERNEL NOT RUN; it is never a theorem certificate.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_independent_target.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v6_finite_bridges.py
python3 tools/test_v5_adaptive_noncommuting.py
python3 tools/test_v5_dyadic_prefix.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake not found; no Lean kernel verification was performed.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
echo 'Kernel build succeeded for the source components; main paper theorem remains OPEN.'
