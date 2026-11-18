#!/usr/bin/env bash
# Full Lean project: fail if ANY part, including the Lemma 3.3 candidate, fails.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/static_audit.py
python3 tools/sympy_check.py
python3 tools/test_noncommuting_numeric.py
python3 tools/test_lemma33_numeric.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake not installed. Lean kernel build was not run.' >&2
  echo 'Install elan/Lean on Ubuntu or use the included GitHub Actions workflow.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
lake env lean OpenAI086/Lemma33Check.lean
echo 'KERNEL BUILD COMPLETE for authored theorems. Theorem 1.1 remains UNPROVED.'
