#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_independent_target.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v47_verifier.py
python3 tools/test_v47_models.py
if command -v lake >/dev/null && command -v lean >/dev/null; then
  if [[ ! -f lake-manifest.json ]]; then lake update; fi
  lake exe cache get
fi
python3 tools/verify_v47_targets.py "$@"
