#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_independent_target.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/static_audit.py
for test in test_v30_inverse test_v31_math test_v36_exact_windows test_v37_compression test_v40_sparse_graph; do
  python3 "tools/$test.py"
done
if ! command -v lake >/dev/null || ! command -v lean >/dev/null; then
  python3 tools/verify_v41_targets.py
  exit 2
fi
if [[ ! -f lake-manifest.json ]]; then lake update; fi
lake exe cache get
python3 tools/verify_v41_targets.py
