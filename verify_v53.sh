#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_registry_integrity.py
python3 tools/check_independent_target.py
python3 tools/check_all_59_lean_targets.py
python3 tools/lean_source_safety.py
python3 tools/test_v52_components.py
python3 tools/test_v53_components.py
python3 tools/test_axiom_report_parser.py
python3 tools/verify_v53_targets.py
