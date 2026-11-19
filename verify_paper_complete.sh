#!/usr/bin/env bash
# Independent-only completion gate; fails until an independent main proof exists.
set -euo pipefail
cd "$(dirname "$0")"
bash verify_all.sh
python3 tools/paper_obligation_report.py --require-complete
python3 tools/certify_complete.py
