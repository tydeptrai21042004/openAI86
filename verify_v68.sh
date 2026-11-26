#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
exec python3 tools/verify_final.py --strict-axioms "$@"
