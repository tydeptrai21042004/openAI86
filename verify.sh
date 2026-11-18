#!/usr/bin/env bash
# Standard entrypoint checks the ENTIRE project.
set -euo pipefail
cd "$(dirname "$0")"
exec bash ./verify_all.sh
