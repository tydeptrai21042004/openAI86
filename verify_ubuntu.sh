#!/usr/bin/env bash
# Ubuntu/WSL: fail closed unless the real Lean kernel build is available.
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1; then
  echo 'Lean/Lake is required; install elan (https://github.com/leanprover/elan).' >&2
  echo 'Then open a new shell or run: source "$HOME/.elan/env"' >&2
  exit 2
fi
# Use a project-local venv only when numpy/sympy are missing. This avoids the
# PEP 668 externally-managed Python environment error on modern Ubuntu.
if ! python3 -c 'import numpy, sympy' >/dev/null 2>&1; then
  python3 -m venv .venv
  .venv/bin/python -m pip install numpy sympy
  export PATH="$PWD/.venv/bin:$PATH"
fi
# The project's pinned Mathlib revision remains in lakefile.toml.
lake update
bash verify_all.sh
