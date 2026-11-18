#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1; then
  echo "ERROR: Lean/lake not installed; this candidate is NOT certified" >&2
  exit 2
fi
lake exe cache get
lake build
lake env lean OpenAI086/Lemma33Reviewed.lean
lake env lean OpenAI086/Lemma33Check.lean
printf '%s\n' 'Candidate compiled and checked. Inspect printed axiom dependencies.'
