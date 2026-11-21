#!/usr/bin/env bash
# Candidate proofs are intentionally not imported by the main project.
# Exit 2 if compilation is unavailable, 1 on a genuine Lean failure, 0 only
# when BOTH analytic sign/limit bridge candidates have compiled.
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED (exit 2): Lean/Lake is absent; no bridge proof was checked.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean verification/candidates/IntegralSignBridge.lean
lake env lean verification/candidates/PrincipalValueSignTransfer.lean
printf 'Both bridge candidates compiled; review their axiom reports before merging.\n'
printf 'IMPORTANT: the plus-shift L3 bound and the bounded extension are NOT proved locally.\n'

# The sign-invariance candidate is independent of the previous two.
if command -v lake >/dev/null 2>&1; then
  echo 'Checking L1 sign-norm candidate (experimental)'
  lake env lean verification/candidates/NormSignBridge.lean
fi

# A third candidate discharges a purely functional-analytic norm-symmetry
# hypothesis in the conditional main transfer.
lake env lean verification/candidates/TransferWithNormSymmetry.lean

# Candidate: positive epsilon is sufficient (no unnecessary global sign hypothesis).
lake env lean verification/candidates/PositiveCutoffTransfer.lean

# Additional finite-interval integrability candidate (explicit measurability hypothesis).
lake env lean verification/candidates/LocalIntegrabilityBridge.lean
