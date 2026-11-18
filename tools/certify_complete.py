#!/usr/bin/env python3
"""Honest final theorem gate: fail unless an independent proof is present.

This script is deliberately NOT a replacement for Lean kernel verification.
When a proof is eventually supplied, run `lake build` before using it.
"""
import json,sys
from pathlib import Path
root=Path(__file__).resolve().parents[1]
status=json.loads((root/'STATUS.json').read_text())
if not status['main_theorem_1_1_proved']:
    print('NOT CERTIFIED: OpenAI #086 Theorem 1.1 still lacks an independent Lean proof.')
    print('See PROOF_TRACEABILITY.md and PaperStatement.lean')
    sys.exit(1)
print('Manifest says proved. This alone is NOT certification; run Lean kernel checks.')
sys.exit(1)
