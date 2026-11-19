#!/usr/bin/env python3
"""Conservative independent-proof obligation register for the 93-page manuscript.

This script never marks a mathematical result complete on the basis of a
source-code match. `--require-complete` fails unless a separately recorded
Lean-kernel certificate exists for each of the 59 named results AND Theorem 1.1.
"""
import argparse
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
MANIFEST=ROOT/'verification/PAPER_RESULTS_INDEX.json'

p=argparse.ArgumentParser()
p.add_argument('--require-complete',action='store_true')
a=p.parse_args()

items=json.loads(MANIFEST.read_text(encoding='utf-8'))['results']
assert len(items)==59, f'expected 59 uniquely named results, got {len(items)}'
keys=[(x['kind'],x['number']) for x in items]
assert len(set(keys))==len(keys)
known=[x for x in items if x['formalization']=='partial']
complete=[x for x in items if x['formalization']=='full_kernel_verified']
status={'paper_results_total':len(items),
        'results_with_some_relevant_local_lean':len(known),
        'paper_results_with_full_kernel_verified_independent_proofs':len(complete),
        'main_theorem_kernel_verified':False,
        'independence':'no TrilinearHT imports in OpenAI086 library',
        'interpretation':'No entry is marked complete without kernel evidence',
        'completeness': 'INCOMPLETE'}
print(json.dumps(status,ensure_ascii=False,indent=2))
if a.require_complete:
    print('FAIL: missing kernel-checked proofs of the full analytic paper.')
    raise SystemExit(3)
