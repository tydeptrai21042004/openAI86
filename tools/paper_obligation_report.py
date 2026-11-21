#!/usr/bin/env python3
"""Conservative register for every numbered result of the 93-page paper.

This is a source inventory; it never treats textual flags or numeric tests as
kernel proof certificates. The strict report calls the independently compiled
exact-theorem gate if (and only if) all inventory entries are attested.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'verification/PAPER_RESULTS_INDEX.json'
p = argparse.ArgumentParser()
p.add_argument('--require-complete', action='store_true')
a = p.parse_args()

items = json.loads(MANIFEST.read_text(encoding='utf-8'))['results']
assert len(items) == 59, f'expected 59 individually numbered results, got {len(items)}'
keys = [(x['kind'], x['number']) for x in items]
assert len(set(keys)) == len(keys), 'duplicate named paper result'
partial = [x for x in items if x['formalization'] == 'partial']
full = [x for x in items if x['formalization'] == 'full_kernel_verified']
# These attestations are human-reviewed pointers to a theorem *and* a kernel
# build log. They are necessary, not sufficient, for strict certification.
evidenced = [x for x in full if x.get('lean_constant') and x.get('certificate_log')]
status = {
  'paper_results_total': len(items),
  'results_with_some_relevant_local_lean': len(partial),
  'paper_results_claiming_full_kernel_proofs': len(full),
  'full_results_with_certificate_references': len(evidenced),
  'main_theorem_kernel_verified_by_this_report': False,
  'completeness': 'INCOMPLETE' if len(evidenced) < 59 else 'EVIDENCE_REQUIRES_EXACT_THEOREM_GATE',
  'interpretation': 'Manifest entries are never proof certificates; the actual Lean build is required.'
}
print(json.dumps(status, ensure_ascii=False, indent=2))
if a.require_complete:
  if len(evidenced) != 59:
    print('FAIL: missing individually attested Lean proofs for all 59 results.')
    sys.exit(3)
  # This additional gate requires and builds the exact local principal-value
  # theorem; it does not blindly accept a populated manifest.
  res = subprocess.run([sys.executable, 'tools/certify_complete.py'], cwd=ROOT)
  sys.exit(res.returncode)
