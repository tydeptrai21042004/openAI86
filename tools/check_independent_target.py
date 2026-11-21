#!/usr/bin/env python3
"""Fail-closed static target guard; deliberately NOT proof verification."""
from pathlib import Path
import hashlib,json,re,sys
ROOT=Path(__file__).resolve().parents[1]
lock=json.loads((ROOT/'verification/TARGET_STATEMENT_LOCK.json').read_text())
target=ROOT/lock['file']
assert target.exists(), 'Theorem statement file removed'
actual=hashlib.sha256(target.read_bytes()).hexdigest()
assert actual==lock['sha256'], 'Exact Theorem 1.1 statement was modified!'
text=target.read_text()
for s in ('def Theorem1_1_Goal : Prop :=',
          '∀ f : Fin 3 → SchwartzMap ℝ ℂ',
          '∀ x : ℝ',
          'Tendsto (fun ε : ℝ => truncHilbert',
          'eLpNorm Tf 1 ≤',
          '∏ i : Fin 3, eLpNorm (f i) 3'):
    assert s in text, f'Required semantic marker missing: {s}'
# Avoid bringing in any upstream proof file or transparent theorem import.
lean=list((ROOT/'OpenAI086').glob('*.lean'))+[ROOT/'OpenAI086.lean',ROOT/'OpenAI086Whole.lean']
for source in lean:
    code=source.read_text()
    assert not re.search(r'(?m)^\s*import\s+TrilinearHT\b',code), source.name
    assert not re.search(r'(?m)^\s*import\s+Auto\b',code), source.name
    assert not re.search(r'(?m)^\s*import\s+TrilinearHT\.Auto\b',code),source.name
print(json.dumps({'status':'source_lock_and_no_upstream_import_pass','target_sha256':actual,
                 'lean_files':len(lean), 'is_kernel_proof':False},indent=2))
