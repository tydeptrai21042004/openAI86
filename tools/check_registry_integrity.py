#!/usr/bin/env python3
"""Consistency checks for the manuscript-result inventory and status metadata.

This checks bookkeeping, not correctness of any Lean proof.
"""
import json
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
source = json.loads((root/'verification/PAPER_RESULTS_INDEX.json').read_text(encoding='utf-8'))
items = source['results']
status = json.loads((root/'STATUS.json').read_text(encoding='utf-8'))
files = sorted((root/'OpenAI086').glob('*.lean'))
theorems = sum(bool(re.match(r'^\s*theorem\s+', line)) for path in files for line in path.read_text(encoding='utf-8').splitlines())
errors=[]

if len(items) != 59:
    errors.append(f'expected 59 indexed results, got {len(items)}')
if len({(x['kind'],x['number']) for x in items}) != len(items):
    errors.append('repeated numbered result keys')
for item in items:
    key = item.get('kind','?') + ' ' + item.get('number','?')
    if not isinstance(item.get('pdf_page'), int) or not (1 <= item['pdf_page'] <= 93):
        errors.append(f'{key}: invalid PDF page')
    if item.get('formalization') not in {'open', 'partial', 'full_kernel_verified'}:
        errors.append(f'{key}: invalid formalization value')
    if item.get('kernel_verified') and item.get('formalization') != 'full_kernel_verified':
        errors.append(f'{key}: inconsistent kernel_verification flag')
    for path in item.get('relevant_modules',[]):
        if not (root/path).is_file():
            errors.append(f'{key}: nonexistent referenced Lean file {path}')
    if item.get('formalization') == 'full_kernel_verified':
        if not item.get('lean_constant') or not item.get('certificate_log'):
            errors.append(f'{key}: proof completion lacks theorem/certificate reference')

if status.get('root_lean_file_count') != len(files) + 2:
    errors.append('STATUS.json Lean file count is stale')
if status.get('theorem_declarations_in_source') != theorems:
    errors.append(f'STATUS.json theorem count stale: {status.get("theorem_declarations_in_source")} vs {theorems}')
if status.get('numbered_results_with_partial_components') != sum(x['formalization']=='partial' for x in items):
    errors.append('STATUS.json partial-results count is stale')
if status.get('theorem_1_1_proved') and not (root/'OpenAI086/MainProof.lean').is_file():
    errors.append('Main theorem marked proved without a proof file')

result = {'kind':'source_inventory_not_kernel_certificate',
          'lean_files':len(files)+2,'theorem_declarations':theorems,
          'paper_results':len(items),'errors':errors}
print(json.dumps(result,indent=2))
if errors:sys.exit(1)
