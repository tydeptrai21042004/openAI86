#!/usr/bin/env python3
"""Static packaging/import validation only, not Lean theorem certification."""
from pathlib import Path
import re,sys,json
root=Path(__file__).resolve().parents[1]
lean_files=sorted(root.rglob('*.lean'))
imports={}; errors=[]
for path in lean_files:
    mod='.'.join(path.relative_to(root).with_suffix('').parts)
    modules=[]
    for line in path.read_text(encoding='utf-8').splitlines():
        m=re.match(r'^\s*(?:public\s+)?import\s+(\S+)',line)
        if m:
            dep=m.group(1)
            modules.append(dep)
            if dep=='Mathlib' or dep.startswith('Mathlib.'):
                continue
            if not (root / (dep.replace('.','/')+'.lean')).is_file():
                errors.append(f'{mod}: missing local import {dep}')
    imports[mod]=modules
if 'OpenAI086Whole' not in imports:
    errors.append('Missing whole-project entrypoint')
if 'OpenAI086' not in imports:
    errors.append('Missing core entrypoint')
if 'OpenAI086.Lemma33Reviewed' not in imports:
    errors.append('Missing Lemma 3.3 reviewed candidate')
if 'OpenAI086.Lemma33Check' not in imports:
    errors.append('Missing candidate check module')
if imports.get('OpenAI086Whole',[]) != ['OpenAI086','OpenAI086.Lemma33Check']:
    errors.append('Whole-project entrypoint must import core and Lemma33Check')
seen=set()
def reach(mod):
    if mod in seen:return
    seen.add(mod)
    for dep in imports.get(mod,[]):
        if dep in imports: reach(dep)
reach('OpenAI086Whole')
not_reached=sorted(set(imports)-seen)
if not_reached:
    errors.append('Unreachable Lean modules from OpenAI086Whole: '+', '.join(not_reached))
main=(root/'OpenAI086/PaperStatement.lean').read_text(encoding='utf-8')
if not re.search(r'\bdef\s+Theorem1_1_Goal\s*:\s*Prop\b', main):
    errors.append('Theorem 1.1 must remain explicitly an unproved proposition')
result={'status':'static_packaging_audit_not_a_kernel_proof',
        'file_count':len(lean_files),'whole_project_reaches_all_lean_files':not not_reached,
        'unreachable':not_reached,'errors':errors}
print(json.dumps(result,indent=2))
if errors:sys.exit(1)
