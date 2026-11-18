#!/usr/bin/env python3
"""Non-kernel source lint: never describe its result as proof verification."""
from pathlib import Path
import re, sys, json
root=Path(__file__).resolve().parents[1]
files=sorted(root.rglob('*.lean'))
fail=[]
theorems=[]
for p in files:
    src=p.read_text(encoding='utf-8')
    for idx,line in enumerate(src.splitlines(),1):
        x=line.strip()
        if re.match(r'^(sorry|admit|axiom|constant|opaque|unsafe\s+def)\b',x):
            fail.append(f'{p.relative_to(root)}:{idx}: forbidden declaration/placeholder: {x[:120]}')
        if x.startswith('import '):
            module=x[len('import '):].strip()
            if not (module in ('Mathlib', 'OpenAI086') or module.startswith('Mathlib.') or module.startswith('OpenAI086.')):
                fail.append(f'{p.relative_to(root)}:{idx}: unapproved import: {module}')
        if re.match(r'^theorem\s+',x):
            theorems.append((str(p.relative_to(root)),x))
        if re.match(r'^theorem\s+Theorem1_1_Goal\b',x):
            fail.append(f'{p.relative_to(root)}:{idx}: do not claim main theorem has a proof')
if not (root/'OpenAI086/PaperStatement.lean').exists():
    fail.append('Missing main theorem statement')
text='\n'.join((root/'OpenAI086/PaperStatement.lean').read_text().splitlines())
if not re.search(r'\bdef Theorem1_1_Goal\s*:\s*Prop\b',text):
    fail.append('The main theorem must remain explicitly unproved until a complete proof exists')
print(json.dumps({
    'status':'static_lint_only_not_kernel_verified',
    'lean_file_count':len(files),
    'theorem_declaration_count':len(theorems),
    'theorem_1_1_kernel_proved':False,
    'issues':fail,
},ensure_ascii=False,indent=2))
if fail: sys.exit(1)
