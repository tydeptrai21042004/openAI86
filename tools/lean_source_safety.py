#!/usr/bin/env python3
"""Lexical safety scan of the independent Lean files (NOT a kernel check).

Unlike line-anchored source scans, this catches `by sorry`, inline `admit`,
constant/axiom declarations, and unsafe native evaluation in proof bodies.
Comments and string literals are ignored. A trusted-axiom certificate
still requires `#print axioms` after a successful Lake build.
"""
from pathlib import Path
import re, sys, json
ROOT=Path(__file__).resolve().parents[1]
FILES=sorted((ROOT/'OpenAI086').rglob('*.lean'))+[ROOT/'OpenAI086.lean',ROOT/'OpenAI086Whole.lean']

# A lexer sufficient for nested Lean block comments, `--` line comments,
# and escaped double-quoted strings. Newlines are retained for diagnostics.
def code_only(src):
    out=[]; i=0; block=0; string=False; line=False
    while i<len(src):
        if src[i]=='\n':
            line=False; out.append('\n'); i+=1; continue
        if line:
            out.append(' ');i+=1;continue
        if block:
            if src[i:i+2]=='/-': block+=1;out.extend('  ');i+=2;continue
            if src[i:i+2]=='-/': block-=1;out.extend('  ');i+=2;continue
            out.append(' ');i+=1;continue
        if string:
            if src[i]=='\\':out.extend('  ');i+=2;continue
            if src[i]=='"':string=False
            out.append(' ');i+=1;continue
        if src[i:i+2]=='/-':block=1;out.extend('  ');i+=2;continue
        if src[i:i+2]=='--':line=True;out.extend('  ');i+=2;continue
        if src[i]=='"':string=True;out.append(' ');i+=1;continue
        out.append(src[i]);i+=1
    if block or string:raise ValueError('unterminated Lean block comment or string')
    return ''.join(out)

violations=[]
pattern=re.compile(r'\b(sorry|admit|axiom|constant|opaque|unsafe|native_decide)\b')
for path in FILES:
    try:clean=code_only(path.read_text('utf-8'))
    except Exception as ex:violations.append(f'{path.name}: {ex}');continue
    for m in pattern.finditer(clean):
        line=clean.count('\n',0,m.start())+1
        violations.append(f'{path.relative_to(ROOT)}:{line}: {m.group(0)}')
    if re.search(r'(?m)^\s*import\s+TrilinearHT\b',clean):
        violations.append(f'{path.name}: external published proof import')
print(json.dumps({'status':'source_scan_not_kernel_check','files':len(FILES),
                  'violations':violations,'safe':not violations},indent=2))
if violations:sys.exit(1)
