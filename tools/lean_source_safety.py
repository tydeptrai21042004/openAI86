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
from independent_sources import independent_sources, LEGACY
FILES=independent_sources(ROOT)

# A lexer sufficient for nested Lean block comments, `--` line comments,
# and escaped double-quoted strings. Newlines are retained for diagnostics.
from lean_lex import code_only

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
                  'violations':violations,'safe':not violations,
                  'preserved_legacy_not_in_independent_scan':[x for x in LEGACY if (ROOT/x).is_file()]},indent=2))
if violations:sys.exit(1)
