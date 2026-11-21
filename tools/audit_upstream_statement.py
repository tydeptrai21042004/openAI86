#!/usr/bin/env python3
"""Extract, rather than assume, the upstream theorem/operator statement.

This is a provenance guard, not a mathematical equivalence proof.
"""
import json,sys,re
from pathlib import Path


def main():
    if len(sys.argv)!=3:
        raise SystemExit('Usage: audit_upstream_statement.py UPSTREAM_PATH OUTPUT_JSON')
    repo=Path(sys.argv[1]); out=Path(sys.argv[2]);out.parent.mkdir(parents=True,exist_ok=True)
    defs=(repo/'TrilinearHT/Defs.lean').read_text(encoding='utf8')
    theorems=(repo/'TrilinearHT/Theorems.lean').read_text(encoding='utf8')
    patterns={
      'T_trunc_definition':(defs,r'(?m)^\s*(?:noncomputable\s+)?def\s+T_trunc\b'),
      'T_definition':(defs,r'(?m)^\s*(?:noncomputable\s+)?def\s+T\b'),
      'main_theorem':(theorems,r'(?m)^\s*theorem\s+trilinear_ht_bound\b'),
    }
    result={'status':'source_statement_extraction_only_NOT_an_equivalence_proof', 'entries':{}}
    for key,(body,pat) in patterns.items():
        match=re.search(pat,body)
        if match is None: raise SystemExit(f'FAIL: missing {key}')
        # Capture context for a human to compare to PDF before claiming equivalence.
        result['entries'][key]=body[match.start():match.start()+2200]
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
    print(f'PASS: extracted declarations from upstream to {out} (no equivalence proven)')

if __name__=='__main__': main()
