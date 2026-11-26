#!/usr/bin/env python3
"""Replay isolated V58 candidates and audit exact axiom output, fail closed."""
from pathlib import Path
import json,re,shutil,subprocess,sys
from axiom_report_parser import parse_axioms
from lean_lex import code_only
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/reports/V58'
FILES=['source_fidelity/v58/FastFourier.lean','source_fidelity/v58/ShortBlockGeometry.lean']
def main():
    OUT.mkdir(parents=True,exist_ok=True)
    report={'full_paper_certified':False,'independent_main_proved':False,'targets':{}}
    for f in FILES+['external_main_theorem/v58/SparseCount.lean']:
        t=code_only((ROOT/f).read_text())
        if re.search(r'\b(sorry|admit|axiom|constant|opaque|unsafe|native_decide)\b',t):
            raise RuntimeError('Forbidden source in '+f)
        names=re.findall(r'^#print axioms (\S+)\s*$',t,re.M)
        if not names: raise RuntimeError('No axiom targets in '+f)
        for n in names:
            report['targets'][n]={'file':f,'status':'REFERENCE REPLAY REQUIRED' if f not in FILES else 'NOT RUN'}
    def save(): (OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    if not shutil.which('lake') or not shutil.which('lean'):
        for e in report['targets'].values():
            if e['file'] in FILES:e['status']='BLOCKED: Lean/Lake unavailable'
        save(); print('BLOCKED: Lean/Lake unavailable; zero V58 kernel certificates.');return 2
    failed=False
    for f in FILES:
        p=subprocess.run(['lake','env','lean',f],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (OUT/(Path(f).stem+'.log')).write_text(p.stdout)
        for n,e in report['targets'].items():
            if e['file']!=f:continue
            try:
                if p.returncode: raise ValueError(f'Lean exited {p.returncode}')
                e.update(status='KERNEL CHECKED; paper fidelity review required',axioms=sorted(parse_axioms(p.stdout,n)))
            except ValueError as ex:e['status']='FAILED: '+str(ex);failed=True
        save()
    print('Reference sparse-count replay is separate; run external_main_theorem/v58/verify_sparse.py.')
    return int(failed)
if __name__=='__main__':sys.exit(main())
