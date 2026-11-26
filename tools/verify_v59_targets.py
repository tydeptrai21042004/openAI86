#!/usr/bin/env python3
"""Fail-closed source audit and isolated kernel checks for V59."""
from pathlib import Path
import json, re, shutil, subprocess, sys
from lean_lex import code_only
from axiom_report_parser import parse_axioms
ROOT = Path(__file__).resolve().parents[1]
LOCAL = ['source_fidelity/v58/FastFourier.lean',
         'source_fidelity/v58/ShortBlockGeometry.lean',
         'source_fidelity/v59/RadialClipping.lean']
REF = ['external_main_theorem/v59/'+x+'.lean' for x in ['Compression','Weyl','ShortBlock']]
OUT = ROOT/'verification/reports/V59'

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    report = {'full_paper_certified': False, 'independent_main_proved': False,
              'source_audit': 'NOT RUN', 'targets': {}}
    def save():
        (OUT/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    try:
        for f in LOCAL+REF:
            t = code_only((ROOT/f).read_text())
            if re.search(r'\b(sorry|admit|axiom|constant|opaque|unsafe|native_decide)\b', t):
                raise ValueError('Forbidden source in '+f)
            names = re.findall(r'^#print axioms (\S+)\s*$', t, re.M)
            if not names:
                raise ValueError('No axiom targets in '+f)
            for name in names:
                if name in report['targets']:
                    raise ValueError('Duplicate axiom target '+name)
                report['targets'][name] = {'file': f, 'status': 'NOT RUN' if f in LOCAL else 'REFERENCE REPLAY REQUIRED'}
        report['source_audit'] = 'PASS'
        save()
    except (ValueError, OSError) as exc:
        report['source_audit'] = 'FAILED'; report['error'] = str(exc); save(); print(exc); return 1
    print('V59 audited source files:', len(LOCAL)+len(REF), 'exact axiom targets:', len(report['targets']))
    if not shutil.which('lean') or not shutil.which('lake'):
        for e in report['targets'].values():
            if e['file'] in LOCAL:
                e['status'] = 'BLOCKED: Lean/Lake unavailable'
        save()
        print('BLOCKED: Lean/Lake unavailable; zero V59 kernel certificates.')
        return 2
    failed = False
    for f in LOCAL:
        proc = subprocess.run(['lake','env','lean',f],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (OUT/(Path(f).stem+'.log')).write_text(proc.stdout)
        for name,e in report['targets'].items():
            if e['file'] != f: continue
            try:
                if proc.returncode: raise ValueError('Lean exited '+str(proc.returncode))
                e.update(status='KERNEL CHECKED; FIDELITY REVIEW REQUIRED',axioms=sorted(parse_axioms(proc.stdout,name)))
            except ValueError as exc:
                failed=True; e['status']='FAILED: '+str(exc)
        save()
    print('Reference replay is separate: external_main_theorem/v59/verify_bridges.py')
    return int(failed)
if __name__ == '__main__': sys.exit(main())
