#!/usr/bin/env python3
"""Verify actual paper-facing candidates, never promote them on a static scan."""
from pathlib import Path
import json, shutil, subprocess, sys
from axiom_report_parser import parse_axioms
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/reports/V56'
MODULES={
 'PaperV43Packing':['v43_lemma31'],
 'PaperV56Lemma32':['v56_private_column_norm_sq','v56_private_column_memLp','v56_lemma32'],
 'PaperV43Lemma33':['v43_lemma33'],
 'PaperV41Section3':['v41_scalar_height_assembly','v41_height_bin_explicit'],
 'PaperV42HeightCounterexample':['v42_actual_height_obstruction'],
 'PaperV56ExceptionalBlocks':['v56_packet_exceptional_count','v56_primary_exceptional_blocks'],
 'ChronologicalHarmonic':['chronological_exception_fraction_harmonic'],
}
ADAPTED='OpenAI086.AdaptedV56.v56_lemma85'
def main():
    OUT.mkdir(parents=True,exist_ok=True)
    report={'full_paper_certified':False,'independent_main_proved':False,'targets':{}}
    for module,names in MODULES.items():
        for name in names:
            report['targets']['OpenAI086.'+name]={'module':'OpenAI086.'+module,'origin':'local','status':'NOT RUN'}
    report['targets'][ADAPTED]={'module':'source_fidelity/v56/EntryRank.lean','origin':'attributed adapted source','status':'NOT RUN'}
    def save(): (OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(cmd,filename):
        p=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (OUT/filename).write_text(p.stdout);return p
    if not shutil.which('lake') or not shutil.which('lean'):
        for e in report['targets'].values(): e['status']='BLOCKED: Lean/Lake unavailable'
        save();print('BLOCKED: Lean/Lake unavailable. No proof certified.');return 2
    # The adapted standalone lemma does not need the independent project to build.
    p=run(['lake','env','lean','source_fidelity/v56/EntryRank.lean'],'adapted_85.log')
    try:
        if p.returncode: raise ValueError('Lean returned '+str(p.returncode))
        report['targets'][ADAPTED].update(status='KERNEL CHECKED; statement fidelity review required',axioms=sorted(parse_axioms(p.stdout,ADAPTED)))
    except ValueError as exc: report['targets'][ADAPTED]['status']='FAILED: '+str(exc)
    save()
    p=run(['lake','build','OpenAI086Whole'],'build.log')
    if p.returncode:
        for n,e in report['targets'].items():
            if n!=ADAPTED: e['status']='BLOCKED: whole-project build failed'
        save();print('Whole-project build failed. See build.log');return 1
    for name,e in report['targets'].items():
        if name==ADAPTED: continue
        check=OUT/(name.rsplit('.',1)[-1]+'.lean')
        check.write_text(f"import {e['module']}\n#check {name}\n#print axioms {name}\n")
        p=run(['lake','env','lean',str(check)],check.stem+'.log')
        try:
            if p.returncode: raise ValueError('Lean returned '+str(p.returncode))
            e.update(status='KERNEL CHECKED; statement fidelity review required',axioms=sorted(parse_axioms(p.stdout,name)))
        except ValueError as exc: e['status']='FAILED: '+str(exc)
        save()
    return int(any(not e['status'].startswith('KERNEL CHECKED') for e in report['targets'].values()))
if __name__=='__main__': sys.exit(main())
