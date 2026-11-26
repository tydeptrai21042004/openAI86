#!/usr/bin/env python3
"""Fail closed. Adapted results are checked separately from the independent tree."""
from pathlib import Path
import json, re, shutil, subprocess, sys
from axiom_report_parser import parse_axioms
from lean_lex import code_only
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'verification/reports/V57'
ADAPTED={
 'source_fidelity/v57/TinySpan.lean': [
   'OpenAI086.AdaptedV57.rational_small_dependence',
   'OpenAI086.AdaptedV57.v57_tiny_of_mem_tinySpan',
   'OpenAI086.AdaptedV57.v57_lemma82_tiny',
   'OpenAI086.AdaptedV57.v57_lemma82_ordered_scales'],
 'source_fidelity/v56/EntryRank.lean': [
   'OpenAI086.AdaptedV56.v56_lemma85',
   'OpenAI086.AdaptedV56.v57_lemma86_rank',
   'OpenAI086.AdaptedV56.v57_floorLog_mono',
   'OpenAI086.AdaptedV56.v57_lemma86']}
LOCAL={'OpenAI086.PaperV57BaseSummation': [
 'OpenAI086.v57_tuple_cutoff_bound','OpenAI086.v57_choose_uniform_tuple_cutoff',
 'OpenAI086.v57_cutoff_limit_bound']}

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    report={'independent_main_proved':False,'full_paper_certified':False,'targets':{}}
    for source,names in ADAPTED.items():
        clean=code_only((ROOT/source).read_text())
        if re.search(r'\b(sorry|admit|axiom|constant|opaque|unsafe|native_decide)\b',clean):
            raise RuntimeError(f'forbidden declaration/tactic in {source}')
        for n in names:
            report['targets'][n]={'source':source,'origin':'attributed adapted','status':'NOT RUN'}
    for source,names in LOCAL.items():
        for n in names:
            report['targets'][n]={'source':source,'origin':'independent','status':'NOT RUN'}
    def save(): (OUT/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    def run(cmd,log):
        p=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (OUT/log).write_text(p.stdout); return p
    def check(p,n):
        e=report['targets'][n]
        try:
            if p.returncode: raise ValueError(f'Lean exited {p.returncode}')
            e.update(status='KERNEL CHECKED; statement fidelity review required',axioms=sorted(parse_axioms(p.stdout,n)))
        except ValueError as ex: e['status']='FAILED: '+str(ex)
        save()
    if not shutil.which('lake') or not shutil.which('lean'):
        for e in report['targets'].values(): e['status']='BLOCKED: Lean/Lake unavailable'
        save(); print('BLOCKED: Lean/Lake unavailable. No result certified.'); return 2
    # Isolated adapted files can be checked even if the independent tree fails.
    for source,names in ADAPTED.items():
        p=run(['lake','env','lean',source],Path(source).stem+'.log')
        for n in names: check(p,n)
    p=run(['lake','build','OpenAI086Whole'],'build.log')
    if p.returncode:
        for names in LOCAL.values():
            for n in names: report['targets'][n]['status']='BLOCKED: independent build failed'
        save(); return 1
    for source,names in LOCAL.items():
        f=OUT/'local_checks.lean'
        f.write_text('import '+source+'\n'+''.join(f'#check {n}\n#print axioms {n}\n' for n in names))
        p=run(['lake','env','lean',str(f)],'local_checks.log')
        for n in names: check(p,n)
    return int(any(not e['status'].startswith('KERNEL CHECKED') for e in report['targets'].values()))
if __name__=='__main__': sys.exit(main())
