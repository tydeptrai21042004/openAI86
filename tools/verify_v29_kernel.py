#!/usr/bin/env python3
"""Build selected independent modules in dependency order, record the first
failure, then require kernel axiom reports. Never certifies a paper result.
Run with --all to include all independent modules. No installation is implicit.
"""
from pathlib import Path
import argparse, json, re, shutil, subprocess, sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT/'verification/reports'; REPORT.mkdir(exist_ok=True)
NAMES={
 'PaperAttemptTreePacking':['v29_generation_contraction','v29_attempt_tree_packing'],
 'PaperEvaluationDominance':['v29_dominant_integer_relation','v29_independent_evaluation_count'],
 'PaperTwoStepLattice':['V29TwoStep.v29_mul_horizontal','V29TwoStep.v29_mul_central','V29TwoStep.v29_inv_horizontal','V29TwoStep.v29_inv_central','V29TwoStep.v29_pure_central_commutes','V29TwoStep.v29_commutator_horizontal','V29TwoStep.v29_commutator_centralizes','V29TwoStep.v29IntegralSubgroup','V29TwoStep.v29RightCosetSetoid'],
 'PaperLemma33Submodules':['v22_submodule_prefix','v22_submodule_variation'],
 'PaperActualSchwartzOperator':['v25_actual_realization','v25_main_and_extension'],
 'PaperCubeInterval':['v28_indicator_cube_positive','v28_interval_cube_nonnegative'],
}
p=argparse.ArgumentParser(); p.add_argument('--all',action='store_true'); p.add_argument('--cache',action='store_true'); args=p.parse_args()
state={'status':'NOT VERIFIED','paper_results_certified':0,'completed_modules':[],'first_failed_module':None,'axiom_reports':{}}
log=REPORT/'V29_KERNEL.log'; summary=REPORT/'V29_KERNEL.json'
def save():summary.write_text(json.dumps(state,indent=2)+'\n')
def message(s):
    print(s,flush=True)
    with log.open('a') as f:f.write(s+'\n')
def fail(msg, code=1):
    state['reason']=msg; message(msg); save(); raise SystemExit(code)
def run(cmd):
    message('$ '+' '.join(cmd))
    with log.open('a') as f:
        proc=subprocess.Popen(cmd,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,bufsize=1)
        chunks=[]
        for line in proc.stdout:
            print(line,end='',flush=True); f.write(line); f.flush(); chunks.append(line)
        return proc.wait(),''.join(chunks)
log.write_text('');save()
if not shutil.which('lean') or not shutil.which('lake'):
    fail('NOT VERIFIED: Lean/Lake unavailable.',2)
rc,_=run(['lean','--version'])
if rc:fail('Lean toolchain invocation failed.',2)
if args.cache:
    rc,_=run(['lake','exe','cache','get'])
    if rc:fail('Mathlib cache setup failed.',2)
mods={'.'.join(f.relative_to(ROOT).with_suffix('').parts):f for f in (ROOT/'OpenAI086').rglob('*.lean')}
mods['OpenAI086']=ROOT/'OpenAI086.lean'; mods['OpenAI086Whole']=ROOT/'OpenAI086Whole.lean'
order=[]; done=set(); active=set()
def visit(m):
    if m in done:return
    if m in active:fail('Import cycle: '+m)
    active.add(m)
    for dep in re.findall(r'^\s*(?:public\s+)?import\s+(\S+)',mods[m].read_text(),re.M):
        if dep in mods:visit(dep)
        elif not dep.startswith('Mathlib'):fail('Unsupported import: '+dep)
    active.remove(m); done.add(m); order.append(m)
for m in (['OpenAI086Whole'] if args.all else ['OpenAI086.'+s for s in NAMES]):visit(m)
for m in order:
    rc,_=run(['lake','build','+'+m])
    if rc:
        state['first_failed_module']=m; fail('BUILD FAILED: '+m)
    state['completed_modules'].append(m);save()
for m,names in NAMES.items():
    path=REPORT/(m+'_v29_check.lean')
    qualified=['OpenAI086.'+name for name in names]
    path.write_text('import OpenAI086.'+m+'\n'+'\n'.join('#print axioms '+n for n in qualified)+'\n')
    rc,out=run(['lake','env','lean',str(path)])
    if rc:fail('Kernel report failed for '+m)
    for n in qualified:
        try:state['axiom_reports'][n]=sorted(parse_axioms(out,n))
        except UnrecognizedAxiomReport as ex:fail(str(ex),3)
    save()
state['status']='SELECTED COMPONENTS VERIFIED (not full paper results)';save();message(state['status'])
