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
 'PaperHeightScaleCorrection':['v31_two_scale_windows','v31_no_dimension_free_width','v31_real_interval_integer_count','v31_corrected_packet_count'],
 'PaperInverseUniformNormalization':['v31_box_mass','v31_short_cube_supported','v31_indicator_mask_sum','v31_indicator_cube_uniform','v31_uniform_inverse_first_step'],
 'PaperLemma33Statement':['v21_paper_lemma33_prefix','v21_paper_lemma33_variation'],
 'PaperInverseDerivative':['v30_interval_inverse_first_step'],
 'PaperInverseExtremal':['v30_extremal_interval_quadratic','v30_extremal_interval_correlation'],
}

p=argparse.ArgumentParser(); p.add_argument('--all',action='store_true'); p.add_argument('--cache',action='store_true'); args=p.parse_args()
state={'printed_lemma_3_5_2_refuted_by_ordinary_math':True,'status':'NOT VERIFIED','paper_results_certified':0,'completed_modules':[],'first_failed_module':None,'axiom_reports':{}}
log=REPORT/'V31_KERNEL.log'; summary=REPORT/'V31_KERNEL.json'
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
if not (ROOT/'lake-manifest.json').exists():
    rc,_=run(['lake','update'])
    if rc:fail('Pinned dependency resolution failed.',2)
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
    path=REPORT/(m+'_v31_check.lean')
    qualified=['OpenAI086.'+name for name in names]
    path.write_text('import OpenAI086.'+m+'\n'+'\n'.join('#print axioms '+n for n in qualified)+'\n')
    rc,out=run(['lake','env','lean',str(path)])
    if rc:fail('Kernel report failed for '+m)
    for n in qualified:
        try:state['axiom_reports'][n]=sorted(parse_axioms(out,n))
        except UnrecognizedAxiomReport as ex:fail(str(ex),3)
    save()
state['status']='SELECTED COMPONENTS VERIFIED (not full paper results)';save();message(state['status'])
