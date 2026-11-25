#!/usr/bin/env python3
"""Check new source candidates and exact interface types, never certify the paper."""
import json, shutil, subprocess, sys
from pathlib import Path
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'verification/reports'; REPORT.mkdir(exist_ok=True)
OUT = REPORT / 'V41_KERNEL.json'; LOG = REPORT / 'V41_KERNEL.log'
state = {'status':'NOT RUN','paper_results_certified':0,'checks':{}}
def save(): OUT.write_text(json.dumps(state, indent=2)+'\n')
def run(cmd):
    print('$ '+' '.join(cmd), flush=True)
    p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    with LOG.open('a') as f: f.write('$ '+' '.join(cmd)+'\n'+p.stdout+'\n')
    print(p.stdout, end='')
    return p.returncode, p.stdout
LOG.write_text(''); save()
if not shutil.which('lake') or not shutil.which('lean'):
    state['status']='NOT RUN: Lean/Lake unavailable'; save(); print(state['status']); sys.exit(2)
rc,_=run(['lake','build','OpenAI086Whole'])
if rc:
    state['status']='BUILD FAILED'; save(); sys.exit(1)
names=['v41_scalar_height_assembly','v41_height_bin_explicit','v41_printed_width_obstruction','v41_full_main_of_schwartz_estimate','v22_submodule_prefix','v22_submodule_variation','v29_attempt_tree_packing']
check = REPORT/'V41KernelCheck.lean'
check.write_text('import OpenAI086Whole\n'+ '\n'.join('#check OpenAI086.'+n+'\n#print axioms OpenAI086.'+n for n in names)+'\n#check OpenAI086.V41NormalizedAbsorptionGoal\n#check OpenAI086.V41UniformLocalGoal\n#check OpenAI086.V41FullMainGoal\n')
rc,txt=run(['lake','env','lean',str(check)])
if rc:
    state['status']='CHECK FAILED'; save(); sys.exit(1)
for n in names:
    try:
        deps=parse_axioms(txt,'OpenAI086.'+n)
        if deps-{'propext','Classical.choice','Quot.sound'}:
            raise UnrecognizedAxiomReport('strict dependency policy failed')
        state['checks'][n]={'status':'DECLARATION CHECKED','axioms':sorted(deps)}
    except UnrecognizedAxiomReport as e:
        state['checks'][n]={'status':'FAILED','reason':str(e)}
state['status']='CANDIDATES CHECKED; PAPER INCOMPLETE' if all(x['status']=='DECLARATION CHECKED' for x in state['checks'].values()) else 'AXIOM AUDIT FAILED'
save(); print(state['status']); sys.exit(0 if state['status'].startswith('CANDIDATES') else 1)
