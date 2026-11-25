#!/usr/bin/env python3
"""Check new source candidates and exact interface types, never certify the paper."""
import json, shutil, subprocess, sys
from pathlib import Path
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / 'verification/reports'; REPORT.mkdir(exist_ok=True)
OUT = REPORT / 'V42_KERNEL.json'; LOG = REPORT / 'V42_KERNEL.log'
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
names=['v42_l2_nonneg', 'v42_l2_sq', 'v42_synthesis_energy', 'v42_complex_column_bounds', 'v42_synthesis_injective', 'v42_pairing_bound', 'v42_complex_refit_bound', 'v42_accuracy_at_least_one', 'v42_accuracy_square_growth', 'v42_shifted_accuracy_tail', 'v42_choose_accuracy_start', 'v42_coordinate_height', 'v42_one_height', 'v42_large_height', 'v42_window_is_qualifying', 'v42_actual_height_obstruction']
check = REPORT/'V42KernelCheck.lean'
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
