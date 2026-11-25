#!/usr/bin/env python3
"""Build V48 Lean candidates independently; this is not a paper-proof promotion."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
from independent_sources import independent_sources

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    '3.2-transition': ('OpenAI086.PaperV48PrivateTransition', 'OpenAI086.v48_private_transition_lower'),
    '3.2-column-transition': ('OpenAI086.PaperV48PrivateTransition', 'OpenAI086.v48_private_column_transition_lower'),
    '3.4-private-increment': ('OpenAI086.PaperV48RestartAssembly', 'OpenAI086.v48_private_increment_large'),
    '3.4-restart-cutoff': ('OpenAI086.PaperV48RestartCutoff', 'OpenAI086.v48_restart_factor_lt_half'),
    '3.4-restart-algebra': ('OpenAI086.PaperV48RestartCutoff', 'OpenAI086.v48_restart_factor_from_variation'),
    '3.4-anchor-adapted': ('OpenAI086.PaperV48SpatialAnchors', 'OpenAI086.v48_anchor_state_constant_on_terminal_cell'),
    '3.4-anchor-measurable': ('OpenAI086.PaperV48SpatialAnchors', 'OpenAI086.v48_anchor_label_fiber_measurable'),
    '3.4-anchor-refinement': ('OpenAI086.PaperV48AnchorPartitions', 'OpenAI086.v48_spatial_partition_refines'),
    '3.4-anchor-partition-measurable': ('OpenAI086.PaperV48AnchorPartitions', 'OpenAI086.v48_spatial_partition_fiber_measurable'),
    '3.4-anchor-finite-range': ('OpenAI086.PaperV48AnchorPartitions', 'OpenAI086.v48_spatial_partition_range_finite'),
    '3.4-history-refinement': ('OpenAI086.PaperV48AnchorPartitions', 'OpenAI086.v48_history_stage_refines'),
    '3.4-restart-assembly': ('OpenAI086.PaperV48RestartAssembly', 'OpenAI086.v48_restart_attempt_contract'),
    '3.4-private-restart': ('OpenAI086.PaperV48RestartAssembly', 'OpenAI086.v48_private_restart_attempt_contract'),
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def digest():
    h = hashlib.sha256()
    for p in sorted(independent_sources(ROOT) + [ROOT/'lean-toolchain', ROOT/'lakefile.toml']):
        h.update(str(p.relative_to(ROOT)).encode()+b'\0'+p.read_bytes()+b'\0')
    return h.hexdigest()

def verify(key):
    mod, theorem = TARGETS[key]
    outdir = ROOT/'verification'/'reports'/'V48'/key
    outdir.mkdir(parents=True, exist_ok=True)
    log = outdir/'kernel.log'
    result = {'target':key,'module':mod,'theorem':theorem,'status':'NOT RUN',
              'paper_result_certified':False,'source_sha256':digest(),'axioms':None}
    def save():
        (outdir/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    save(); log.write_text('')
    if not shutil.which('lean') or not shutil.which('lake'):
        result['status']='BLOCKED: Lean/Lake unavailable'; save()
        log.write_text(result['status']+'\n')
        print(key+': '+result['status'])
        return 2
    def run(cmd):
        p = subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        with log.open('a') as f: f.write('$ '+' '.join(cmd)+'\n'+p.stdout+'\n')
        print(p.stdout,end='')
        return p
    p=run(['lake','build','+'+mod])
    if p.returncode:
        result['status']='BUILD FAILED'; save(); return 1
    check=outdir/'Check.lean'
    check.write_text(f'import {mod}\n#check {theorem}\n#print axioms {theorem}\n')
    p=run(['lake','env','lean',str(check)])
    if p.returncode:
        result['status']='KERNEL CHECK FAILED'; save(); return 1
    try:
        axioms=parse_axioms(p.stdout,theorem)
        if axioms-ALLOWED:
            raise UnrecognizedAxiomReport('Unapproved axiom dependency: '+str(axioms-ALLOWED))
    except UnrecognizedAxiomReport as e:
        result['status']='AXIOM CHECK FAILED'; result['reason']=str(e); save(); return 1
    result['status']='ENCODED STATEMENT KERNEL CHECKED'
    result['axioms']=sorted(axioms)
    result['scope']='Requires manuscript statement-fidelity review; not promoted to a full paper result.'
    save(); return 0

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--target',choices=TARGETS,action='append')
    args=ap.parse_args()
    keys=args.target or list(TARGETS)
    return max(verify(k) for k in keys)
if __name__=='__main__': sys.exit(main())
