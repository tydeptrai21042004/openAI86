#!/usr/bin/env python3
"""Fail-closed V49 kernel verifier; static checks never promote results."""
import argparse, json, shutil, subprocess, sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
TARGETS={
 '3.4-anchor-history':('OpenAI086.PaperV49AnchorCoherence','OpenAI086.v49_anchor_depth_history_coherent'),
 '3.4-anchor-cells':('OpenAI086.PaperV49AnchorCoherence','OpenAI086.v49_anchor_cell_history_coherent'),
 '3.4-predecessor':('OpenAI086.PaperV49AnchorCoherence','OpenAI086.v49_previous_anchor_label_coherent'),
 '3.4-row-error':('OpenAI086.PaperV49ErrorRows','OpenAI086.v49_anchor_error_rows'),
 '3.4-row-assembly':('OpenAI086.PaperV49ErrorRows','OpenAI086.v49_segment_anchor_error_assembly'),
}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--target',choices=TARGETS,action='append')
    args=ap.parse_args()
    keys=args.target or list(TARGETS)
    if not shutil.which('lean') or not shutil.which('lake'):
        out=ROOT/'verification'/'reports'/'V49'
        out.mkdir(parents=True,exist_ok=True)
        report={'targets':{k:{'module':TARGETS[k][0],'constant':TARGETS[k][1],
                              'status':'BLOCKED: Lean/Lake unavailable',
                              'paper_result_certified':False} for k in keys},
                'note':'Static/model checks are not kernel certification.'}
        (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
        for k in keys: print(f'{k}: BLOCKED: Lean/Lake unavailable')
        return 2
    rc=0
    for k in keys:
        mod, theorem=TARGETS[k]
        p=subprocess.run(['lake','build','+'+mod],cwd=ROOT,text=True)
        if p.returncode:
            print(f'{k}: BUILD FAILED'); rc=max(rc,1); continue
        check=ROOT/'verification'/'reports'/'V49'/k/'Check.lean'
        check.parent.mkdir(parents=True,exist_ok=True)
        check.write_text(f'import {mod}\n#check {theorem}\n#print axioms {theorem}\n')
        p=subprocess.run(['lake','env','lean',str(check)],cwd=ROOT,text=True)
        if p.returncode:
            print(f'{k}: KERNEL CHECK FAILED'); rc=max(rc,1)
        else:
            print(f'{k}: encoded statement checked; manuscript-fidelity review still required')
    return rc
if __name__=='__main__': sys.exit(main())
