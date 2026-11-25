#!/usr/bin/env python3
"""Independently build and inspect manuscript-level candidates.
A successful check certifies the *encoded statement* only. Paper fidelity
review is separate. A failed/missing Lean process cannot produce PASS.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    '3.1': ('OpenAI086.PaperV43Packing', 'OpenAI086.v43_lemma31',
            'example : OpenAI086.V43Lemma31Goal := OpenAI086.v43_lemma31'),
    '3.3': ('OpenAI086.PaperV43Lemma33', 'OpenAI086.v43_lemma33',
            '#check OpenAI086.V43Lemma33Goal'),
    '3.5-scalar': ('OpenAI086.PaperV41Section3', 'OpenAI086.v41_scalar_height_assembly',
            'example (d B : ℕ) (ξ : Fin d → ℝ) : OpenAI086.V41ScalarHeightGoal d B ξ := OpenAI086.v41_scalar_height_assembly d B ξ'),
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def source_hash():
    from independent_sources import independent_sources
    h = hashlib.sha256()
    paths = independent_sources(ROOT) + [ROOT/'lean-toolchain', ROOT/'lakefile.toml']
    for path in sorted(paths):
        h.update(str(path.relative_to(ROOT)).encode()+b'\0'+path.read_bytes()+b'\0')
    return h.hexdigest()

def verify(key):
    module, theorem, typecheck = TARGETS[key]
    folder = ROOT/'verification'/'reports'/'V43'/key
    folder.mkdir(parents=True, exist_ok=True)
    output = folder/'result.json'
    log = folder/'kernel.log'
    log.write_text('')
    result = {'target': key, 'module': module, 'theorem': theorem,
              'status':'NOT RUN', 'paper_result_certified':False,
              'source_sha256': source_hash(), 'axioms':None}
    def save():
        output.write_text(json.dumps(result, indent=2)+'\n')
    def run(cmd):
        print('$ '+' '.join(cmd), flush=True)
        p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT)
        with log.open('a') as out: out.write('$ '+' '.join(cmd)+'\n'+p.stdout+'\n')
        print(p.stdout, end='')
        return p
    save()
    if not shutil.which('lake') or not shutil.which('lean'):
        result['status']='BLOCKED: Lean/Lake unavailable'; log.write_text(result['status']+'\n'); save(); print(key+': '+result['status']); return 2
    p = run(['lake','build','+'+module])
    if p.returncode:
        result['status']='BUILD FAILED'; save(); return 1
    check = folder/'Check.lean'
    check.write_text(f'import {module}\n{typecheck}\n#check {theorem}\n#print axioms {theorem}\n')
    p = run(['lake','env','lean',str(check)])
    if p.returncode:
        result['status']='TYPE OR KERNEL CHECK FAILED'; save(); return 1
    try:
        axioms = parse_axioms(p.stdout, theorem)
        if axioms - ALLOWED:
            raise UnrecognizedAxiomReport('Strict foundational dependency policy violated')
    except UnrecognizedAxiomReport as exc:
        result['status']='AXIOM CHECK FAILED'; result['reason']=str(exc); save(); return 1
    result['status']='ENCODED STATEMENT KERNEL CHECKED'
    result['axioms']=sorted(axioms)
    result['scope']='Requires human statement-fidelity review; no manuscript registry promotion.'
    save()
    return 0

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--target', choices=TARGETS, action='append')
    args=ap.parse_args()
    codes=[verify(key) for key in (args.target or TARGETS)]
    return max(codes)

if __name__=='__main__': sys.exit(main())
