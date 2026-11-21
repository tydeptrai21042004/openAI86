#!/usr/bin/env python3
"""Strict gate for a future, locally proved Theorem 1.1.

No JSON status flag, numerical experiment, or externally proved theorem can
satisfy this gate. A direct proof term of our exact target is required.
"""
from pathlib import Path
import re, shutil, subprocess, sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
root=Path(__file__).resolve().parents[1]
proof=root/'OpenAI086/MainProof.lean'
core=(root/'OpenAI086.lean').read_text(encoding='utf8')
if not proof.exists() or 'import OpenAI086.MainProof' not in core:
    print('OPEN: Theorem 1.1 is not proved inside this repository.')
    print('Required: OpenAI086/MainProof.lean, imported through OpenAI086.lean.')
    sys.exit(1)
src=proof.read_text(encoding='utf8')
if not re.search(r'\btheorem\s+Theorem1_1_Proved\s*:\s*Theorem1_1_Goal\b',src):
    print('OPEN: The required theorem does not have the exact local target type.')
    sys.exit(1)
if not shutil.which('lake'):
    print('UNVERIFIED: Lake/Lean not installed.')
    sys.exit(2)
for cmd in ([sys.executable,'tools/static_audit.py'],
            ['lake','build','OpenAI086Whole']):
    result=subprocess.run(cmd,cwd=root)
    if result.returncode:
        sys.exit(result.returncode)
check=root/'verification'/'MainTheoremAxiomCheck.lean'
check.parent.mkdir(exist_ok=True)
check.write_text('import OpenAI086Whole\n'
                 '#check OpenAI086.Theorem1_1_Proved\n'
                 '#print axioms OpenAI086.Theorem1_1_Proved\n')
print('Checking exact target and axiom dependencies...')
result=subprocess.run(['lake','env','lean',str(check)],cwd=root,
                      text=True,capture_output=True)
print(result.stdout, end='')
print(result.stderr, end='',file=sys.stderr)
if result.returncode:
    sys.exit(result.returncode)
# A source scan cannot detect dependencies imported from other modules, and
# a successful #check can refer to untrusted axioms. Inspect the kernel report.
try:
    axioms = parse_axioms(result.stdout + result.stderr,
                         'OpenAI086.Theorem1_1_Proved')
except UnrecognizedAxiomReport as ex:
    print(f'FAIL: {ex}', file=sys.stderr)
    sys.exit(3)
print(f'PASS: exact target compiled; trusted dependencies: {sorted(axioms)}')
print('Mathematical fidelity, pointwise principal values, and L³ extension still require review.')
