#!/usr/bin/env python3
"""Strict gate for a future, locally proved Theorem 1.1.

No JSON status flag, numerical experiment, or externally proved theorem can
satisfy this gate. A direct proof term of our exact target is required.
"""
from pathlib import Path
import re, shutil, subprocess, sys
root=Path(__file__).resolve().parents[1]
proof=root/'OpenAI086/MainProof.lean'
whole=(root/'OpenAI086Whole.lean').read_text(encoding='utf8')
if not proof.exists() or 'import OpenAI086.MainProof' not in whole:
    print('OPEN: Theorem 1.1 is not proved inside this repository.')
    print('Required: OpenAI086/MainProof.lean with an imported Lean proof term.')
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
check.write_text('import OpenAI086.MainProof\n'
                 '#check OpenAI086.Theorem1_1_Proved\n'
                 '#print axioms OpenAI086.Theorem1_1_Proved\n')
print('Checking exact target and axiom dependencies...')
result=subprocess.run(['lake','env','lean',str(check)],cwd=root)
if result.returncode:
    sys.exit(result.returncode)
print('Lean ACCEPTED the exact local theorem. REVIEW AXIOM OUTPUT above.')
print('WARNING: L3-extension / correspondence to the mathematical paper')
print('requires a separate statement audit, not this source-level gate.')
