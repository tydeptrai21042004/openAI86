#!/usr/bin/env python3
"""Fail-closed V51 kernel verification. Static/model checks never certify."""
from pathlib import Path
import json, shutil, subprocess, sys
ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    '4.3-return-algebra': ('OpenAI086.PaperV51WeylReturnAlgebra', 'OpenAI086.v51_short_return_span_isotropic'),
    '7.2-randomizer': ('OpenAI086.PaperV51WeylReturnAlgebra', 'OpenAI086.v51_progression_randomizer_exp_one'),
    '5-staggered-product': ('OpenAI086.PaperV51StaggeredExpansion', 'OpenAI086.v51_four_slot_product_difference_bound'),
    '8.9-event-energy': ('OpenAI086.PaperV51Prop89Assembly', 'OpenAI086.v51_prop89_event_energy_assembly'),
    '4.7-external-interface': ('OpenAI086.PaperV51LSSExternalInterface', 'OpenAI086.v51_apply_lss_external_input'),
}

def main():
    if not shutil.which('lean') or not shutil.which('lake'):
        out = ROOT/'verification'/'reports'/'V51'
        out.mkdir(parents=True, exist_ok=True)
        report = {'targets': {k: {'module': m, 'constant': t,
                                  'status': 'BLOCKED: Lean/Lake unavailable',
                                  'paper_result_certified': False}
                             for k, (m, t) in TARGETS.items()},
                  'note': 'Exact arithmetic tests and static audits are not Lean kernel certificates.'}
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
        for k in TARGETS: print(f'{k}: BLOCKED: Lean/Lake unavailable')
        return 2
    rc = subprocess.run(['lake', 'build', 'OpenAI086'], cwd=ROOT).returncode
    if rc:
        print('FAIL: OpenAI086 library build failed; no V51 certificate issued.')
        return rc
    for key, (module, theorem) in TARGETS.items():
        check = ROOT/'verification'/'reports'/'V51'/key/'Check.lean'
        check.parent.mkdir(parents=True, exist_ok=True)
        check.write_text(f'import {module}\n#check {theorem}\n#print axioms {theorem}\n')
        rc = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=ROOT).returncode
        if rc:
            print(f'{key}: KERNEL CHECK FAILED')
            return rc
        print(f'{key}: Lean declaration checked; manuscript-level proof review still required.')
    return 0

if __name__ == '__main__':
    sys.exit(main())
