#!/usr/bin/env python3
"""Fail-closed V52 Lean kernel checks. Static/model checks are not certificates."""
from pathlib import Path
import json, shutil, subprocess, sys
ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    '4.3-iterated-weyl-samples': ('OpenAI086.PaperV52IteratedWeylSamples',
        'OpenAI086.v52_iterated_sample_lower_bound'),
    '4.3-return-bound-bridge': ('OpenAI086.PaperV52IteratedWeylSamples',
        'OpenAI086.v52_return_bound_from_iterated_samples'),
    '9.1-nonfuture-pair': ('OpenAI086.PaperV52SparseNonfuture',
        'OpenAI086.v52_nonfuture_pair_mass'),
    '9.1-six-pairs': ('OpenAI086.PaperV52SparseNonfuture',
        'OpenAI086.v52_six_nonfuture_pair_mass'),
    '10.3-parameter-order': ('OpenAI086.PaperV52ParameterOrder',
        'OpenAI086.v52_choose_parameter_order'),
    '10.3-side-cost': ('OpenAI086.PaperV52ParameterOrder',
        'OpenAI086.v52_side_cost_power'),
    '10.3-quality-power': ('OpenAI086.PaperV52ParameterOrder',
        'OpenAI086.v52_quality_power_from_ceiling_power'),
}

def main():
    if not shutil.which('lean') or not shutil.which('lake'):
        out = ROOT/'verification'/'reports'/'V52'
        out.mkdir(parents=True, exist_ok=True)
        report = {'targets': {k: {'module': m, 'constant': t,
                                  'status': 'BLOCKED: Lean/Lake unavailable',
                                  'paper_result_certified': False}
                             for k, (m, t) in TARGETS.items()},
                  'note': 'Static audits and exact rational regressions are not Lean kernel certificates.'}
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
        for k in TARGETS: print(f'{k}: BLOCKED: Lean/Lake unavailable')
        return 2
    rc = subprocess.run(['lake', 'build', 'OpenAI086'], cwd=ROOT).returncode
    if rc:
        print('FAIL: OpenAI086 library build failed; no V52 certificate issued.')
        return rc
    for key, (module, theorem) in TARGETS.items():
        check = ROOT/'verification'/'reports'/'V52'/key/'Check.lean'
        check.parent.mkdir(parents=True, exist_ok=True)
        check.write_text(f'import {module}\n#check {theorem}\n#print axioms {theorem}\n')
        rc = subprocess.run(['lake', 'env', 'lean', str(check)], cwd=ROOT).returncode
        if rc:
            print(f'{key}: KERNEL CHECK FAILED')
            return rc
        print(f'{key}: declaration checked; paper-level proof review remains necessary.')
    return 0

if __name__ == '__main__':
    sys.exit(main())
