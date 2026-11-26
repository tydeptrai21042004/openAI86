#!/usr/bin/env python3
"""Replay the pinned V60 reference bridges in an isolated workspace.
A successful run certifies the listed declarations only, not independent
proofs or the entire original paper. Preparation never certifies proofs.
"""
import argparse
import json
import re
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / 'v55'))
from verify_snapshot import prepare, ARCHIVE_SHA, COMMIT
sys.path.insert(0, str(ROOT / 'tools'))
from axiom_report_parser import parse_axioms

BRIDGES = {
    'CorePath': ('Sec15_5OneDistributionCalculationFinalSums', []),
    'Completion': ('Sec16_3SummingUpdateLevels', []),
}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('archive', type=Path)
    p.add_argument('--work-dir', type=Path, required=True)
    p.add_argument('--target', choices=['all', *BRIDGES], default='all')
    p.add_argument('--prepare-only', action='store_true')
    p.add_argument('--no-cache', action='store_true')
    a = p.parse_args()
    selected = list(BRIDGES) if a.target == 'all' else [a.target]
    w = a.work_dir.resolve()
    if w.exists() and (not w.is_dir() or any(w.iterdir())):
        p.error('Work directory must be empty')
    w.mkdir(parents=True, exist_ok=True)
    report = {'status': 'NOT VERIFIED', 'source_commit': COMMIT,
              'archive_sha256': ARCHIVE_SHA, 'proof_origin': 'reference_dependency',
              'full_paper_certified': False, 'independent_main_proved': False,
              'targets': {name: {'status': 'NOT RUN'} for name in selected}}
    def save():
        (w/'v60_bridge_certificate.json').write_text(json.dumps(report, indent=2)+'\n')
    def run(cmd, log):
        with (w/log).open('w', encoding='utf-8') as out:
            proc = subprocess.run(cmd, cwd=w, stdout=out, stderr=subprocess.STDOUT)
        if proc.returncode:
            raise RuntimeError(f'{cmd} exited {proc.returncode}; see {w/log}')
        return (w/log).read_text(encoding='utf-8')
    save()
    try:
        prepare(a.archive.resolve(), w)
        for name in selected:
            shutil.copyfile(HERE/f'{name}.lean', w/f'ReferenceV60{name}.lean')
        report['status'] = 'SOURCE PREPARED NOT VERIFIED'
        save()
        if a.prepare_only:
            print('Prepared pinned source workspace; no proofs certified.')
            return 0
        if not shutil.which('lake') or not shutil.which('lean'):
            report['status'] = 'BLOCKED: Lean/Lake unavailable'
            save()
            print(report['status'], file=sys.stderr)
            return 2
        if not a.no_cache:
            run(['lake', 'exe', 'cache', 'get'], 'cache.log')
        failed = False
        for name in selected:
            mod, _ = BRIDGES[name]
            targets = re.findall(r'^#print axioms (\S+)\s*$', (HERE/f'{name}.lean').read_text(), re.M)
            if not targets:
                raise ValueError(f'No exact axiom targets for {name}')
            try:
                run(['lake', 'build', '+TrilinearHT.Auto.'+mod], f'{name}_build.log')
                out = run(['lake', 'env', 'lean', f'ReferenceV60{name}.lean'], f'{name}_lean.log')
                report['targets'][name] = {
                    'status': 'KERNEL CHECKED REFERENCE-BACKED; FIDELITY REVIEW REQUIRED',
                    'axioms': {n: sorted(parse_axioms(out, n)) for n in targets}}
            except (OSError, RuntimeError, ValueError) as exc:
                report['targets'][name] = {'status': 'FAILED', 'error': str(exc)}
                failed = True
            save()
        report['status'] = 'FAILED OR PARTIAL' if failed else 'SELECTED BRIDGES KERNEL CHECKED'
        save()
        return int(failed)
    except (OSError, RuntimeError, ValueError) as exc:
        report['error'] = str(exc)
        report['status'] = 'FAILED'
        save()
        print(exc, file=sys.stderr)
        return 1

if __name__ == '__main__':
    sys.exit(main())
