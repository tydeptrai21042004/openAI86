#!/usr/bin/env python3
"""Optional external proof replay, separate from independent certification."""
from pathlib import Path
import argparse, hashlib, json, re, shutil, subprocess, sys
ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
COMMIT = '0fac9f4ed4aa3391931897a681ce547981fb5f46'
TOOLCHAIN = 'leanprover/lean4:v4.35.0-rc3'
MATHLIB = 'c55e6e786f49471c72fbddbec5415808896aec1e'
URL = 'https://github.com/roos-j/lean-trilinearht.git'
ALLOWED = {'propext', 'Quot.sound', 'Classical.choice'}
NAMES = ['TrilinearHT.trilinear_ht_bound', 'Auto.T_trunc_eq_neg', 'Auto.tendsto_T_trunc', 'OpenAI086.Theorem1_1_Proved']
EXPECTED = '77d2c9742d84e1a831f439fb0814d29ec074fc270760b7ff8f290da4f465939b'

def check_axioms(output, name):
    pat = rf"(?m)^\s*['`\"]?{re.escape(name)}['`\"]?\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$"
    matches = list(re.finditer(pat, output))
    if len(matches) != 1:
        raise ValueError(f'Expected exactly one axiom report for {name}; got {len(matches)}')
    axioms = {s.strip() for s in (matches[0].group(1) or '').split(',') if s.strip()}
    if not axioms <= ALLOWED:
        raise ValueError(f'{name}: unapproved axioms {sorted(axioms - ALLOWED)}')
    return sorted(axioms)

def source():
    raw = (ROOT/'OpenAI086/PaperStatement.lean').read_bytes()
    if hashlib.sha256(raw).hexdigest() != EXPECTED:
        raise ValueError('V32 exact target hash mismatch')
    text = raw.decode('utf8')
    if not text.startswith('import Mathlib\n'):
        raise ValueError('Unexpected original import header')
    return ('import Mathlib\nimport TrilinearHT.Theorems\n'
            'import TrilinearHT.Auto.Sec16_3SummingUpdateLevels\n' +
            text[len('import Mathlib\n'):] + '\n' +
            (HERE/'MainProof.lean.in').read_text(encoding='utf8'))

def run(args, cwd, log):
    print('+', ' '.join(str(x) for x in args), flush=True)
    with log.open('a', encoding='utf8') as out:
        out.write('\n$ ' + ' '.join(str(x) for x in args) + '\n'); out.flush()
        result = subprocess.run(args, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(f'Command failed ({result.returncode}); see {log}')

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work-dir', type=Path, default=ROOT/'.external-replay')
    p.add_argument('--no-cache', action='store_true')
    p.add_argument('--prepare-only', action='store_true', help='Generate exact check file without a certificate')
    a = p.parse_args()
    work = a.work_dir.resolve(); work.mkdir(parents=True, exist_ok=True)
    log = work/'external_build.log'; log.write_text('', encoding='utf8')
    cert = work/'external_certificate.json'
    report = {'status':'NOT_VERIFIED', 'proof_origin':'external_dependency', 'commit':COMMIT,
              'lean_toolchain':TOOLCHAIN, 'mathlib_commit':MATHLIB, 'target_sha256':EXPECTED,
              'independent_main_proof':False, 'full_paper_certified':False}
    def save(): cert.write_text(json.dumps(report, indent=2)+'\n', encoding='utf8')
    save()
    try:
        check = work/'MainProof.lean'; check.write_text(source(), encoding='utf8')
        if a.prepare_only:
            report['status'] = 'SOURCE_PREPARED_NOT_VERIFIED'; save(); print(check); return 0
        for exe in ('git','lake'):
            if not shutil.which(exe): raise RuntimeError(f'{exe} is not installed or is not on PATH')
        repo = work/'lean-trilinearht'
        if not repo.exists():
            run(['git','clone','--no-checkout',URL,str(repo)], work, log)
        if not (repo/'.git').is_dir(): raise RuntimeError('Unexpected checkout directory')
        run(['git','fetch','origin',COMMIT],repo,log)
        run(['git','checkout','--detach',COMMIT],repo,log)
        actual = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
        if actual != COMMIT: raise ValueError('External commit mismatch')
        if subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=repo,text=True).strip():
            raise ValueError('Tracked upstream files have local modifications')
        if (repo/'lean-toolchain').read_text().strip() != TOOLCHAIN: raise ValueError('Lean pin mismatch')
        manifest = json.loads((repo/'lake-manifest.json').read_text())
        if not any(x.get('name') == 'mathlib' and x.get('rev') == MATHLIB for x in manifest['packages']):
            raise ValueError('Mathlib pin mismatch')
        run(['lake','--version'],repo,log)
        if not a.no_cache:
            run(['lake','exe','cache','get'],repo,log)
        run(['lake','build','TrilinearHT'],repo,log)
        checklog = work/'exact_target.log'; checklog.write_text('',encoding='utf8')
        replay_file = repo/'V33ExactTarget.lean'
        if replay_file.exists() and replay_file.read_bytes() != check.read_bytes():
            raise ValueError('Refusing to overwrite a different V33ExactTarget.lean')
        shutil.copyfile(check, replay_file)
        report['exact_check_sha256'] = hashlib.sha256(check.read_bytes()).hexdigest()
        run(['lake','env','lean',replay_file.name],repo,checklog)
        output = checklog.read_text(encoding='utf8')
        report['axioms'] = {name:check_axioms(output,name) for name in NAMES}
        report['status'] = 'KERNEL_VERIFIED_EXTERNAL_EXACT_TARGET'
        save(); print('PASS: exact V32 main goal verified through the external dependency.'); return 0
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as e:
        report['error'] = str(e); save(); print('NOT VERIFIED:',e,file=sys.stderr); return 1

if __name__ == '__main__': sys.exit(main())
