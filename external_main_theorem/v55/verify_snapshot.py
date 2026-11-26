#!/usr/bin/env python3
"""Replay the uploaded reference snapshot in an isolated workspace, not the independent gate."""
import argparse, hashlib, json, shutil, subprocess, sys, zipfile
from pathlib import Path, PurePosixPath
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent))
from verify_external import check_axioms
ARCHIVE_SHA = 'e5e865eaa06b570ea5a3442432bee0e5e2a10d94f748cc1bb06afc8608dba3f9'
TARGET_SHA = '77d2c9742d84e1a831f439fb0814d29ec074fc270760b7ff8f290da4f465939b'
COMMIT = '7b4209609e6a7fb9d9935973ee8541495f943660'
TOOLCHAIN = 'leanprover/lean4:v4.36.0-rc1'
MATHLIB = 'fbc1661a327737928fe9d69b74f7deaa09eecfbc'
EXACT_NAMES = ['TrilinearHT.trilinear_ht_bound','Auto.T_trunc_eq_neg',
               'Auto.tendsto_T_trunc','Auto.finite_inverse','Auto.tht_main',
               'OpenAI086.ReferenceV55.exact_main']
FULL_NAMES = ['OpenAI086.ReferenceV55.schwartz_estimate','OpenAI086.ReferenceV55.full_main']

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def prepare(archive, work):
    if sha(archive) != ARCHIVE_SHA: raise ValueError('Uploaded snapshot SHA-256 mismatch')
    if sha(ROOT/'OpenAI086/PaperStatement.lean') != TARGET_SHA: raise ValueError('Locked target changed')
    with zipfile.ZipFile(archive) as z:
        if z.comment.decode().strip() != COMMIT: raise ValueError('Snapshot commit marker mismatch')
        for m in z.infolist():
            p = PurePosixPath(m.filename)
            if p.is_absolute() or '..' in p.parts or not p.parts or p.parts[0] != 'lean-trilinearht-master':
                raise ValueError('Unexpected ZIP path')
            if m.is_dir() or len(p.parts) < 2: continue
            rel = Path(*p.parts[1:])
            # Only source/config/license/documentation; no scripts from the uploaded archive are executed.
            if rel.parts[0] not in {'TrilinearHT','blueprint','automation'} and str(rel) not in {
                'TrilinearHT.lean','lakefile.toml','lake-manifest.json','lean-toolchain','LICENSE','README.md'}:
                continue
            dest = work/rel; dest.parent.mkdir(parents=True, exist_ok=True); dest.write_bytes(z.read(m))
    if (work/'lean-toolchain').read_text().strip() != TOOLCHAIN: raise ValueError('Toolchain mismatch')
    if (ROOT/'lean-toolchain').read_text().strip() != TOOLCHAIN: raise ValueError('Local toolchain mismatch')
    manifest = json.loads((work/'lake-manifest.json').read_text())
    if not any(p.get('name') == 'mathlib' and p.get('rev') == MATHLIB for p in manifest['packages']):
        raise ValueError('Mathlib revision mismatch')
    if MATHLIB not in (ROOT/'lakefile.toml').read_text(): raise ValueError('Local Mathlib mismatch')
    shutil.copytree(ROOT/'OpenAI086', work/'OpenAI086')
    shutil.copyfile(HERE/'Exact.lean',work/'ReferenceV55Exact.lean')
    shutil.copyfile(HERE/'Full.lean',work/'ReferenceV55Full.lean')
    with (work/'lakefile.toml').open('a') as f:
        f.write('\n[[lean_lib]]\nname = "OpenAI086"\n\n[[lean_lib]]\nname = "ReferenceV55Exact"\n')

def run(cmd, work, logfile):
    print('+', ' '.join(cmd), flush=True)
    with (work/logfile).open('w',encoding='utf8') as out:
        p = subprocess.run(cmd,cwd=work,stdout=out,stderr=subprocess.STDOUT)
    if p.returncode: raise RuntimeError(f'{cmd[0]} failed ({p.returncode}); see {work/logfile}')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('archive',type=Path)
    ap.add_argument('--work-dir',type=Path,required=True,help='New empty workspace (not the original repository)')
    ap.add_argument('--prepare-only',action='store_true')
    ap.add_argument('--exact-only',action='store_true')
    ap.add_argument('--no-cache',action='store_true')
    a=ap.parse_args(); work=a.work_dir.resolve()
    if work.exists() and (not work.is_dir() or any(work.iterdir())):
        print('Refusing to reuse a nonempty workspace.',file=sys.stderr); return 1
    work.mkdir(parents=True,exist_ok=True)
    report={'status':'NOT_VERIFIED','source_commit':COMMIT,'archive_sha256':ARCHIVE_SHA,
            'target_sha256':TARGET_SHA,'lean_toolchain':TOOLCHAIN,'mathlib_commit':MATHLIB,
            'proof_origin':'external_dependency','independent_main_proof':False,'full_paper_certified':False,
            'exact_target_verified':False,'full_target_verified':False}
    def save(): (work/'reference_certificate.json').write_text(json.dumps(report,indent=2)+'\n')
    save()
    try:
        prepare(a.archive.resolve(),work)
        report['status']='SOURCE_PREPARED_NOT_VERIFIED'; save()
        if a.prepare_only: print('Prepared:',work); return 0
        if not shutil.which('lake') or not shutil.which('lean'):
            report['error']='Lean/Lake missing'; save(); print(report['error'],file=sys.stderr); return 2
        run(['lake','--version'],work,'toolchain.log')
        if not a.no_cache: run(['lake','exe','cache','get'],work,'cache.log')
        run(['lake','build','TrilinearHT'],work,'reference_build.log')
        run(['lake','build','+OpenAI086.PaperStatement'],work,'local_target_build.log')
        run(['lake','env','lean','ReferenceV55Exact.lean'],work,'exact_target.log')
        report['exact_axioms']={n:check_axioms((work/'exact_target.log').read_text(),n) for n in EXACT_NAMES}
        report['exact_target_verified']=True; report['status']='KERNEL_VERIFIED_EXTERNAL_EXACT_TARGET'; save()
        if a.exact_only: return 0
        run(['lake','build','ReferenceV55Exact','+OpenAI086.PaperV41MainGoal'],work,'full_dependencies.log')
        run(['lake','env','lean','ReferenceV55Full.lean'],work,'full_target.log')
        report['full_axioms']={n:check_axioms((work/'full_target.log').read_text(),n) for n in FULL_NAMES}
        report['full_target_verified']=True; report['status']='KERNEL_VERIFIED_EXTERNAL_BOTH_TARGETS'; save()
        return 0
    except (OSError,ValueError,RuntimeError,zipfile.BadZipFile) as e:
        report['error']=str(e); save(); print('NOT VERIFIED:',e,file=sys.stderr); return 1

if __name__=='__main__': sys.exit(main())
