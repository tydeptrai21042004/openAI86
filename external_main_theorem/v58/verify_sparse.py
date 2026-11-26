#!/usr/bin/env python3
"""Replay the exact pinned reference and paper-exponent sparse-count bridge."""
import argparse, json, shutil, subprocess, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'v55'))
from verify_snapshot import prepare, ARCHIVE_SHA, COMMIT
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from axiom_report_parser import parse_axioms

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('archive',type=Path)
    p.add_argument('--work-dir',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');p.add_argument('--no-cache',action='store_true');a=p.parse_args()
    w=a.work_dir.resolve()
    if w.exists() and (not w.is_dir() or any(w.iterdir())):p.error('Work directory must be empty')
    w.mkdir(parents=True,exist_ok=True)
    r={'status':'NOT VERIFIED','proof_origin':'reference_dependency','source_commit':COMMIT,'archive_sha256':ARCHIVE_SHA,'full_paper_certified':False,'independent_lemma91_certified':False}
    def save(): (w/'sparse_certificate.json').write_text(json.dumps(r,indent=2)+'\n')
    def run(cmd,name):
        x=subprocess.run(cmd,cwd=w,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (w/name).write_text(x.stdout)
        if x.returncode:raise RuntimeError(f'{cmd} failed; see {w/name}')
        return x.stdout
    try:
        prepare(a.archive.resolve(),w)
        shutil.copyfile(HERE/'SparseCount.lean',w/'ReferenceV58Sparse.lean')
        r['status']='SOURCE PREPARED NOT VERIFIED';save()
        if a.prepare_only:return 0
        if not shutil.which('lake') or not shutil.which('lean'):
            r['status']='BLOCKED: Lean/Lake unavailable';save();return 2
        if not a.no_cache:run(['lake','exe','cache','get'],'cache.log')
        run(['lake','build','+TrilinearHT.Auto.Sec15_3FiniteSparseCountLemma'],'build.log')
        out=run(['lake','env','lean','ReferenceV58Sparse.lean'],'sparse.log')
        r['axioms']=sorted(parse_axioms(out,'OpenAI086.ReferenceV58.lemma91'))
        r['status']='KERNEL CHECKED REFERENCE-BACKED; PAPER FIDELITY REVIEW REQUIRED';save();return 0
    except Exception as e:
        r['error']=str(e);save();print(e,file=sys.stderr);return 1
if __name__=='__main__':sys.exit(main())
