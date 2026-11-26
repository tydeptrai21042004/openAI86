#!/usr/bin/env python3
"""Prepare and replay all V76 source tracks using the bundled pinned snapshot.
A successful replay is not a certificate of exact whole-paper fidelity.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'external_main_theorem/v55'))
from verify_snapshot import prepare, ARCHIVE_SHA, COMMIT, TOOLCHAIN, MATHLIB
from axiom_report_parser import parse_axioms
from lean_lex import code_only

BRIDGES = {
    'ReferenceV58Sparse': 'external_main_theorem/v58/SparseCount.lean',
    'ReferenceV59Compression': 'external_main_theorem/v59/Compression.lean',
    'ReferenceV59Weyl': 'external_main_theorem/v59/Weyl.lean',
    'ReferenceV59ShortBlock': 'external_main_theorem/v59/ShortBlock.lean',
    'ReferenceV60CorePath': 'external_main_theorem/v60/CorePath.lean',
    'ReferenceV60Completion': 'external_main_theorem/v60/Completion.lean',
    'ReferenceV61OuterAndStages': 'external_main_theorem/v61/OuterAndStages.lean',
    'ReferenceV61GraphChain': 'external_main_theorem/v61/GraphChain.lean',
    'ReferenceV62ExceptionalSchedule': 'external_main_theorem/v62/ExceptionalSchedule.lean',
    'ReferenceV62EventChains': 'external_main_theorem/v62/EventChains.lean',
    'ReferenceV63JointCounts': 'external_main_theorem/v63/JointCounts.lean',
    'ReferenceV63CorePolynomial': 'external_main_theorem/v63/CorePolynomial.lean',
    'ReferenceV64CompressionAverage': 'external_main_theorem/v64/CompressionAverage.lean',
    'ReferenceV64HeightCorrespondence': 'external_main_theorem/v64/HeightCorrespondence.lean',
    'ReferenceV65ChartOperations': 'external_main_theorem/v65/ChartOperations.lean',
    'ReferenceV65Separation': 'external_main_theorem/v65/Separation.lean',
    'ReferenceV65Detection': 'external_main_theorem/v65/Detection.lean',
    'ReferenceV66Predictors': 'external_main_theorem/v66/Predictors.lean',
    'ReferenceV66ActiveBudget': 'external_main_theorem/v66/ActiveBudget.lean',
    'ReferenceV66Localization': 'external_main_theorem/v66/Localization.lean',
    'ReferenceV67SidePower': 'external_main_theorem/v67/SidePower.lean',
    'ReferenceV67Variation': 'external_main_theorem/v67/Variation.lean',
    'ReferenceV67NearGain': 'external_main_theorem/v67/NearGain.lean',
    'ReferenceV68IntervalVariation': 'external_main_theorem/v68/IntervalVariation.lean',
    'ReferenceV68StackReserve': 'external_main_theorem/v68/StackReserve.lean',
    'ReferenceV68PolylogReserve': 'external_main_theorem/v68/PolylogReserve.lean',
    'ReferenceV69ComponentComparison': 'external_main_theorem/v69/ComponentComparison.lean',
    'ReferenceV69TopBins': 'external_main_theorem/v69/TopBins.lean',
    'ReferenceV69TopReserve': 'external_main_theorem/v69/TopReserve.lean',
    'ReferenceV70PaperTypes': 'external_main_theorem/v70/PaperTypes.lean',
    'ReferenceV70PaperCounting': 'external_main_theorem/v70/PaperCounting.lean',
    'ReferenceV70TypeReserve': 'external_main_theorem/v70/TypeReserve.lean',
    'ReferenceV71PaperDensity': 'external_main_theorem/v71/PaperDensity.lean',
    'ReferenceV71PaperMasks': 'external_main_theorem/v71/PaperMasks.lean',
    'ReferenceV72PaperEventEnergy': 'external_main_theorem/v72/PaperEventEnergy.lean',
    'ReferenceV72PaperLocalForms': 'external_main_theorem/v72/PaperLocalForms.lean',
    'ReferenceV73PaperGlobalEnergy': 'external_main_theorem/v73/PaperGlobalEnergy.lean',
    'ReferenceV73PaperRollingEnergy': 'external_main_theorem/v73/PaperRollingEnergy.lean',
    'ReferenceV74PaperFixedStacks': 'external_main_theorem/v74/PaperFixedStacks.lean',
    'ReferenceV75PaperFirstTops': 'external_main_theorem/v75/PaperFirstTops.lean',
    'ReferenceV75PaperTopCount': 'external_main_theorem/v75/PaperTopCount.lean',
    'ReferenceV76PaperTorus': 'external_main_theorem/v76/PaperTorus.lean',
    'ReferenceV76PaperPathTests': 'external_main_theorem/v76/PaperPathTests.lean',
}
STATIC = ['check_project_integrity.py', 'check_registry_integrity.py',
          'check_independent_target.py', 'check_all_59_lean_targets.py',
          'lean_source_safety.py', 'test_v60_models.py', 'test_v61_models.py', 'test_v62_models.py',
          'test_axiom_report_parser.py']
PAPER_SHA = '24b584066ae76b2f28dc03d32a2b0a2cdc3b4f92e0e82f4a3d133f28ccc5a936'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--work-dir', type=Path, default=ROOT / '.final-replay')
    p.add_argument('--prepare-only', action='store_true')
    p.add_argument('--main-only', action='store_true', help='Replay reference and both main bridges only')
    p.add_argument('--strict-axioms', action='store_true', help='Require only propext, Classical.choice and Quot.sound')
    p.add_argument('--no-cache', action='store_true', help='Skip the Mathlib cache download')
    a = p.parse_args()
    w = a.work_dir.resolve()
    if w.exists() and (not w.is_dir() or any(w.iterdir())):
        p.error('Use a new empty --work-dir; existing logs will not be overwritten.')
    w.mkdir(parents=True, exist_ok=True)
    report = {'status': 'NOT VERIFIED', 'reference_commit': COMMIT,
              'reference_archive_sha256': ARCHIVE_SHA, 'toolchain': TOOLCHAIN,
              'mathlib_commit': MATHLIB, 'scope': 'main-only' if a.main_only else 'all',
              'independent_main_proved': False, 'full_paper_certified': False,
              'strict_axioms': a.strict_axioms, 'checks': {}}
    def save():
        (w / 'final_verification.json').write_text(json.dumps(report, indent=2)+'\n')
    def run(key, cmd, cwd):
        log = w / (key+'.log')
        print('>', key, flush=True)
        with log.open('w', encoding='utf-8') as out:
            ret = subprocess.run(cmd, cwd=cwd, stdout=out, stderr=subprocess.STDOUT)
        report['checks'][key] = {'exit_code': ret.returncode, 'status': 'PASS' if ret.returncode == 0 else 'FAILED', 'log': log.name}
        save()
        return ret.returncode == 0
    def audit(key, path):
        targets = re.findall(r'^#print axioms (\S+)\s*$', code_only(path.read_text()), re.M)
        if not targets:
            raise ValueError('Missing axiom checks in '+str(path))
        ok = run(key, ['lake', 'env', 'lean', str(path.relative_to(w))], w)
        if ok:
            try:
                out = (w/(key+'.log')).read_text()
                report['checks'][key]['axioms'] = {n: sorted(parse_axioms(out, n)) for n in targets}
                if a.strict_axioms:
                    for n, axioms in report['checks'][key]['axioms'].items():
                        if set(axioms) - {'propext', 'Classical.choice', 'Quot.sound'}:
                            raise ValueError('Strict axiom policy rejected '+n+': '+str(axioms))
                report['checks'][key]['status'] = 'KERNEL CHECKED; PAPER FIDELITY REVIEW REQUIRED'
            except ValueError as ex:
                report['checks'][key].update(status='FAILED AXIOM AUDIT', error=str(ex)); ok = False
            save()
        return ok
    save()
    try:
        if hashlib.sha256((ROOT/'paper(7).pdf').read_bytes()).hexdigest() != PAPER_SHA:
            raise ValueError('Original paper hash mismatch')
        for name in STATIC:
            if not run(name.removesuffix('.py'), [sys.executable, str(ROOT/'tools'/name)], ROOT):
                raise RuntimeError('Static check failed: '+name)
        prepare(ROOT/'reference_snapshot/lean-trilinearht.zip', w)
        for name, rel in BRIDGES.items():
            shutil.copyfile(ROOT/rel, w/(name+'.lean'))
        shutil.copyfile(ROOT/'final_source/FinalMain.lean', w/'FinalMain.lean')
        for name in ('OpenAI086.lean','OpenAI086Whole.lean'):
            shutil.copyfile(ROOT/name, w/name)
        shutil.copytree(ROOT/'source_fidelity', w/'source_fidelity')
        with (w/'lakefile.toml').open('a') as f:
            f.write('\n[[lean_lib]]\nname = "ReferenceV55Full"\n\n[[lean_lib]]\nname = "OpenAI086Whole"\n\n[[lean_lib]]\nname = "ReferenceV60CorePath"\n\n[[lean_lib]]\nname = "ReferenceV59Compression"\n')
            f.write('\n[[lean_lib]]\nname = "ReferenceV66ActiveBudget"\n\n[[lean_lib]]\nname = "ReferenceV70PaperTypes"\n\n[[lean_lib]]\nname = "ReferenceV70PaperCounting"\n')
            f.write('\n[[lean_lib]]\nname = "ReferenceV71PaperDensity"\n\n[[lean_lib]]\nname = "ReferenceV72PaperEventEnergy"\n')
            f.write('\n[[lean_lib]]\nname = "ReferenceV72PaperLocalForms"\n\n[[lean_lib]]\nname = "ReferenceV73PaperGlobalEnergy"\n\n[[lean_lib]]\nname = "ReferenceV73PaperRollingEnergy"\n')
            f.write('\n[[lean_lib]]\nname = "ReferenceV75PaperFirstTops"\n\n[[lean_lib]]\nname = "ReferenceV76PaperTorus"\n')
        # Standalone adapted dependencies are compiled as separate Lake libraries.
        for name, rel in {'SourceV56EntryRank': 'source_fidelity/v56/EntryRank.lean',
                          'SourceV60CoreSummation': 'source_fidelity/v60/CoreSummation.lean',
                          'SourceV61WeightedCore': 'source_fidelity/v61/WeightedCore.lean',
                          'SourceV62PathCore': 'source_fidelity/v62/PathCore.lean',
                          'SourceV64PaperExceptional': 'source_fidelity/v64/PaperExceptional.lean'}.items():
            shutil.copyfile(ROOT/rel, w/(name+'.lean'))
            with (w/'lakefile.toml').open('a') as f:
                f.write('\n[[lean_lib]]\nname = "'+name+'"\n')
        sources = [w/'ReferenceV55Exact.lean', w/'ReferenceV55Full.lean', w/'FinalMain.lean']
        sources += [w/(n+'.lean') for n in BRIDGES]
        sources += sorted((w/'source_fidelity').glob('v*/*.lean'))
        forbidden = re.compile(r'\b(sorry|admit|axiom|constant|opaque|unsafe|native_decide)\b')
        for source in sources:
            if forbidden.search(code_only(source.read_text())):
                raise ValueError('Forbidden source construct in '+str(source))
        report['prepared_source_files'] = len(sources)
        report['status'] = 'SOURCE PREPARED NOT VERIFIED'; save()
        if a.prepare_only:
            print('Prepared:', w, '(no kernel checks performed)'); return 0
        if not shutil.which('lean') or not shutil.which('lake'):
            report['status'] = 'BLOCKED: Lean/Lake unavailable'; save(); print(report['status']); return 2
        if not run('toolchain', ['lake', 'env', 'lean', '--version'], w):
            raise RuntimeError('Toolchain unavailable')
        if not a.no_cache and not run('cache', ['lake','exe','cache','get'], w):
            raise RuntimeError('Mathlib cache acquisition failed; see cache.log')
        ok = run('reference_build', ['lake','build','TrilinearHT'], w)
        if ok:
            exact = run('exact_dependencies', ['lake','build','+OpenAI086.PaperStatement'], w)
            if exact:
                exact = audit('exact_main', w/'ReferenceV55Exact.lean')
            full = exact and run('full_dependencies', ['lake','build','ReferenceV55Exact','+OpenAI086.PaperV41MainGoal'], w)
            if full:
                full = audit('full_main', w/'ReferenceV55Full.lean')
            final = full and run('final_dependencies', ['lake','build','ReferenceV55Full'], w)
            if final:
                final = audit('final_main', w/'FinalMain.lean')
            ok = bool(final)
            if not a.main_only:
                for name in BRIDGES:
                    if name in ('ReferenceV61GraphChain', 'ReferenceV62EventChains', 'ReferenceV70PaperTypes'):
                        if not run(name+'_dependencies', ['lake','build','SourceV56EntryRank'],w):
                            ok = False; continue
                    if name == 'ReferenceV63JointCounts':
                        if not run(name+'_dependencies', ['lake','build','ReferenceV60CorePath'],w):
                            ok = False; continue
                    if name == 'ReferenceV64CompressionAverage':
                        if not run(name+'_dependencies', ['lake','build','ReferenceV59Compression'],w):
                            ok = False; continue
                    if name == 'ReferenceV64HeightCorrespondence':
                        if not run(name+'_dependencies', ['lake','build','SourceV64PaperExceptional'],w):
                            ok = False; continue
                    if name == 'ReferenceV66Localization':
                        if not run(name+'_dependencies', ['lake','build','ReferenceV66ActiveBudget'],w):
                            ok = False; continue
                    if name in ('ReferenceV70PaperCounting', 'ReferenceV70TypeReserve', 'ReferenceV71PaperDensity'):
                        if not run(name+'_dependencies', ['lake','build','SourceV56EntryRank','ReferenceV70PaperTypes'],w):
                            ok = False; continue
                    if name == 'ReferenceV71PaperMasks':
                        if not run(name+'_dependencies', ['lake','build','SourceV56EntryRank','ReferenceV70PaperTypes','ReferenceV70PaperCounting'],w):
                            ok = False; continue
                    if name in ('ReferenceV72PaperEventEnergy', 'ReferenceV72PaperLocalForms'):
                        targets = ['SourceV56EntryRank', 'ReferenceV70PaperTypes', 'ReferenceV71PaperDensity']
                        if name == 'ReferenceV72PaperLocalForms':
                            targets.append('ReferenceV72PaperEventEnergy')
                        if not run(name+'_dependencies', ['lake','build',*targets], w):
                            ok = False; continue
                    if name in ('ReferenceV73PaperGlobalEnergy', 'ReferenceV73PaperRollingEnergy'):
                        targets = ['SourceV56EntryRank', 'ReferenceV70PaperTypes', 'ReferenceV71PaperDensity', 'ReferenceV72PaperEventEnergy']
                        if name == 'ReferenceV73PaperRollingEnergy':
                            targets += ['ReferenceV72PaperLocalForms', 'ReferenceV73PaperGlobalEnergy']
                        if not run(name+'_dependencies', ['lake','build',*targets], w):
                            ok = False; continue
                    if name == 'ReferenceV74PaperFixedStacks':
                        targets = ['SourceV56EntryRank', 'ReferenceV70PaperTypes', 'ReferenceV71PaperDensity', 'ReferenceV72PaperEventEnergy', 'ReferenceV72PaperLocalForms', 'ReferenceV73PaperGlobalEnergy', 'ReferenceV73PaperRollingEnergy']
                        if not run(name+'_dependencies', ['lake','build',*targets], w):
                            ok = False; continue
                    if name in ('ReferenceV75PaperFirstTops', 'ReferenceV75PaperTopCount', 'ReferenceV76PaperTorus', 'ReferenceV76PaperPathTests'):
                        targets = ['SourceV56EntryRank', 'ReferenceV70PaperTypes', 'ReferenceV71PaperDensity', 'ReferenceV72PaperEventEnergy', 'ReferenceV72PaperLocalForms', 'ReferenceV73PaperGlobalEnergy']
                        if name != 'ReferenceV75PaperFirstTops':
                            targets.append('ReferenceV75PaperFirstTops')
                        if name == 'ReferenceV76PaperPathTests':
                            targets.append('ReferenceV76PaperTorus')
                        if not run(name+'_dependencies', ['lake','build',*targets], w):
                            ok = False; continue
                    ok = audit(name, w/(name+'.lean')) and ok
        if not a.main_only:
            for source in sorted((w/'source_fidelity').glob('v*/*.lean')):
                if source.stem == 'WeightedCore':
                    if not run('v61_core_dependencies',['lake','build','SourceV60CoreSummation'],w):
                        ok = False; continue
                if source.stem == 'PathCore':
                    if not run('v62_path_dependencies',['lake','build','SourceV61WeightedCore'],w):
                        ok = False; continue
                if source.stem == 'SideEnergy':
                    if not run('v62_side_dependencies',['lake','build','SourceV62PathCore','+OpenAI086.PaperV51Prop89Assembly'],w):
                        ok = False; continue
                if source.stem == 'PaperExceptional':
                    if not run('v64_exceptional_dependencies',['lake','build','SourceV64PaperExceptional'],w):
                        ok = False; continue
                if source.stem == 'IndependentMilestones':
                    modules = ['PaperV43Packing','PaperV56Lemma32','PaperV43Lemma33','PaperHeightFinalWrappers',
                               'PaperV56ExceptionalBlocks','PaperV51Prop89Assembly','OuterStopping']
                    if not run('v61_independent_dependencies',['lake','build'] + ['+OpenAI086.'+m for m in modules],w):
                        ok = False; continue
                ok = audit(source.parent.name+'_'+source.stem, source) and ok
            ok = run('independent_build',['lake','build','OpenAI086Whole'],w) and ok
        report['status'] = ('SELECTED SOURCE TARGETS KERNEL CHECKED; WHOLE PAPER NOT CERTIFIED'
                            if ok else 'FAILED OR PARTIAL')
        save(); print(report['status']); return 0 if ok else 1
    except (OSError, RuntimeError, ValueError) as ex:
        report['status']='FAILED'; report['error']=str(ex); save(); print(ex,file=sys.stderr); return 1

if __name__ == '__main__':
    sys.exit(main())
