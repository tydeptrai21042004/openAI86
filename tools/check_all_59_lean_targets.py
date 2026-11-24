#!/usr/bin/env python3
"""Audit Lean TARGET COVERAGE (not theorem correctness or kernel verification)."""
from pathlib import Path
from collections import Counter
import hashlib,json,re,sys

root=Path(__file__).resolve().parents[1]
index=json.loads((root/'verification/PAPER_RESULTS_INDEX.json').read_text())
items=index['results']
problems=[]
if len(items)!=59:problems.append(f'inventory has {len(items)} rather than 59 results')
if len({(i['kind'],i['number']) for i in items})!=59:problems.append('duplicate result keys')
partial=target_only=0
for it in items:
    key=it['kind']+' '+it['number']
    level=it.get('lean_target_level')
    if not it.get('relevant_modules'):
        problems.append(key+': missing Lean module mapping')
    for m in it.get('relevant_modules',[]):
        if not (root/m).is_file():problems.append(key+': missing '+m)
    if it['formalization']=='open':
        target_only+=1
        if level!='typed_finite_proxy_only':problems.append(key+': wrong coverage label')
        p=root/f"OpenAI086/PaperTargets/Result_{it['number'].replace('.','_')}.lean"
        if not p.exists():problems.append(key+': expected proxy goal file absent');continue
        s=p.read_text()
        if 'STATUS: TYPED FINITE MODEL ONLY. NOT THE PAPER STATEMENT OR PROOF.' not in s:
            problems.append(key+': safety label missing')
        decl=f"def result_{it['number'].replace('.','_')}_model_goal"
        if decl not in s:
            problems.append(key+': missing typed Lean goal declaration')
        if any(re.search(r'\b'+bad+r'\b',s) for bad in ('sorry','admit','axiom')):
            problems.append(key+': forbidden placeholder in target file')
        if it.get('lean_target_is_paper_statement') is not False:
            problems.append(key+': finite proxy incorrectly labeled as paper statement')
    elif it['formalization']=='partial':
        partial+=1
        if level!='partial_component_exists':problems.append(key+': expected partial-source label')
    else:
        problems.append(key+': unexpected formalization status '+str(it['formalization']))
if partial!=59:problems.append(f'partial should be 59 but is {partial}')
if target_only!=0:problems.append(f'target-only should be 0 but is {target_only}')
for name in ('OpenAI086/PaperTargets/Catalog.lean','OpenAI086/PaperTargets/Models.lean',
             'OpenAI086/PaperTargets.lean','OpenAI086/FiniteDyadicOperatorBridge.lean'):
    if not (root/name).is_file():problems.append('missing infrastructure '+name)

status=json.loads((root/'STATUS.json').read_text())
if status.get('numbered_results_with_typed_target_index')!=59:problems.append('status target count stale')
if status.get('theorem_1_1_proved') or status.get('lean_kernel_build_verified_here'):
    problems.append('false completion claim')
# V7 promotions must have a substantive mapped module and checked entrypoint;
# typed finite proxy declarations remain in place and are NOT paper statements.
v7 = {
    '5.5': ('FiniteFourSlotIncrementExpansion', 'finite_two_slot_increment_expansion'),
    '6.2': ('FinitePathTelescoping', 'finite_path_endpoint_bound'),
    '6.4': ('FiniteCatalogClosure', 'finite_catalog_iterate_in_closed_set'),
    '6.7': ('FiniteCatalogQuantitative', 'finite_catalog_iterate_card_growth'),
}
for number,(module,theorem) in v7.items():
    item=next((i for i in items if i['number']==number),None)
    if item is None or item['formalization']!='partial':
        problems.append('V7 mapping missing/incorrect: '+number)
        continue
    source='OpenAI086/'+module+'.lean'
    target=root/'OpenAI086/PaperTargets'/('Result_'+number.replace('.','_')+'.lean')
    if source not in item.get('relevant_modules',[]):
        problems.append('V7 source not mapped: '+number)
    source_file=root/source
    if not source_file.is_file() or not re.search(r'^theorem\s+'+re.escape(theorem)+r'\b',source_file.read_text(),re.M):
        problems.append('V7 proof declaration missing: '+number)
    if not target.is_file() or '#check OpenAI086.'+theorem not in target.read_text():
        problems.append('V7 target lacks proof-component crosscheck: '+number)

# V26 direct component crosswalk; never treat a component as a full result.
v26 = {'4.6': ('PaperSingleScaleModulation', 'v26_progression_modulation'), '4.10': ('PaperInverseSeparation', 'v26_inverse_separator_contradiction'), '4.11': ('PaperPairL1Form', 'v26_pair_coordinate_L1'), '4.12': ('PaperDetectionExtraction', 'v26_weighted_pair_witness'), '5.4': ('PaperGreedyInsertion', 'v26_fresh_moment_jump'), '5.6': ('PaperGreedyInsertion', 'v26_child_moment_energy'), '5.8': ('PaperActiveMinimum', 'v26_cell_min_expansion'), '6.3': ('PaperColorEpisodes', 'v26_winner_shift_injective'), '7.4': ('PaperRollingSideStacks', 'v26_select_matched_band')}
for number,(module,theorem) in v26.items():
    item=next(i for i in items if i['number']==number)
    source='OpenAI086/'+module+'.lean'
    if item['formalization']!='partial' or item['kernel_verified'] or source not in item['relevant_modules']:
        problems.append('V26 mapping missing/incorrect: '+number)
    if not re.search(r'^theorem\s+'+re.escape(theorem)+r'\b',(root/source).read_text(),re.M):
        problems.append('V26 declaration missing: '+number)


# V27 component crosswalk, no promotion to a full proof.
v27 = {'4.3': ('PaperWeylReturns', 'v27_return_antisymmetry'), '5.1': ('PaperScaleRowSummation', 'v27_scale_row_sum'), '5.2': ('PaperPredictorTruncation', 'v27_predictor_tail_bound'), '5.7': ('PaperActiveMarginal', 'v27_tiny_frequency_marginal'), '6.1': ('PaperTagMixedCurvature', 'v27_mixed_curvature'), '6.6': ('PaperSameTagMoments', 'v27_same_tag_moment_bound'), '6.8': ('PaperBinaryLocalization', 'v27_localization_error')}
for number,(module,theorem) in v27.items():
    item=next(i for i in items if i['number']==number)
    source='OpenAI086/'+module+'.lean'
    if item['formalization']!='partial' or item['kernel_verified'] or source not in item['relevant_modules']:
        problems.append('V27 mapping missing/incorrect: '+number)
    if not re.search(r'^theorem\s+'+re.escape(theorem)+r'\b',(root/source).read_text(),re.M):
        problems.append('V27 declaration missing: '+number)
external=next(i for i in items if i['number']=='4.7')
if external['formalization']!='partial' or external['kernel_verified'] or external.get('full_quantitative_inverse_open') is not True:
    problems.append('4.7 must be partial only; full quantitative inverse remains open')
for module, theorem in [('PaperInverseDerivative','v30_interval_inverse_first_step'),
                        ('PaperInverseExtremal','v30_extremal_interval_quadratic'),
                        ('PaperInverseExtremal','v30_extremal_interval_correlation')]:
    source='OpenAI086/'+module+'.lean'
    if source not in external['relevant_modules'] or not re.search(r'^theorem\s+'+theorem+r'\b',(root/source).read_text(),re.M):
        problems.append('4.7 restricted inverse component missing: '+theorem)

# Optional paper byte-for-byte check when the current PDF is present.
paper=next((q for q in (Path('/mnt/data/paper(5).pdf'), Path('/mnt/data/paper(4).pdf'),
    Path('/mnt/data/paper(3).pdf'), Path('/mnt/data/paper (2).pdf')) if q.is_file()), None)
if paper is not None:
    h=hashlib.sha256(paper.read_bytes()).hexdigest()
    if h!=index['paper_sha256']:
        problems.append('current paper PDF SHA256 does not match indexed paper')

result={'audit':'59_lean_target_entrypoints_not_paper_proofs',
        'total':len(items),'partial_components':partial,'finite_proxy_goals_only':target_only,
        'complete_kernel_verified':0,'current_paper_sha_match':paper is not None and not any('SHA256' in p for p in problems),
        'errors':problems}
print(json.dumps(result,ensure_ascii=False,indent=2))
sys.exit(bool(problems))
