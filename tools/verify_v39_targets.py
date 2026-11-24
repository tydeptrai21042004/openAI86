#!/usr/bin/env python3
"""Targeted kernel check. A failed target does not prevent checking others.
No manuscript-wide certificate is inferred from individual declarations.
"""
import argparse, json, shutil, subprocess, sys
from pathlib import Path
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
ROOT=Path(__file__).resolve().parents[1]
REPORT=ROOT/'verification/reports'; REPORT.mkdir(exist_ok=True)
TARGETS={
 '4.3-balls': ('PaperWeylBallPacking', ['v39_shift_sample', 'v39_ball_lower', 'v39_progression_separated', 'v39_disjoint_energy', 'v39_return_bound']),
 '4.3-span': ('PaperWeylSubspace', ['v39_chart_return_phase', 'v39_isotropic_span', 'v39_effective_quadratic']),
 '2.3-accuracy': ('PaperAccuracySummation', ['v39_level_multiplicity', 'v39_geometric_half', 'v39_accuracy_linear_lower', 'v39_accuracy_weighted_sum', 'v39_accuracy_small_coefficient', 'v39_power_accuracy_growth', 'v39_accuracy_infinite', 'v39_paper_accuracy_series']),
 '7.5-three-sides': ('PaperThreeSidePower', ['v39_three_side_pointwise', 'v39_three_side_square_budget', 'v39_three_side_scaled_budget']),
 '3.2-refit': ('PaperCompressionRefit', ['v38_refit_coefficient', 'v38_refit_bound']),
 '3.4-energy': ('PaperCompressionEnergySplit', ['v38_doubling_sum', 'v38_doubling_length', 'v38_split_pointwise', 'v38_integrated_representative_energy']),
 '3.4-measure': ('PaperCompressionMeasureBridge', ['v38_normalized_leaf_jensen', 'v38_restart_increment_lower', 'v38_restart_from_variation']),
 '3.4-maximal': ('PaperCompressionMaximal', ['v37_max_nonneg', 'v37_max_square_step', 'v37_max_adapted', 'v37_weighted_cell_moment', 'v37_weighted_maximal_L2', 'v37_average_moment', 'v37_actual_weighted_maximal_L2']),
 '3.4-rows': ('PaperCompressionVectorRows', ['v37_complex_vector_cs', 'v37_complex_row_error', 'v37_attempt_compression', 'v37_integrated_column_budget']),

 '3.5-wrappers': ('PaperHeightFinalWrappers',['v36_log_scaled', 'v36_scale_iff_window', 'v36_mem_qualifying', 'v36_qualifying_finite', 'v36_height_subfamily_count', 'v36_actual_qualifying_count', 'v36_sup_nonneg', 'v36_sup_mem', 'v36_mem_sup_values', 'v36_sup_value_height', 'v36_sup_log_bins', 'v36_sup_mem_qualifying', 'v36_sup_scale_count', 'v36_sup_real_tail', 'v36_vector_mem_qualifying', 'v36_vector_full_scale_count', 'v36_sup_tail_characterization', 'v36_sup_qualifying_finite', 'v36_vector_qualifying_finite']),
 '3.5-tail': ('PaperHeightTailAssembly',['v35_one_packet_tail','v35_tail_by_bins','v35_tail_infinite','v35_height_tail','v35_height_real_tail']),
 '3.5-vector': ('PaperHeightVectorAssembly',['v35_height_width_bound','v35_vector_comparison','v35_vector_log_cover','v35_vector_bin_count','v35_vector_tail','v35_vector_real_tail','v35_vector_scale_count']),
 '3.5-actual': ('PaperHeightScalarAssembly',['v34_mem_values','v34_no_height_chain','v34_log_packing','v34_height_log_cover','v34_height_scale_count','v34_height_bin_count']),
 '5.3-complex': ('PaperComplexPredictorMoment',['v34_complex_predictor_moment','v34_complex_predictor_increment','v34_predictor_increment_energy']),
 '3.1': ('PaperAttemptTreePacking', ['v29_generation_contraction','v29_attempt_tree_packing']),
 '3.3': ('PaperLemma33Submodules',['v22_submodule_prefix','v22_submodule_variation']),
 '3.5-box': ('PaperHeightBoundedRelation',['v32_integer_relation_from_box','v32_integer_box_dependence']),
 '3.5-chain': ('PaperHeightSeparatedChain',['v32_no_long_cleared_chain']),
 '3.5-cover': ('PaperHeightPacketCover',['v32_separated_net','v32_separated_scale_count','v32_no_bounded_relation_at_maximum']),
 '3.5-erratum': ('PaperHeightScaleCorrection',['v31_no_dimension_free_width','v31_corrected_packet_count']),
}
p=argparse.ArgumentParser(); p.add_argument('--cache',action='store_true'); p.add_argument('--targets',nargs='+',choices=TARGETS,default=list(TARGETS)); args=p.parse_args()
log=REPORT/'V39_TARGETS.log'; out=REPORT/'V39_TARGETS.json'
log.write_text(''); state={'status':'NOT VERIFIED','paper_results_certified':0,'original_3_5_2_refuted_in_ordinary_math':True,'targets':{x:{'status':'NOT RUN'} for x in args.targets}}
def save(): out.write_text(json.dumps(state,indent=2)+'\n')
def note(msg):
    print(msg,flush=True)
    with log.open('a') as f:f.write(msg+'\n')
def run(cmd):
    note('$ '+' '.join(cmd)); r=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    note(r.stdout); return r.returncode,r.stdout
save()
if not shutil.which('lean') or not shutil.which('lake'):
    state['reason']='Lean/Lake unavailable'; note(state['reason']); save(); sys.exit(2)
rc,_=run(['lean','--version'])
if rc: state['reason']='Pinned toolchain invocation failed';save();sys.exit(2)
if not (ROOT/'lake-manifest.json').exists():
    rc,_=run(['lake','update'])
    if rc: state['reason']='Dependency resolution failed';save();sys.exit(2)
if args.cache:
    rc,_=run(['lake','exe','cache','get'])
    if rc: state['reason']='Mathlib cache failed';save();sys.exit(2)
for key in args.targets:
    mod,names=TARGETS[key]; result=state['targets'][key]
    rc,_=run(['lake','build','+OpenAI086.'+mod])
    if rc: result['status']='BUILD FAILED';save();continue
    qualified=['OpenAI086.'+n for n in names]
    check=REPORT/('V39_'+mod+'_check.lean')
    check.write_text('import OpenAI086.'+mod+'\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in qualified)+'\n')
    rc,txt=run(['lake','env','lean',str(check)])
    if rc: result['status']='CHECK FAILED';save();continue
    try: result['axioms']={n:sorted(parse_axioms(txt,n)) for n in qualified}
    except UnrecognizedAxiomReport as ex: result.update(status='AXIOM AUDIT FAILED',reason=str(ex));save();continue
    if any(set(a)-{'propext','Quot.sound','Classical.choice'} for a in result['axioms'].values()):
        result['status']='AXIOM AUDIT FAILED';result['reason']='V39 strict axiom policy';save();continue
    result['status']='DECLARATIONS KERNEL CHECKED';result['scope']='candidate statement fidelity still requires review';save()
passed=sum(r['status']=='DECLARATIONS KERNEL CHECKED' for r in state['targets'].values())
state['status']=f'{passed}/{len(args.targets)} target groups checked; not full paper certification';save();note(state['status']);sys.exit(0 if passed==len(args.targets) else 1)
