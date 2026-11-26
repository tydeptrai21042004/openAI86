#!/usr/bin/env python3
"""Kernel check of explicit source candidates, with strict axiom allowlist.
A checked component is NOT automatically a certified full paper result.
"""
from pathlib import Path
import json, shutil, subprocess, sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
ROOT = Path(__file__).resolve().parents[1]
MODULES = {
    'PaperV54StageRefit': ['v54_global_projection_eq_local_sum', 'v54_masked_column_refinement', 'v54_masked_stage_span_step'],
    'PaperV54GreedyBlocks': ['v54_greedy_flatten', 'v54_greedy_mass_bounds'],
    'PaperV54FourthMoment': ['v54_integer_resonance', 'v54_resonant_fourth_mass', 'v54_resonant_complex_product', 'v54_complex_fourth_mass'],
    'PaperV54ChartPhase': ['v54_chart_bilinear_increment', 'v54_chart_total_increment', 'v54_chart_increment_mod_integer'],
    'PaperV54RetainedAbsorption': ['v54_retained_quality_power'],

    'PaperV43Packing': ['v43_lemma31'],
    'ChronologicalHarmonic': ['chronological_exception_fraction_harmonic'],
    'PaperV41Section3': ['v41_scalar_height_assembly'],
    'PaperV42HeightCounterexample': ['v42_actual_height_obstruction'],
    'PaperV52ParameterOrder': ['v52_choose_parameter_order'],
    'PaperV52SparseNonfuture': ['v52_six_nonfuture_pair_mass'],
    'PaperV53ParameterCompletion': ['v53_small_base_power','v53_ceiling_bounds','v53_ceiling_power',
        'v53_main_power','v53_polynomial_side_cost','v53_ceiling_inverse_quarter'],
    'PaperV53WeylIntegral': ['v53_integral_modulation_error','v53_integrated_sample_propagation'],
    'PaperV53SparseExponent': ['v53_sparse_auxiliary_powers','v53_sparse_small_density','v53_sparse_all_density'],
}

def main():
    out = ROOT/'verification'/'reports'/'V54'
    out.mkdir(parents=True, exist_ok=True)
    report = {'full_paper_certified': False, 'targets': {}}
    for module, names in MODULES.items():
        for name in names:
            report['targets'][name] = {'module': 'OpenAI086.'+module,
                'constant': 'OpenAI086.'+name, 'status': 'NOT RUN'}
    def save():
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    if not shutil.which('lean') or not shutil.which('lake'):
        for entry in report['targets'].values(): entry['status'] = 'BLOCKED: Lean/Lake unavailable'
        save(); print('BLOCKED: Lean/Lake unavailable; no kernel certificate issued.'); return 2
    build = subprocess.run(['lake','build','OpenAI086Whole'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/'build.log').write_text(build.stdout)
    if build.returncode:
        for entry in report['targets'].values(): entry['status'] = 'BLOCKED: whole-project build failed'
        save(); print(build.stdout); return 1
    failed = False
    for name, entry in report['targets'].items():
        theorem = entry['constant']
        check = out/(name+'.lean')
        check.write_text(f"import {entry['module']}\n#check {theorem}\n#print axioms {theorem}\n")
        proc = subprocess.run(['lake','env','lean',str(check)],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/(name+'.log')).write_text(proc.stdout)
        try:
            if proc.returncode: raise ValueError('Lean exited nonzero')
            entry['axioms'] = sorted(parse_axioms(proc.stdout,theorem))
            entry['status'] = 'COMPONENT KERNEL CHECKED; statement fidelity review required'
        except ValueError as err:
            entry['status'] = 'FAILED: '+str(err); failed=True
        print(name+': '+entry['status'])
        save()
    return int(failed)

if __name__ == '__main__': sys.exit(main())
