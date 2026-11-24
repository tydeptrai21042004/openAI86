#!/usr/bin/env python3
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v25_schwartz_lipschitz', 'OpenAI086.v25_paired_uniform', 'OpenAI086.v25_kernel_measurable', 'OpenAI086.v25_paired_measurable', 'OpenAI086.v25_shift_integrable', 'OpenAI086.v25_shift_minus_integrable', 'OpenAI086.v25_kernel_cut_integrable', 'OpenAI086.v25_paired_integrable', 'OpenAI086.v25_cut_pair_identity', 'OpenAI086.v25_pv_tendsto', 'OpenAI086.v25_pair_integrable', 'OpenAI086.v25_T_pv', 'OpenAI086.v25_pair_add_1', 'OpenAI086.v25_T_add_1', 'OpenAI086.v25_pair_smul_1', 'OpenAI086.v25_T_smul_1', 'OpenAI086.v25_pair_add_2', 'OpenAI086.v25_T_add_2', 'OpenAI086.v25_pair_smul_2', 'OpenAI086.v25_T_smul_2', 'OpenAI086.v25_pair_add_3', 'OpenAI086.v25_T_add_3', 'OpenAI086.v25_pair_smul_3', 'OpenAI086.v25_T_smul_3', 'OpenAI086.v25_L1_ae', 'OpenAI086.v25_main_from_concrete_bound', 'OpenAI086.v25_near_weight', 'OpenAI086.v25_far_weight', 'OpenAI086.v25_near_pair_majorant', 'OpenAI086.v25_far_single_majorant', 'OpenAI086.v25_joint_majorant', 'OpenAI086.v25_joint_integrable', 'OpenAI086.v25_pv_spatial_integrable', 'OpenAI086.v25_T_memLp', 'OpenAI086.v25_actual_L1_ae', 'OpenAI086.v25_L1_add_1', 'OpenAI086.v25_L1_smul_1', 'OpenAI086.v25_L1_add_2', 'OpenAI086.v25_L1_smul_2', 'OpenAI086.v25_L1_add_3', 'OpenAI086.v25_L1_smul_3', 'OpenAI086.v25_actual_realization', 'OpenAI086.v25_main_and_extension', 'OpenAI086.v25_symmetric_chart_phase', 'OpenAI086.v25_skew_chart_phase', 'OpenAI086.v25_shell_pool', 'OpenAI086.v25_quadratic_resonance', 'OpenAI086.v25_fourth_moment_pairings', 'OpenAI086.v25_slow_fast_progression', 'OpenAI086.v25_magnitude_power', 'OpenAI086.v25_mixed_magnitude_power', 'OpenAI086.v25_step_assoc', 'OpenAI086.v25_step_inv_right', 'OpenAI086.v25_step_inv_left', 'OpenAI086.v25_right_difference_formula', 'OpenAI086.v25_second_right_difference']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names: print(n, sorted(parse_axioms(log,n)))
except (OSError,IndexError,UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('All V25 component reports accepted; this is not a full-paper certificate.')
