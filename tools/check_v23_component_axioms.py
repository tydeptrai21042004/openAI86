#!/usr/bin/env python3
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v23_restrict_ae', 'OpenAI086.v23_L2_disjoint_support', 'OpenAI086.v23_restrict_orthogonal', 'OpenAI086.v23_rescaled_cramer_l1', 'OpenAI086.v23_cramer_tiny_gap', 'OpenAI086.v23_power_quotient_lift', 'OpenAI086.v23_shift_descends', 'OpenAI086.v23_power_quotient_lift_gcd', 'OpenAI086.v23_last_separation', 'OpenAI086.v23_overlap_grid_constant', 'OpenAI086.v23_first_top_exists', 'OpenAI086.v23_first_top_unique', 'OpenAI086.v23_first_top_whole_cell', 'OpenAI086.v23_certified_variation_split', 'OpenAI086.v23_certified_variation_energy', 'OpenAI086.v23_two_frequency_equations', 'OpenAI086.v23_amplitude_exponents', 'OpenAI086.v23_oscillatory_ibp_bound', 'OpenAI086.v23_small_slope_oscillatory_bound', 'OpenAI086.v23_private_lift_energy']
names += ['OpenAI086.v23_cleared_minor_nonsingular', 'OpenAI086.v23_bounded_height_square_system']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names: print(n, sorted(parse_axioms(log,n)))
except (OSError,IndexError,UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('All new component axiom reports accepted. This does not certify full paper results.')
