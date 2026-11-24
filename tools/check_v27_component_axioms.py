#!/usr/bin/env python3
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v27_return_antisymmetry', 'OpenAI086.v27_integral_skew_zero', 'OpenAI086.v27_return_energy_obstruction', 'OpenAI086.v27_scale_row_sum', 'OpenAI086.v27_clump_coefficient', 'OpenAI086.v27_geometric_tail', 'OpenAI086.v27_predictor_tail_bound', 'OpenAI086.v27_predictor_catalog', 'OpenAI086.v27_tiny_frequency_marginal', 'OpenAI086.v27_constant_marginal', 'OpenAI086.v27_mixed_curvature', 'OpenAI086.v27_halving_witness', 'OpenAI086.v27_integer_carry', 'OpenAI086.v27_common_quadratic', 'OpenAI086.v27_same_tag_moment_bound', 'OpenAI086.V27SplitTree.v27_leaf_sum', 'OpenAI086.v27_localization_split', 'OpenAI086.v27_localization_error']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names: print(n, sorted(parse_axioms(log,n)))
except (OSError,IndexError,UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('All V27 component reports accepted; not a full-paper certificate.')
