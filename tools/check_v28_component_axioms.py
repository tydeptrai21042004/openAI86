#!/usr/bin/env python3
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v28_translate_sum', 'OpenAI086.v28_star_self', 'OpenAI086.v28_correlation_energy', 'OpenAI086.v28_indexed_cube_factor', 'OpenAI086.v28_sum_fin_three', 'OpenAI086.v28_raw_cube_energy', 'OpenAI086.v28_raw_cube_nonnegative', 'OpenAI086.v28_raw_cube_real', 'OpenAI086.v28_indicator_cube_positive', 'OpenAI086.v28_interval_cube_nonnegative', 'OpenAI086.v28_test_phase_bound', 'OpenAI086.v28_test_phase_exact', 'OpenAI086.v28_compact_test_bound', 'OpenAI086.v28_compact_test_measurable', 'OpenAI086.v28_compact_test_zero', 'OpenAI086.v28_compact_test_pair', 'OpenAI086.v28_compact_testing_L1', 'OpenAI086.v28_scale_primitive_derivative', 'OpenAI086.v28_scale_window_identity']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names: print(n, sorted(parse_axioms(log,n)))
except (OSError,IndexError,UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('All V28 component reports accepted; not a full-paper certificate.')
