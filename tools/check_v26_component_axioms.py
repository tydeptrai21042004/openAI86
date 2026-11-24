#!/usr/bin/env python3
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v26_progression_modulation_phase', 'OpenAI086.v26_progression_modulation', 'OpenAI086.v26_multiplier_energy', 'OpenAI086.v26_inverse_separator_contradiction', 'OpenAI086.v26_decomposition_closure_error', 'OpenAI086.v26_pair_coordinate_L1', 'OpenAI086.v26_weighted_witness', 'OpenAI086.v26_weighted_pair_witness', 'OpenAI086.v26_clipping_tail_pointwise', 'OpenAI086.v26_clipping_tail_integral', 'OpenAI086.v26_fresh_moment_jump', 'OpenAI086.v26_insertion_energy_charge', 'OpenAI086.v26_child_moment_energy', 'OpenAI086.v26_active_union_count', 'OpenAI086.v26_min_subadd', 'OpenAI086.v26_min_sum', 'OpenAI086.v26_cell_min_expansion', 'OpenAI086.v26_marked_unique', 'OpenAI086.v26_fixed_top_winner', 'OpenAI086.v26_mark_failure_persists', 'OpenAI086.v26_shift_winner_marked', 'OpenAI086.v26_winner_shift_injective', 'OpenAI086.v26_rolling_stack_increment', 'OpenAI086.v26_side_prefix_telescoping', 'OpenAI086.v26_select_matched_band']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names: print(n, sorted(parse_axioms(log,n)))
except (OSError,IndexError,UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('All V26 component reports accepted; not a full-paper certificate.')
