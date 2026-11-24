#!/usr/bin/env python3
from pathlib import Path
import sys
from axiom_report_parser import parse_axioms, UnrecognizedAxiomReport
names = ['OpenAI086.v24_extend_family_agrees', 'OpenAI086.v24_extend_family_norm', 'OpenAI086.v24_dense_clm_ext', 'OpenAI086.v24_third_agrees', 'OpenAI086.v24_third_norm', 'OpenAI086.v24_second_agrees', 'OpenAI086.v24_second_norm', 'OpenAI086.v24_extension_agrees', 'OpenAI086.v24_extension_opNorm', 'OpenAI086.v24_extension_product_bound', 'OpenAI086.v24_extension_unique', 'OpenAI086.v24_schwartz_dense', 'OpenAI086.v24_L3_extension', 'OpenAI086.v24_weighted_band_transfer', 'OpenAI086.v24_band_weight_difference', 'OpenAI086.v24_terminal_band_weight', 'OpenAI086.v24_outgoing_band_identity', 'OpenAI086.v24_min_add_error', 'OpenAI086.v24_min_power', 'OpenAI086.v24_min_power_with_error', 'OpenAI086.v24_weighted_min_assembly', 'OpenAI086.v24_geometric_quarter', 'OpenAI086.v24_restart_packing', 'OpenAI086.v24_level_absorption', 'OpenAI086.truncated_kernel_integral_sign', 'OpenAI086.three_factor_prod', 'OpenAI086.truncationSignBridge', 'OpenAI086.v24_main_from_plus_bound', 'OpenAI086.v24_L1_ofReal_norm', 'OpenAI086.v24_L3_ofReal_norm', 'OpenAI086.v24_main_and_extension']
try:
    log=Path(sys.argv[1]).read_text()
    for n in names: print(n, sorted(parse_axioms(log,n)))
except (OSError,IndexError,UnrecognizedAxiomReport) as e:
    sys.exit(f'NOT VERIFIED: {e}')
print('All V24 component reports accepted; this is not a full-paper certificate.')
