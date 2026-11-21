#!/usr/bin/env python3
"""Conservative, STATIC statement/dependency audit. NOT Lean kernel verification."""
from pathlib import Path
import json, re, sys
ROOT=Path(__file__).resolve().parents[1]
paper=(ROOT/'OpenAI086/PaperStatement.lean').read_text()
reduction=(ROOT/'OpenAI086/ConditionalMainTransfer.lean').read_text()
main=(ROOT/'OpenAI086.lean').read_text()
bridge=(ROOT/'verification/candidates/IntegralSignBridge.lean').read_text()
limit=(ROOT/'verification/candidates/PrincipalValueSignTransfer.lean').read_text()
checks={
    'original_exact_PDF_goal_remains_defined':bool(re.search(r'\bdef\s+Theorem1_1_Goal\s*:\s*Prop\b',paper)),
    'pointwise_limit_not_erased': 'Tendsto' in paper and '(𝓝[>] (0 : ℝ))' in paper,
    'minus_shifts_unchanged': all(s in paper for s in ['x - t', 'x - 2*t', 'x - 3*t']),
    'original_goal_has_eLpNorm_L1': 'eLpNorm Tf 1' in paper,
    'original_goal_has_three_L3_inputs': 'eLpNorm (f i) 3' in paper,
    'conditional_bridge_targets_exact_goal':bool(re.search(r'\btheorem\s+Theorem1_1_from_plus_shift\b',reduction)) and 'Theorem1_1_Goal := by' in reduction,
    'conditional_bridge_explicit_plus_convergence': 'PlusShiftPointwiseBound' in reduction,
    'conditional_bridge_explicit_integral_sign': 'hsign :' in reduction,
    'conditional_bridge_explicit_L1_negation': 'hnorm :' in reduction,
    'conditional_bridge_imported': 'import OpenAI086.ConditionalMainTransfer' in main,
    'candidate_integral_change_of_variable': 'integral_neg_eq_self' in bridge and 'integral_indicator hs' in bridge,
    'candidate_principal_value_transfer': 'tendsto_under_global_sign' in limit,
    'no_unconditional_main_proof_claimed': not (ROOT/'OpenAI086/MainProof.lean').exists(),
}
report={'audit':'STATIC_ONLY_NOT_KERNEL_CHECK', 'all_checks_pass':all(checks.values()), 'checks':checks,
        'main_goal_proved':False,'kernel_checked_here':False,
        'candidate_stage':'not imported into core; requires lake build and independent axiom review'}
(ROOT/'verification/reports').mkdir(exist_ok=True,parents=True)
(ROOT/'verification/reports/THEOREM_BRIDGE_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report, indent=2))
sys.exit(0 if all(checks.values()) else 1)
