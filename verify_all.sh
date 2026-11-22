#!/usr/bin/env bash
# Full Lean project: fail if ANY part, including all independent proof modules, fails.
set -euo pipefail
cd "$(dirname "$0")"
python3 tools/check_project_integrity.py
python3 tools/check_independent_target.py
python3 tools/test_symmetric_numerator.py
python3 tools/test_local_pv_cancellation.py
python3 tools/test_paired_kernel.py
python3 tools/check_registry_integrity.py
python3 tools/check_all_59_lean_targets.py
python3 tools/scope_audit.py
python3 tools/static_audit.py
python3 tools/lean_source_safety.py
python3 tools/paper_obligation_report.py
python3 tools/sympy_check.py
python3 tools/test_noncommuting_numeric.py
python3 tools/test_lemma33_numeric.py
python3 tools/test_lemma33_complex_stress.py
python3 tools/test_new_components_numeric.py
python3 tools/test_continuation_finite.py
python3 tools/test_errata_regression.py
python3 tools/test_incidence_predictor_energy.py
python3 tools/test_deep_components.py
python3 tools/test_height_ratio.py
python3 tools/test_axiom_report_parser.py
python3 tools/test_new_finite_bridges.py
python3 tools/test_continuation_projection_prob.py
python3 tools/test_bridge_status.py
python3 tools/test_v3_quantitative_components.py
python3 tools/test_v4_blocks_and_pruning.py
python3 tools/test_v5_adaptive_noncommuting.py
python3 tools/test_v5_dyadic_prefix.py
python3 tools/test_v6_finite_bridges.py
python3 tools/test_v7_operator_product_expansion.py
python3 tools/test_v7_catalog_and_increments.py
python3 tools/test_v8_normed_row_bessel.py
python3 tools/test_v8_coarse_prefix_variation.py
if ! command -v lake >/dev/null 2>&1; then
  echo 'UNVERIFIED: lake not installed. Lean kernel build was not run.' >&2
  echo 'Install elan/Lean on Ubuntu or use the included GitHub Actions workflow.' >&2
  exit 2
fi
lake exe cache get
lake build OpenAI086Whole
lake env lean OpenAI086Whole.lean
echo 'KERNEL BUILD COMPLETE for authored independent components. Theorem 1.1 remains OPEN.'
