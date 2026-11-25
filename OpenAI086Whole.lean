import OpenAI086

/-!
# OpenAI086Whole: independent proof-development entrypoint

Everything reachable from this file uses Mathlib and the independently
authored OpenAI086 source modules only.  No copied Lean proofs from
`TrilinearHT` or other external formalizations are imported.

This entrypoint checks a number of actual proved intermediate declarations.
It explicitly does NOT assert that Theorem 1.1 is proved.
-/

#check OpenAI086.Theorem1_1_Goal
#check OpenAI086.quadratic_resonance
#check OpenAI086.ordered_telescoping_three
#check OpenAI086.arbitrary_depth_ordered_telescoping
#check OpenAI086.four_finite_stop_union_bound
#check OpenAI086.finite_path_label_energy
#check OpenAI086.entry_rank_double_count
#check OpenAI086.discreteProgressionMarginal_zero
#check OpenAI086.ordinaryQuadratic_affine

#print axioms OpenAI086.quadratic_resonance
#print axioms OpenAI086.arbitrary_depth_ordered_telescoping
#print axioms OpenAI086.finite_path_label_energy
#print axioms OpenAI086.entry_rank_double_count

-- Continued independent finite mathematical steps in Sections 8 and 9.
#check OpenAI086.ambient_component_intersection_bound
#check OpenAI086.strict_majorities_intersect
#check OpenAI086.quantitative_predecessor_overlap
#check OpenAI086.ranked_exceptional_density_le
#check OpenAI086.finite_incidence_mass_bound
#check OpenAI086.ordered_pair_occurrences_le
#check OpenAI086.retained_pair_occurrences_le
#check OpenAI086.greedy_block_count_bound
#check OpenAI086.half_density_block_count

#print axioms OpenAI086.quantitative_predecessor_overlap
#print axioms OpenAI086.ranked_exceptional_density_le
#print axioms OpenAI086.ordered_pair_occurrences_le

#check OpenAI086.four_edge_colors_determine_path
#print axioms OpenAI086.four_edge_colors_determine_path

-- Additional finite corrections to the October 2026 manuscript.
#check OpenAI086.interleaved_gap_telescope
#check OpenAI086.interleaved_gap_nonnegative
#check OpenAI086.interleaved_gap_budget
#check OpenAI086.first_failure_four_three_iff
#check OpenAI086.first_failure_four_none_iff
#check OpenAI086.predictor_increment_exact
#print axioms OpenAI086.interleaved_gap_budget
#print axioms OpenAI086.first_failure_four_three_iff

#check OpenAI086.Theorem1_1_from_plus_shift

#check OpenAI086.finite_weighted_path_budget
#check OpenAI086.finite_multifamily_stopping_budget
#check OpenAI086.alternating_paths_determined_by_colors
#check OpenAI086.compression_coefficient_error_budget

#check OpenAI086.firstFailureIndex_true_prefix

#check OpenAI086.finite_first_success_weight_identity

-- Continuation v2 proof components.  The named paper results are still open.
#check OpenAI086.nested_projection_square_variation_bound
#check OpenAI086.ordered_contraction_perturbation
#check OpenAI086.compression_row_error_from_bessel
#check OpenAI086.variable_first_success_identity
#print axioms OpenAI086.nested_projection_square_variation_bound
#print axioms OpenAI086.compression_row_error_from_bessel

#check OpenAI086.varying_prefix_rows_need_more_than_constant_one

-- V9: height-lag budget and first-failure clarity.
#check OpenAI086.finite_height_lag_telescoping
#check OpenAI086.finite_height_lag_budget
#print axioms OpenAI086.finite_height_lag_budget

#check OpenAI086.bad_density_chain_with_proved_height_lag
#print axioms OpenAI086.bad_density_chain_with_proved_height_lag

#check OpenAI086.finite_predictor_weighted_orthogonality
#print axioms OpenAI086.finite_predictor_weighted_orthogonality

-- V10: two independent telescoping directions, actual rank incidence,
-- and row choices at sparse arbitrary noncommuting projection depths.
-- These are partial mathematical bridges, NOT completed paper results.
#check OpenAI086.integer_gap_or_density_bound
#check OpenAI086.finite_set_rank_monotone
#check OpenAI086.finite_bad_height_from_nested_sets
#check OpenAI086.real_interleaved_gap_telescope
#check OpenAI086.real_interleaved_gap_budget
#check OpenAI086.bad_density_chain_with_both_telescopes
#check OpenAI086.bad_density_chain_from_ranked_exceptions
#check OpenAI086.finite_sparse_choice_noncommuting_row_bound

#print axioms OpenAI086.integer_gap_or_density_bound
#print axioms OpenAI086.finite_bad_height_from_nested_sets
#print axioms OpenAI086.bad_density_chain_from_ranked_exceptions
#print axioms OpenAI086.finite_sparse_choice_noncommuting_row_bound

-- V14: source candidates only; these checks require a successful Lean build.
#check OpenAI086.bad_density_with_initial_heights
#check OpenAI086.bad_density_with_initial_heights_strict
#check OpenAI086.full_chronological_integer_log_bad_density
#check OpenAI086.full_chronological_integer_log_bad_density_strict
#check OpenAI086.full_bad_height_sum_split
#check OpenAI086.full_paper_bad_height_sum
#check OpenAI086.paper_full_chronological_integer_log_bad_density
#check OpenAI086.paper_full_chronological_integer_log_bad_density_strict
#check OpenAI086.finite_scalar_level_energy_assembly
#check OpenAI086.finite_linear_level_energy_assembly
#print axioms OpenAI086.full_paper_bad_height_sum
#print axioms OpenAI086.finite_scalar_level_energy_assembly
#check OpenAI086.finite_dyadic_width_le_length
#check OpenAI086.finite_dyadic_width_is_power_two
#check OpenAI086.finite_dyadic_prefix_widths_nodup
#print axioms OpenAI086.finite_dyadic_prefix_widths_nodup
#check OpenAI086.finite_dyadic_prefix_block_aligned
#check OpenAI086.aligned_equal_width_intervals_separated

-- V16 algebraic bridge (not a proof of the Hilbert-space estimate).
#check OpenAI086.finite_dyadic_width_mem_set
#check OpenAI086.finite_dyadic_width_set_card_le
#check OpenAI086.finite_linear_prefix_grouped_by_width
#check OpenAI086.finite_dyadic_linear_pairs_widths_nodup
#check OpenAI086.finite_linear_width_level_zero_or_aligned_block
#check OpenAI086.finite_ordered_actual_prefix_width_expansion
#check OpenAI086.finite_row_actual_prefix_width_expansion
#check OpenAI086.finite_linear_row_actual_prefix_width_expansion
#print axioms OpenAI086.finite_row_actual_prefix_width_expansion

-- V16: exact zero-mask closure of existing actual dyadic Bessel rows.
#check OpenAI086.masked_finite_row_contraction
#check OpenAI086.actual_dyadic_masked_tuple_bessel
#check OpenAI086.actual_dyadic_masked_multilevel_bessel
#print axioms OpenAI086.actual_dyadic_masked_multilevel_bessel

-- V16 actual mask/grid-index extraction; Nat-indexed choices.
#check OpenAI086.finite_dyadic_row_width_choices_exist
#check OpenAI086.finite_dyadic_row_paper_block_choices_exist
#check OpenAI086.finite_dyadic_multilayer_row_choices_exist
#print axioms OpenAI086.finite_dyadic_multilayer_row_choices_exist

-- V17: source proof candidates, only meaningful after a successful Lean build.
#check OpenAI086.finite_dyadic_prefix_block_inside
#check OpenAI086.finite_dyadic_zero_base_start_lt
#check OpenAI086.finite_dyadic_aligned_block_index_lt
#check OpenAI086.finite_dyadic_bounded_width_selection
#check OpenAI086.finite_dyadic_bounded_row_choices
#check OpenAI086.finite_dyadic_bounded_multilayer_choices
#check OpenAI086.actual_dyadic_selected_width_row_bessel
#check OpenAI086.actual_dyadic_one_layer_prefix_bessel
#check OpenAI086.finite_list_width_product_as_tuple_sum
#print axioms OpenAI086.actual_dyadic_one_layer_prefix_bessel
#check OpenAI086.actual_dyadic_width_card_le
#check OpenAI086.actual_dyadic_one_layer_explicit_log_bound
#print axioms OpenAI086.actual_dyadic_one_layer_explicit_log_bound
-- V48: coefficient-motion/private-coordinate bridge and restart cutoff.
#check OpenAI086.v48_private_transition_lower
#check OpenAI086.v48_private_column_transition_lower
#check OpenAI086.v48_restart_factor_lt_half
#check OpenAI086.v48_restart_factor_from_variation
#check OpenAI086.v48_anchor_state_constant_on_terminal_cell
#check OpenAI086.v48_anchor_label_fiber_measurable
#print axioms OpenAI086.v48_private_transition_lower
#print axioms OpenAI086.v48_restart_factor_lt_half


-- V48: private-coordinate increment and quantitative attempt contraction.
#check OpenAI086.v48_private_increment_large
#check OpenAI086.v48_restart_attempt_contract
#check OpenAI086.v48_private_restart_attempt_contract
#check OpenAI086.v48_stage_label_constant_on_terminal_cell
#check OpenAI086.v48_stage_label_fiber_measurable
#check OpenAI086.v48_stage_active_cell
#print axioms OpenAI086.v48_private_increment_large
#print axioms OpenAI086.v48_restart_attempt_contract
#check OpenAI086.v48_spatial_partition_range_finite
#print axioms OpenAI086.v48_spatial_partition_range_finite
