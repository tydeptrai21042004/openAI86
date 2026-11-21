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
