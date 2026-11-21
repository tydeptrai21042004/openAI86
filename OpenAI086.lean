import OpenAI086.SchwartzSizeBridge
import OpenAI086.GlobalLipschitzCancellation
import OpenAI086.PairedKernelBound
import OpenAI086.SymmetricLocalCancellation
import OpenAI086.SymmetricNumerator
import OpenAI086.FinitePVReflection
import OpenAI086.ColoredPathUniqueness
import OpenAI086.ComponentIntersections
import OpenAI086.SparsePairBudget
import OpenAI086.EntryRankConcrete
import OpenAI086.SparseBlockAccounting
import OpenAI086.ArbitraryDepthTelescoping
import OpenAI086.FiniteStoppingSets
import OpenAI086.FiniteMarginalCancellation
import OpenAI086.OrderedProductTelescoping
import OpenAI086.QuadraticChartsElementary
import OpenAI086.PathLabelEnergy
import OpenAI086.EntryRankSummation
import OpenAI086.LocalForms
import OpenAI086.PrincipalValueGoals
import OpenAI086.PrivateEnergyExact
import OpenAI086.FiniteCompression
import OpenAI086.DyadicTails
import OpenAI086.OuterStopping
import OpenAI086.Resonance
import OpenAI086.ProgressionGeometry
import OpenAI086.PrivateCoordinates
import OpenAI086.QuadraticPhase
import OpenAI086.SignConvention
import OpenAI086.FiniteReductions
import OpenAI086.Packing
import OpenAI086.ErrataChecks
import OpenAI086.PredictorMoments
import OpenAI086.BadDensityChain
import OpenAI086.FirstFailure
import OpenAI086.FirstFailureFour
import OpenAI086.InterleavedGapBudget
import OpenAI086.BadDensityIncidence
import OpenAI086.PredictorEnergy
import OpenAI086.BadDensityBudgetAssembly
import OpenAI086.NestedCoordinateProducts
import OpenAI086.CommonGoodHeight
import OpenAI086.SparsePairObstruction
import OpenAI086.HeightBinsOneDim
import OpenAI086.PaperStatement
import OpenAI086.ConditionalMainTransfer
import OpenAI086.CoordinateProjections
import OpenAI086.SymmetricKernel
import OpenAI086.UniformBootstrap

import OpenAI086.NoncommutingProducts
import OpenAI086.NoncommutingProjectionExample
import OpenAI086.PrefixCombinatorics

/-!
Independent OpenAI #086 audit and partial formalization.

Every `theorem` above contains a proof term to be checked by Lean.
`Theorem1_1_Goal` is a DEFINITION of an unproved proposition.
-/

#check OpenAI086.quadratic_resonance
#check OpenAI086.matched_quadratic_phase
#check OpenAI086.kernel_reversal
#check OpenAI086.two_coordinates_injective
#check OpenAI086.private_energy_lower_bound
#check OpenAI086.packing_of_contracted_generations
#check OpenAI086.predictor_identity_general
#check OpenAI086.corrected_chain_is_nested
#check OpenAI086.first_failure_two_iff
#check OpenAI086.Theorem1_1_Goal
#check OpenAI086.bad_density_incidence_chain_bound
#check OpenAI086.predictor_increment_finite_energy

#print axioms OpenAI086.quadratic_resonance
#print axioms OpenAI086.packing_of_contracted_generations
#print axioms OpenAI086.private_energy_lower_bound

#check OpenAI086.coordMask_chain_energy
#check OpenAI086.symmetric_kernel_pair
#check OpenAI086.uniform_absorption

#check OpenAI086.ordered_difference_correct
#check OpenAI086.ordered_difference_norm_le
#check OpenAI086.orthogonal_projections_need_not_commute
#check OpenAI086.finite_prefix_dyadic_halves

#print axioms OpenAI086.ordered_difference_correct
#print axioms OpenAI086.orthogonal_projections_need_not_commute

-- New formalized intermediate consequences from §§2–3.
#check OpenAI086.four_stopping_families_bound
#check OpenAI086.good_root_retains_three_quarters
#check OpenAI086.dyadic_tail_multiple_bins
#check OpenAI086.fixed_anchor_row_contraction
#check OpenAI086.private_column_coercivity

#print axioms OpenAI086.four_stopping_families_bound
#print axioms OpenAI086.private_column_coercivity

#check OpenAI086.fourLinearLocalForm
#check OpenAI086.HasZeroProgressionMarginals
#check OpenAI086.TruncationSignBridge_Goal
#check OpenAI086.PlusShiftSchwartzBound_Goal

-- Independently authored additional proof components (NOT full paper proofs).
#check OpenAI086.four_finite_stop_union_bound
#check OpenAI086.discreteProgressionMarginal_zero
#check OpenAI086.ordered_telescoping_three
#check OpenAI086.ordered_telescoping_four
#check OpenAI086.ordinaryQuadratic_affine
#check OpenAI086.ordinaryQuadratic_exp_mul
#check OpenAI086.finite_path_label_energy
#check OpenAI086.entry_rank_double_count

#print axioms OpenAI086.ordered_telescoping_four
#print axioms OpenAI086.finite_path_label_energy
#print axioms OpenAI086.entry_rank_double_count

#check OpenAI086.arbitrary_depth_ordered_telescoping
#print axioms OpenAI086.arbitrary_depth_ordered_telescoping

-- Deeper partial formalization, not a kernel certificate without Lake.
#check OpenAI086.bad_density_two_way_budget
#check OpenAI086.bad_density_chain_from_two_budgets
#check OpenAI086.applyCoordLayers_eq_common
#check OpenAI086.coordMultiProduct_depth_uniform_energy
#check OpenAI086.four_roles_common_good_at_least_half
#check OpenAI086.four_roles_have_common_good_height

#print axioms OpenAI086.bad_density_chain_from_two_budgets
#print axioms OpenAI086.coordMultiProduct_depth_uniform_energy
#print axioms OpenAI086.four_roles_common_good_at_least_half

#check OpenAI086.singleton_pair_one_occurrence
#check OpenAI086.singleton_pair_total_mass
#print axioms OpenAI086.singleton_pair_total_mass

#check OpenAI086.one_dim_height_ratio
#check OpenAI086.one_dim_height_ratio_symmetric
#print axioms OpenAI086.one_dim_height_ratio_symmetric

-- Exact logical reduction: analytical premises are explicit and UNPROVED.
#check OpenAI086.PlusShiftPointwiseBound
#check OpenAI086.Theorem1_1_from_plus_shift
#print axioms OpenAI086.Theorem1_1_from_plus_shift

-- Independent symmetric singular-integral building blocks (not Theorem 1.1).
#check OpenAI086.triple_difference_identity
#check OpenAI086.triple_difference_norm_bound
#check OpenAI086.symmetricTripleNumerator_at_zero
#check OpenAI086.symmetricTripleNumerator_telescope
#check OpenAI086.symmetricTripleNumerator_bound
#check OpenAI086.kernel_pair_reflection
#check OpenAI086.finite_paired_reflection
#print axioms OpenAI086.triple_difference_norm_bound
#print axioms OpenAI086.finite_paired_reflection

#check OpenAI086.triple_difference_common_majorant
#check OpenAI086.symmetric_numerator_linear_bound
#print axioms OpenAI086.symmetric_numerator_linear_bound

-- Independent bridge: the paired quotient is uniformly bounded under
-- bounded Lipschitz inputs.  Not a theorem about global integrability.
#check OpenAI086.quotient_bounded_of_linear_vanishing
#check OpenAI086.pairedHilbertKernel_zero
#check OpenAI086.pairedHilbertKernel_bound
#check OpenAI086.paired_kernel_bound_of_global_lipschitz
#print axioms OpenAI086.paired_kernel_bound_of_global_lipschitz

-- Direct Mathlib Schwartz-to-uniform-bound bridge.
#check OpenAI086.schwartz_value_bounded_by_seminorm
#check OpenAI086.tripleSchwartzSize_bound
#check OpenAI086.schwartz_first_iterated_derivative_bound
#print axioms OpenAI086.tripleSchwartzSize_bound
#check OpenAI086.paired_kernel_bound_for_schwartz_of_lipschitz
#print axioms OpenAI086.paired_kernel_bound_for_schwartz_of_lipschitz
