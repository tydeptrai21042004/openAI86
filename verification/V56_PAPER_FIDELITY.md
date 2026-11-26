# V56 manuscript-to-reference crosswalk

All 59 numbered entries, including Definition 4.1. A source anchor indicates where to investigate, not a proof of the original proposition. The 58 mathematical result certificates remain open.

| Paper | Page | Reference source | Remaining fidelity obligation |
|---|---:|---|---|
| Theorem 1.1 | 2 | Sec16_3SummingUpdateLevels.lean — tht_main | V55 sign/PV bridge to the locked theorem; kernel not replayed. |
| Lemma 2.1 | 4 | Sec03LocalFormsFiniteConstants.lean — localProgression_absoluteNormBound | Check exponent polytope, normalized norms, and vector-valued version. |
| Theorem 2.2 | 4 | Sec16_3SummingUpdateLevels.lean — uniform_of_activeFinal | Reference uniform bound uses its local kernel class; equivalence of C_N not proved. |
| Proposition 2.3 | 4 | Sec16_3SummingUpdateLevels.lean — normalizedAbsorption_of_activeFinal | Match normalization, quantifiers in q,c,N and restart decomposition. |
| Lemma 2.4 | 5 | Sec16_3SummingUpdateLevels.lean — uniform_of_normalized, tht_main_of_uniform | Match lattice, Gevrey kernel construction and limiting argument. |
| Lemma 3.1 | 7 | DyadicStopping.lean  | Local v43_lemma31 is a direct finite packing candidate; kernel check required. |
| Lemma 3.2 | 8 | Sec04ColumnProjections.lean — columnCombination_bounds, cellColumnProjection_ae_bound, cellColumnProjection_predictor_moment | V56 joint normalized-cell candidate; audit reindexing selected labels and actual normalized interval. |
| Lemma 3.3 | 8 | RademacherMenshov.lean — nestedProjectionProduct_prefix_rows, nestedProjectionProduct_successive_jumps | Local v43_lemma33 candidate includes heterogeneous row codomains; reference uses common codomain for prefix theorem. |
| Lemma 3.4 | 9 | Sec04ColumnProjections.lean — columnSpatialCompression, columnSpatialCompression_complements | Reference explicit bound has larger dependence on m, uses pointwise path-count and common codomain; do not assert exact printed bound or integral variant. |
| Lemma 3.5 | 13 | RationalLinearAlgebra.lean — rational_logarithmic_cover, rational_dyadic_scale_count, rational_frequency_tiny_sum | Printed part (2) refuted. Corrected scalar/Euclidean/supremum candidates; V56 covers packet application to Lemma 8.2. |
| Definition 4.1 | 15 | Sec05QuadraticCharts.lean  | Definition: chart representation agrees in outline; derivative and bounded-atom conventions need comparison. |
| Lemma 4.2 | 15 | Sec05QuadraticCharts.lean — productQuadraticChart_bounded, translateQuadraticChart_bounded | Match arbitrary affine rescaling and quantitative derivative budgets. |
| Lemma 4.3 | 16 | Sec09_1ReturnWeylSplitting.lean — weylSplitting | Lattice transference and error treatment adapted; exact constants/complexity need translation. |
| Lemma 4.4 | 18 | Sec09_2ChartFourierSeparation.lean — chart_split_fourier_explicit, chart_split_fourier_dim_zero | Match exact expansion, dimension zero and uniform tails. |
| Lemma 4.5 | 20 | Sec09_2ChartFourierSeparation.lean — progressionSeparation | Match coefficient sums, tail bounds, and chart complexities. |
| Lemma 4.6 | 21 | Sec09_2ChartFourierSeparation.lean — sep_one_atom_expansion | Compare conditional one-scale separation statements and smooth bump costs. |
| Theorem 4.7 | 22 | Sec07FiniteInverse.lean — finite_inverse | ALTERNATIVE ONLY: finite cyclic chart theorem does not prove the general LSS nilmanifold theorem. |
| Lemma 4.8 | 22 | GowersCauchySchwarz.lean  | Check circle normalization, mixed cubes and seminorm. |
| Lemma 4.9 | 23 | Sec08ContinuousDecomposition.lean — continuous_inverse | Alternative finite inverse input; check exact continuous normalization and bounds. |
| Lemma 4.10 | 26 | Sec08ContinuousDecomposition.lean — continuous_decomposition_interval, continuous_decomposition | Match three-way decomposition, uniform and L1 norms and complexity. |
| Lemma 4.11 | 27 | Sec10Detection.lean — vonNeumann_local_bounded | Match one L2 input and constants for arbitrary slot. |
| Lemma 4.12 | 27 | Sec10Detection.lean — detection_atom_pair | Match q, residual size, correlation, and quantitative witness. |
| Lemma 5.1 | 30 | Sec11_1aPredictors.lean  | Check separated-term scale sum and admissible sequences. |
| Corollary 5.2 | 31 | Sec11_1aPredictors.lean — finitePredictorList | Check absolute scale errors and predictor labels. |
| Lemma 5.3 | 32 | Sec11_1bDelayedMoments.lean — delayedPredictorReplacement | Audit private-coordinate predictor term and delayed-depth loss. |
| Lemma 5.4 | 33 | Sec11_2aAdaptiveFitsStagger.lean  | Match normalized subtree, energy fit and restart budgets. |
| Lemma 5.5 | 34 | Sec11_2aAdaptiveFitsStagger.lean  | Verify exact two-earliest-increments expansion and all positions. |
| Proposition 5.6 | 35 | Sec11_2bFiniteBaseDataPairs.lean, Sec11_2cFiniteBaseDataAssembly.lean  | Match high truncation, delayed fits and stopping partitions. |
| Lemma 5.7 | 37 | Sec11_2bFiniteBaseDataPairs.lean — tripleNorm_count | Check fixed triple scale range and exception threshold. |
| Proposition 5.8 | 38 | Sec11_2cFiniteBaseDataAssembly.lean — activeCellReduction | Match minimum before powered estimates and base errors. |
| Lemma 6.1 | 40 | Sec12_1TagsAmbientGraph.lean  | Match tag separation and chosen parameters. |
| Lemma 6.2 | 41 | Sec12_1TagsAmbientGraph.lean  | Match endpoint coordinates and short paths. |
| Lemma 6.3 | 42 | Sec12_2DecreasingColorsHistoricalMasks.lean  | Check decreasing colors and exceptional-root bound. |
| Lemma 6.4 | 43 | Sec12_2DecreasingColorsHistoricalMasks.lean — historicalMaskSeparation | Match every pad and historical inclusion condition. |
| Lemma 6.5 | 45 | Sec12_2DecreasingColorsHistoricalMasks.lean, Sec12_3FiniteSameTagCatalogs.lean  | Check Bessel separation of actual endpoint spaces. |
| Lemma 6.6 | 46 | Sec12_3FiniteSameTagCatalogs.lean  | Compare same-tag tests and finite template complexity. |
| Lemma 6.7 | 48 | Sec12_3FiniteSameTagCatalogs.lean, Sec12_3bCatalogsMainColumns.lean  | Match catalog closure and path label budget. |
| Proposition 6.8 | 49 | Sec12_4BinaryLocalizationVariation.lean — attempt_localization | Match binary search leaves and absolute error. |
| Lemma 6.9 | 50 | Sec14_1TransferPairedDefects.lean, Sec12_4BinaryLocalizationVariation.lean  | Check coupled filters, independent side choices and near bands. |
| Lemma 7.1 | 52 | FeffermanStein.lean  | Mixed-norm maximal argument changed; exact A_r statement still required. |
| Lemma 7.2 | 53 | Sec14_2aShortBlockSampling.lean, Sec14_2bShortBlockSummation.lean — short_block_comparison | Compare randomized torus estimate, clipping and exponent tending to zero. |
| Lemma 7.3 | 58 | Sec12_4BinaryLocalizationVariation.lean, Sec14_3PowerCostsFrozenComplements.lean — basic_variation_G0 | Match certified endpoints, overlap and variations. |
| Lemma 7.4 | 60 | Sec14_4FixedStacksTwoVaryingSides.lean  | Match fixed side stacks and time-dependent states. |
| Proposition 7.5 | 62 | Sec14_5bExportedSideEstimate.lean — side_estimate | Match conditional square-energy assumptions, q,p and hull minima. |
| Lemma 8.1 | 65 | Sec13_1OneExpansionAtFirstMatch.lean  | Match single first-match expansion and bounded lift. |
| Lemma 8.2 | 67 | Sec13_2TwoGraphsHeightStabilization.lean — exceptional_blocks_count, rational_span_expand_bounded | V56 proves first assertion candidate (5d); tiny-span Cramer coefficient bound remains. |
| Lemma 8.3 | 68 | Sec13_2TwoGraphsHeightStabilization.lean — height_stabilization | Match stabilization budgets and nonexceptional modes. |
| Lemma 8.4 | 69 | Sec13_2TwoGraphsHeightStabilization.lean  | Check PRE/CURRENT good predicate coherence. |
| Lemma 8.5 | 69 | Sec13_3BesselRowsLinearSideEnergy.lean — sum_frac_le_harmonic, sum_frac_le_log | V56 attributed standalone proof candidate for H_M and log bound. |
| Lemma 8.6 | 70 | Sec13_3BesselRowsLinearSideEnergy.lean — chain_bad_count | Audit endpoint inclusions in bad-density chains. |
| Lemma 8.7 | 70 | Sec13_3BesselRowsLinearSideEnergy.lean — separated_projection_rows | Match actual mode families and cross terms. |
| Lemma 8.8 | 71 | Sec13_3BesselRowsLinearSideEnergy.lean — lift_composition_global | Match lift, histories and heterogeneous codomains. |
| Proposition 8.9 | 72 | Sec13_3BesselRowsLinearSideEnergy.lean — linear_energy | Match exact subtotals including private coordinates and leakage. |
| Lemma 8.10 | 74 | Sec13_5RepresentativesComponentSizesFirstTops.lean  | Check inheritance of representatives across blocks. |
| Lemma 8.11 | 75 | Sec13_5RepresentativesComponentSizesFirstTops.lean — size_comparison | Check component size, incidence and normalization. |
| Proposition 8.12 | 76 | Sec13_5RepresentativesComponentSizesFirstTops.lean — first_top_count | Match removal of first stops and uniform top count. |
| Lemma 9.1 | 81 | Sec15_3FiniteSparseCountLemma.lean — sparse_count_explicit | Match all hypotheses, pure shift gap, real-grid approximation, constants and exponent. |
| Proposition 9.2 | 87 | Sec15_4VerificationCountingHypotheses.lean, Sec15_5OneDistributionCalculationFinalSums.lean — four_core_sparse_explicit, three_core_sparse_explicit, powered_count | Match four- and three-core hypotheses and same amplitude grouping. |
| Proposition 9.3 | 89 | Sec15_5OneDistributionCalculationFinalSums.lean — core_final_patterns | Match original cell minimum, all errors and uniform epsilon independent of q. |

## Unnumbered completion sections
- §10.1: Actual attempt partition, exceptions and packing.
- §10.2–10.3: Derive retainedMin_holds using original parameter order and complexity budgets.
- §10.4: Full base expansion and activeFinal_holds, then exact original Proposition 2.3.
