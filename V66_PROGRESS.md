# V66 — Predictor and localization integration (source candidates)

No Lean compilation or numerical testing was performed, per user request.

- Corollary 5.2: `predictors_all_dimensions` supplies the actual PredictorPackage on padded charts, with equalities of their atoms to the original low pair. It retains the reference admissible-opponent and depth-energy conditions.
- Lemma 5.7 / Proposition 5.8: `base_reduction_joint` combines the reference active count and inactive tail / base form reduction on a single ActiveSetup. `active_subset_length` proves length packing for any subset of active cells.
- Proposition 6.8: `localization_error_budget` supplies the weighted numerical-error bound from packing and the search-leaf count. `attempt_localization_budgeted` applies the actual catalog construction and localization theorem and obtains a root-length error bound under the explicitly stated numerical reserve. This does not establish the choice of all original parameters, or identify every original graph and mask with the reference objects.

Remaining: exact LSS Theorem 4.7, original chart pooled tails, delayed predictor and adaptive schedule correspondence, graph and mask correspondence, side-energy and core parameter choices, original outer reduction / absorption. The independent proof remains incomplete. Printed Lemma 3.5(2) still requires the documented correction. The new proof terms are uncompiled; no certification or promotion in the independent result registry is claimed.
