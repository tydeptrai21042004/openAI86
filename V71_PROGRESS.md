# V71 — Exact paper-side density and common-height masks

Source-only continuation of V70. Two new Lean modules contain seven theorem candidates and two definitions. No Lean compilation or numerical regression suite has been run. Prior Lean files, the manuscript and the pinned reference are unchanged.

## Section 8 — density chains (Lemma 8.6)

`PaperDensity.lean` constructs finite exceptional sets X_i from the final CURRENT component and finite height-bad sets Y_{i,h} from the current component. Monotonicity supplies coverage at earlier heights. The exact `PaperGood` failure implies `v57Bad` with beta=1/10; the strict bad-height count follows from failure of `PaperCore`. This removes the manually assumed floor-log bad-density condition of V62 on the reference component model.

`paperSideModes` and `paperSideEvents` are defined with the stronger paper predicate, not the old ratio-based core predicate. `paper_chain_events_bound` uses actual linked geometric events, path-local label counts and the transport lemma to derive the chronological inclusions. `paper_chain_length_schedule` supplies the actual exceptional and bad-height multiplicity bounds (4*dmax and 3*dmax*Rht) from the pinned reference schedule. The printed manuscript allows a larger exceptional count; the stronger reference estimate is used on the reference data only.

`rank_le_eleven_log` bounds the floor-log rank by 11 log M. `paper_height_reserve` supplies the numerical reserve in the exact floor-log density theorem from the valid schedule and Cj >= 340. `paper_chain_length_valid` combines both, without a separate assumed height reserve. All claims are uncompiled candidates. The geometric hypotheses on the selected event class and path labels remain explicit; the downstream separation/coloring and global square-energy proof still use the old side/core split and have not been silently relabeled.

## Section 9 — common-height role masks

`PaperMasks.lean` uses the paper-core bad-height estimate and the common-height probability bound from V70 to derive nonempty joint successful heights for every tuple of core modes. It then applies the attributed reference `first_success_masked` theorem with the exact `PaperGood` predicate. The result is a convergent HasSum over all failed trial lengths, assignments of first failing roles, failed heights and the final successful height; the normalized weight is |H|^(-(n+1)). This is an identity on finite tuples of paper-core modes, not the full analytic expansion of the original local four-linear form with side/offset roles.

## Remaining source work

- Sections 2–3: exact local-kernel correspondence, outer reduction, compression and corrected-height integration.
- Section 4: exact Leng–Sah–Sawhney theorem, pooled Fourier tails and chart correspondence.
- Sections 5–6: delayed fits, adaptive schedules, graph/mask/helper-filter correspondence.
- Section 7: weighted mixed-norm maximal theorem and actual stack energy.
- Section 8: actual event partition/coloring, global side energy using paperSideEvents, first-top energy on exact type classes, use-cell correspondence.
- Section 9: incorporate masks into the actual core/side/offset local forms; progression normalization and numerical errors.
- Section 10: remaining analytic overhead bounds and whole-proof parameter integration.

The whole-paper source is incomplete. The false printed Lemma 3.5(2) retains its correction. No claim is made that these new Lean proofs elaborate or pass the kernel; user will check later.
