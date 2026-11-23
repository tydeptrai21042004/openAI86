import Mathlib
import OpenAI086.HeightPositionChainBridge
import OpenAI086.EntryRankConcrete

/-!
# Lemma 8.6: rank-controlled exceptional incidences in both directions

This combines the two scalar interleaved/lagged budgets with the concrete
entry-rank Bessel-style density argument. Unlike the previous bridge,
NO global budget is simply postulated for either exception family: both
are deduced from per-label occurrence counts and the first-entry rank
lower bound on the corresponding containing-set size.

The one remaining interface is a POINTWISE inequality expressing the
paper's actual bad-height predicate by lag jumps, interleaved gaps,
and exceptional-label fractions. Deriving that predicate directly from
nested sets and the floor-log test is still open. This module does not
claim the entire manuscript Lemma 8.6.
-/

namespace OpenAI086

/-- The rank-harmonic cost of at most `M` primary labels. -/
def finiteRankHarmonic (M : ℕ) : ℝ :=
  ∑ r : Fin M, (1 : ℝ) / ((r.val + 1 : ℕ) : ℝ)

/-- Both exception budgets are now derived from per-label multiplicity
and rank data, rather than assumed as height or position incidence sums.
The resulting constant is `(L + B*H_M)/δ`, with the exact geometric
absorption factor 2 inherited from the manuscript's count. -/
theorem bad_density_chain_from_ranked_exceptions
    (N H lag M : ℕ) (δ L A B : ℝ)
    (p c : ℕ → ℕ → ℝ)
    (heightActive : Fin (N + 1) → Fin H → Fin M → Prop)
    (positionActive : Fin H → Fin (N + 1) → Fin M → Prop)
    (heightSize : Fin (N + 1) → Fin H → ℕ)
    (positionSize : Fin H → Fin (N + 1) → ℕ)
    (bad : Fin (N + 1) → Fin H → ℝ)
    (hδ : 0 < δ) (hH : 0 < H)
    (hpc : ∀ i ≤ N, ∀ h, p i h ≤ c i h)
    (hcp : ∀ i < N, ∀ h, c i h ≤ p (i + 1) h)
    (hfirstHeight : ∀ i ≤ N, ∀ r < lag, 0 ≤ p i r)
    (hlastHeight : ∀ i ≤ N, ∀ r < lag, p i (H + r) ≤ L)
    (hfirstPosition : ∀ h < H, 0 ≤ p 0 (h + lag))
    (hlastPosition : ∀ h < H, c N (h + lag) ≤ L)
    (hheightRank : ∀ i h r, heightActive i h r →
      r.val + 1 ≤ heightSize i h)
    (hpositionRank : ∀ h i r, positionActive h i r →
      r.val + 1 ≤ positionSize h i)
    (hheightMultiplicity : ∀ i r,
      (∑ h : Fin H, if heightActive i h r then (1 : ℝ) else 0) ≤ A)
    (hpositionMultiplicity : ∀ h r,
      (∑ i : Fin (N + 1), if positionActive h i r then (1 : ℝ) else 0) ≤ B)
    (hpoint : ∀ i : Fin (N + 1), ∀ h : Fin H,
      bad i h ≤
        ((p i.val (h.val + lag) - p i.val h.val) +
          (∑ r : Fin M, if heightActive i h r then
            (1 : ℝ) / (heightSize i h : ℝ) else 0)) +
        ((c i.val (h.val + lag) - p i.val (h.val + lag)) +
          (∑ r : Fin M, if positionActive h i r then
            (1 : ℝ) / (positionSize h i : ℝ) else 0)))
    (hlower : ∀ i : Fin (N + 1),
      δ * (H : ℝ) ≤ ∑ h : Fin H, bad i h)
    (hbudget : 2 * ((lag : ℝ) * L + A * finiteRankHarmonic M) ≤
      δ * (H : ℝ)) :
    ((N + 1 : ℕ) : ℝ) ≤
      2 * (L + B * finiteRankHarmonic M) / δ := by
  classical
  let heightNoise : Fin (N + 1) → Fin H → ℝ := fun i h =>
    ∑ r : Fin M, if heightActive i h r then
      (1 : ℝ) / (heightSize i h : ℝ) else 0
  let positionNoise : Fin (N + 1) → Fin H → ℝ := fun i h =>
    ∑ r : Fin M, if positionActive h i r then
      (1 : ℝ) / (positionSize h i : ℝ) else 0
  have hv : ∀ i : Fin (N + 1),
      (∑ h : Fin H, heightNoise i h) ≤ A * finiteRankHarmonic M := by
    intro i
    simpa only [heightNoise, finiteRankHarmonic] using
      (ranked_exceptional_density_le H M A
        (fun h r => heightActive i h r) (heightSize i)
        (fun h r hr => hheightRank i h r hr)
        (fun r => hheightMultiplicity i r))
  have hh : ∀ h : Fin H,
      (∑ i : Fin (N + 1), positionNoise i h) ≤
        B * finiteRankHarmonic M := by
    intro h
    simpa only [positionNoise, finiteRankHarmonic] using
      (ranked_exceptional_density_le (N + 1) M B
        (fun i r => positionActive h i r) (positionSize h)
        (fun i r hr => hpositionRank h i r hr)
        (fun r => hpositionMultiplicity h r))
  exact bad_density_chain_with_both_telescopes
    N H lag δ L (A * finiteRankHarmonic M) (B * finiteRankHarmonic M)
    p c heightNoise positionNoise bad hδ hH hpc hcp
    hfirstHeight hlastHeight hfirstPosition hlastPosition
    hv hh (by intro i h; exact hpoint i h) hlower hbudget

end OpenAI086
