import OpenAI086.PaperV44PrivateRefit
import OpenAI086.PaperV42PrivateColumns

/-! V48: convert the coefficient-motion stopping criterion on p.11 of the
paper into the pointwise lower bound for the actual augmented columns.
This is the missing algebraic bridge between the anchor rule and the
restart-integral estimate. The finite-column synthesis is the exact
physical-plus-private vector used by Lemma 3.2. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

/-- Finite private-coordinate synthesis is linear in its coefficient vector. -/
theorem v48_synthesis_sub {n : ℕ} (φ : Fin n → ℂ) (a : Fin n → ℝ)
    (c d : Fin n → ℂ) :
    v42Synthesis φ a c - v42Synthesis φ a d =
      v42Synthesis φ a (c - d) := by
  funext j
  induction j using Fin.cases with
  | zero =>
      simp [v42Synthesis, Finset.sum_sub_distrib, sub_mul]
  | succ i =>
      simp [v42Synthesis, sub_mul]

/-- The private-coordinate lower bound turns an ℓ² coefficient
movement into a lower bound on the full augmented synthesis movement. -/
theorem v48_private_transition_lower {n : ℕ}
    (φ : Fin n → ℂ) (a : Fin n → ℝ) (c d : Fin n → ℂ)
    (D τ α : ℝ) (hD : 0 < D) (hn : (n : ℝ) ≤ D)
    (ha : ∀ i, 1 / D ≤ a i)
    (hcol : ∀ i, ‖φ i‖^2 + (a i)^2 ≤ D^2)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α)
    (hmove : τ * α ≤ v42L2Norm (c - d)) :
    D⁻¹ * τ * α ≤
      v42L2Norm (v42Synthesis φ a c - v42Synthesis φ a d) := by
  have hlow := (v42_complex_column_bounds φ a (c-d) D hD hn ha hcol).1
  have hq0 : 0 ≤ v42L2Norm (c-d) / D :=
    div_nonneg (v42_l2_nonneg _) hD.le
  have hs0 : 0 ≤ v42L2Norm (v42Synthesis φ a (c-d)) := v42_l2_nonneg _
  have hsq : (v42L2Norm (c-d) / D)^2 ≤
      (v42L2Norm (v42Synthesis φ a (c-d)))^2 := by
    simpa only [div_pow] using hlow
  have hnorm : v42L2Norm (c-d) / D ≤
      v42L2Norm (v42Synthesis φ a (c-d)) :=
    (sq_le_sq₀ hq0 hs0).mp hsq
  have hmove' : τ*α/D ≤ v42L2Norm (c-d)/D :=
    div_le_div_of_nonneg_right hmove hD.le
  calc
    D⁻¹ * τ * α = τ*α/D := by ring
    _ ≤ v42L2Norm (c-d)/D := hmove'
    _ ≤ v42L2Norm (v42Synthesis φ a (c-d)) := hnorm
    _ = v42L2Norm (v42Synthesis φ a c - v42Synthesis φ a d) := by
      rw [← v48_synthesis_sub]

/-- Same transition estimate for the actual Euclidean-space columns used
by the continuous L² projection construction. -/
theorem v48_private_column_transition_lower {Ω : Type*} {n : ℕ}
    (φ : Ω → Fin n → ℂ) (a : Fin n → ℝ)
    (c d : Fin n → ℂ) (D τ α : ℝ)
    (hD : 0 < D) (hn : (n : ℝ) ≤ D)
    (ha : ∀ i, 1/D ≤ a i)
    (hcol : ∀ x i, ‖φ x i‖^2 + (a i)^2 ≤ D^2)
    (hτ : 0 ≤ τ) (hα : 0 ≤ α)
    (hmove : τ*α ≤ v42L2Norm (c-d)) (x : Ω) :
    D⁻¹*τ*α ≤
      ‖(∑ i, c i • v44PrivateColumn φ a i x) -
        (∑ i, d i • v44PrivateColumn φ a i x)‖ := by
  have hl := v48_private_transition_lower (φ x) a c d D τ α hD hn ha (hcol x)
    hτ hα hmove
  have hsum :
      (∑ i, c i • v44PrivateColumn φ a i x) -
        (∑ i, d i • v44PrivateColumn φ a i x) =
      ∑ i, (c i-d i) • v44PrivateColumn φ a i x := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [sub_smul]
  have hnorm :
      ‖∑ i, (c i-d i) • v44PrivateColumn φ a i x‖ =
        v42L2Norm (v42Synthesis (φ x) a (c-d)) := by
    rw [← EuclideanSpace.norm_eq]
    rw [v44_private_synthesis_coords]
    simp [v42L2Norm]
  rw [hsum, hnorm]
  exact hl

end OpenAI086
