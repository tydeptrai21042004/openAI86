import Mathlib
import OpenAI086.FiniteRowCauchySchwarz
import OpenAI086.PathLabelEnergy
import OpenAI086.Packing

/-! Lemma 3.4, pp.12–13: vector-valued coefficient-error estimate and
summation of the two independently packed budgets. The actual stopping
construction and projection representatives must still be supplied. -/
namespace OpenAI086
open MeasureTheory

/-- Finite Cauchy–Schwarz for a sum of complex multiples of vectors. -/
theorem v37_complex_vector_cs {V Y : Type*} [Fintype V]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] (c : V → ℂ) (v : V → Y) :
    ‖∑ i, c i • v i‖^2 ≤ (∑ i, ‖c i‖^2)*(∑ i, ‖v i‖^2) := by
  classical
  have h : ‖∑ i, c i • v i‖ ≤ ∑ i, ‖c i‖*‖v i‖ := by
    simpa only [norm_smul] using (norm_sum_le (Finset.univ : Finset V) (fun i => c i • v i))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (finite_row_cauchy_schwarz (fun i => ‖c i‖) (fun i => ‖v i‖))

/-- The paper's error rows have heterogeneous Hilbert (or normed) codomains.
Linearity identifies the error with the sum of the individually tested
columns. The global Bessel bound is used once per label, not once per row. -/
theorem v37_complex_row_error {R V X : Type*} [Fintype R] [Fintype V]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    {Y : R → Type*} [∀ r, NormedAddCommGroup (Y r)] [∀ r, NormedSpace ℂ (Y r)]
    (B : (r : R) → X →L[ℂ] Y r) (φ : V → X) (e : R → V → ℂ)
    (τ : ℝ) (hsmall : ∀ r, (∑ v, ‖e r v‖^2) ≤ τ^2)
    (hB : ∀ z, (∑ r, ‖B r z‖^2) ≤ ‖z‖^2) :
    (∑ r, ‖B r (∑ v, e r v • φ v)‖^2) ≤ τ^2*(∑ v, ‖φ v‖^2) := by
  classical
  calc
    _ ≤ ∑ r, τ^2*(∑ v, ‖B r (φ v)‖^2) := by
      apply Finset.sum_le_sum
      intro r _
      simp only [map_sum, map_smul]
      exact (v37_complex_vector_cs (e r) (fun v => B r (φ v))).trans
        (mul_le_mul_of_nonneg_right (hsmall r) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    _ = τ^2*(∑ r, ∑ v, ‖B r (φ v)‖^2) := by rw [Finset.mul_sum]
    _ = τ^2*(∑ v, ∑ r, ‖B r (φ v)‖^2) := by rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun v _ => hB (φ v))) (sq_nonneg τ)

/-- Apply the two separately contracted attempt budgets of the paper.
This is the final squared-norm estimate for a single size segment once
anchor and error bounds on its attempt generations have been obtained. -/
theorem v37_attempt_compression (mass energy anchor err : ℕ → ℝ)
    (ρ A B : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hm0 : 0 ≤ mass 0) (he0 : 0 ≤ energy 0)
    (hm : ∀ n, mass (n+1) ≤ ρ*mass n)
    (he : ∀ n, energy (n+1) ≤ ρ*energy n)
    (ha : ∀ n, anchor n ≤ A*energy n)
    (hb : ∀ n, err n ≤ B*mass n) (N : ℕ) :
    (∑ n ∈ Finset.range N, anchor n) ≤ A*energy 0/(1-ρ) ∧
    (∑ n ∈ Finset.range N, err n) ≤ B*mass 0/(1-ρ) := by
  exact ⟨cost_of_packed_generations energy anchor A ρ hA hρ0 hρ1 he0 he ha N,
    cost_of_packed_generations mass err B ρ hB hρ0 hρ1 hm0 hm hb N⟩

/-- Integrate the pointwise path budget on a genuine measure space.
The functions are already extended by zero outside the attempt root.
Integrability of their squared norms is explicit. -/
theorem v37_integrated_column_budget {Ω V H : Type*} [MeasurableSpace Ω]
    [Fintype V] [DecidableEq V] [NormedAddCommGroup H]
    (μ : MeasureTheory.Measure Ω) (R : Set Ω) (φ : V → Ω → H)
    (active : Ω → Finset V) (D : ℝ) (hD : 0 ≤ D)
    (hcard : ∀ x, ((active x).card : ℝ) ≤ D)
    (hbound : ∀ x v, v ∈ active x → ‖φ v x‖ ≤ D)
    (hzero : ∀ x v, v ∉ active x → φ v x = 0)
    (hout : ∀ x v, x ∉ R → φ v x = 0)
    (hR : MeasurableSet R)
    (hi : ∀ v, MeasureTheory.Integrable (fun x => ‖φ v x‖^2) μ)
    (hc : MeasureTheory.Integrable (R.indicator (fun _ : Ω => D^3)) μ) :
    (∑ v, ∫ x, ‖φ v x‖^2 ∂μ) ≤ (μ R).toReal*D^3 := by
  classical
  have hp (x : Ω) : (∑ v, ‖φ v x‖^2) ≤ R.indicator (fun _ : Ω => D^3) x := by
    by_cases hx : x ∈ R
    · rw [Set.indicator_of_mem hx]
      have he : (∑ v ∈ active x, ‖φ v x‖^2) = ∑ v, ‖φ v x‖^2 := by
        apply Finset.sum_subset (Finset.subset_univ (active x))
        intro v _ hv
        simp [hzero x v hv]
      rw [← he]
      exact finite_path_label_energy (active x) (fun v => φ v x) D hD (hcard x) (hbound x)
    · rw [Set.indicator_of_notMem hx]
      have hz : ∀ v, φ v x = 0 := fun v => hout x v hx
      simp [hz]
  have hs : MeasureTheory.Integrable (fun x => ∑ v, ‖φ v x‖^2) μ :=
    MeasureTheory.integrable_finset_sum _ (fun v _ => hi v)
  have h := MeasureTheory.integral_mono hs hc hp
  rw [MeasureTheory.integral_finset_sum _ (fun v _ => hi v), MeasureTheory.integral_indicator hR] at h
  simpa [MeasureTheory.integral_const, MeasureTheory.Measure.real, smul_eq_mul, mul_comm] using h

end OpenAI086
