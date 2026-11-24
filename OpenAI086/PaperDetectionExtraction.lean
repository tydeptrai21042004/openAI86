import Mathlib

/-! Lemma 4.12 (pp.28–29): weighted extraction of a witnessing atom pair
and explicit clipping-tail integrability. Does not prove the inverse input
or the quantitative chart expansion. -/
namespace OpenAI086
open MeasureTheory

/-- A large weighted complex form forces a large individual term. -/
theorem v26_weighted_witness {I : Type*} (s : Finset I)
    (c z : I → ℂ) (A δ : ℝ) (hδ : 0 ≤ δ)
    (hA : ∑ i ∈ s, ‖c i‖ ≤ A)
    (hlarge : A*δ < ‖∑ i ∈ s, c i*z i‖) :
    ∃ i ∈ s, δ < ‖z i‖ := by
  classical
  by_contra! h
  have hb : ‖∑ i ∈ s, c i*z i‖ ≤ A*δ := calc
    _ ≤ ∑ i ∈ s, ‖c i*z i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖c i‖*‖z i‖ := by simp only [norm_mul]
    _ ≤ ∑ i ∈ s, ‖c i‖*δ := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (h i hi) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖c i‖)*δ := by rw [Finset.sum_mul]
    _ ≤ A*δ := mul_le_mul_of_nonneg_right hA hδ
  exact (not_lt_of_ge hb) hlarge

/-- Extract a pair from the two structured expansions. -/
theorem v26_weighted_pair_witness {I J : Type*} (s : Finset I) (t : Finset J)
    (a : I → ℂ) (b : J → ℂ) (z : I → J → ℂ)
    (A B δ : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hδ : 0 ≤ δ)
    (ha : ∑ i ∈ s, ‖a i‖ ≤ A) (hb : ∑ j ∈ t, ‖b j‖ ≤ B)
    (hlarge : A*(B*δ) < ‖∑ i ∈ s, a i*(∑ j ∈ t, b j*z i j)‖) :
    ∃ i ∈ s, ∃ j ∈ t, δ < ‖z i j‖ := by
  obtain ⟨i, hi, hz⟩ := v26_weighted_witness s a
    (fun i => ∑ j ∈ t, b j*z i j) A (B*δ) (mul_nonneg hB0 hδ) ha hlarge
  obtain ⟨j, hj, hzij⟩ := v26_weighted_witness t b (z i) B δ hδ hb hz
  exact ⟨i, hi, j, hj, hzij⟩

/-- Pointwise tail clipping inequality for arbitrary real powers q ≥ p.
This is the exact inequality integrated in the clipping part of Lemma 4.12. -/
theorem v26_clipping_tail_pointwise (x B p q : ℝ)
    (hx : 0 ≤ x) (hB : 0 < B) (hpq : p ≤ q) :
    (if B < x then x^p else 0) ≤ B^(p-q)*x^q := by
  by_cases h : B < x
  · rw [if_pos h]
    have hxp : 0 < x := hB.trans h
    have hh : B^(q-p) ≤ x^(q-p) :=
      Real.rpow_le_rpow hB.le h.le (sub_nonneg.mpr hpq)
    have hpos : 0 < B^(q-p) := Real.rpow_pos_of_pos hB _
    have hmul := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hx p)
    rw [← Real.rpow_add hxp] at hmul
    have hqp : p+(q-p) = q := by ring
    rw [hqp] at hmul
    have he : p-q = -(q-p) := by ring
    rw [he, Real.rpow_neg hB.le]
    calc
      x^p ≤ x^q / B^(q-p) := (le_div_iff₀ hpos).2 (by simpa [mul_comm] using hmul)
      _ = (B^(q-p))⁻¹*x^q := by ring
  · rw [if_neg h]
    positivity

/-- Integrate the clipping bound against an arbitrary measure, with explicit
integrability obligations for both powers. -/
theorem v26_clipping_tail_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (B p q : ℝ) (hB : 0 < B) (hpq : p ≤ q)
    (hn : ∀ᵐ x ∂μ, 0 ≤ f x)
    (h1 : Integrable (fun x => if B < f x then (f x)^p else 0) μ)
    (h2 : Integrable (fun x => (f x)^q) μ) :
    (∫ x, (if B < f x then (f x)^p else 0) ∂μ) ≤
       B^(p-q)*(∫ x, (f x)^q ∂μ) := by
  calc
    _ ≤ ∫ x, B^(p-q)*(f x)^q ∂μ := by
      apply integral_mono_ae h1 (h2.const_mul _)
      filter_upwards [hn] with x hx
      exact v26_clipping_tail_pointwise (f x) B p q hx hB hpq
    _ = _ := by rw [integral_const_mul]

end OpenAI086
