import Mathlib

/-! Lemma 8.11, page 76: abstract norm estimates for component-size comparison.
The oscillatory almost-orthogonality and projection leakage bounds remain
explicit hypotheses, rather than being replaced by a finite coordinate proxy. -/
namespace OpenAI086

variable {X : Type*} [NormedAddCommGroup X]

/-- The exact core-minus-side subtotal estimate with projection leakage. -/
theorem v19_component_size_bound (σ2 C floor ε : ℝ) (p total side : X)
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hsize : σ2 ≤ C*‖total-side‖^2+floor)
    (hleak : ‖total-p‖ ≤ ε) :
    σ2 ≤ 4*C*‖p‖^2+2*C*‖side‖^2+4*C*ε^2+floor := by
  have htp : ‖total‖ ≤ ‖p‖+ε := by
    have h := norm_add_le p (total-p)
    have he : p+(total-p)=total := by abel
    rw [he] at h
    linarith
  have hts : ‖total-side‖ ≤ ‖total‖+‖side‖ := by
    simpa [sub_eq_add_neg] using norm_add_le total (-side)
  have hts2 := pow_le_pow_left₀ (norm_nonneg (total-side)) hts 2
  have htp2 := pow_le_pow_left₀ (norm_nonneg total) htp 2
  have h1 : ‖total-side‖^2 ≤ 2*‖total‖^2+2*‖side‖^2 := by
    nlinarith [sq_nonneg (‖total‖-‖side‖)]
  have h2 : ‖total‖^2 ≤ 2*‖p‖^2+2*ε^2 := by
    nlinarith [sq_nonneg (‖p‖-ε)]
  have h3 := mul_le_mul_of_nonneg_left h1 hC
  have h4 := mul_le_mul_of_nonneg_left h2 hC
  nlinarith

/-- Discarding unsuccessful components preserves the lower synthesis
bound and hence the desired side-subtotal energy estimate. -/
theorem v19_successful_side_energy {I : Type*} [Fintype I]
    (S : Finset I) (v : I → X) (C : ℝ)
    (h : (∑ i, ‖v i‖^2) ≤ C*‖∑ i, v i‖^2) :
    (∑ i ∈ S, ‖v i‖^2) ≤ C*‖∑ i, v i‖^2 := by
  classical
  calc
    _ ≤ ∑ i, ‖v i‖^2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ S) (fun i _ _ => sq_nonneg ‖v i‖)
    _ ≤ _ := h

end OpenAI086
