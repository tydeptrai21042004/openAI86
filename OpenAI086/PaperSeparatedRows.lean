import Mathlib
import OpenAI086.FiniteRowCauchySchwarz

/-! Lemma 8.7 p.71. Pointwise pathwise multiplicity bound for the
cross terms in synthesis. No bound on the total number of rows is used.
The oscillatory estimate and its integration on dyadic cells remain open. -/
namespace OpenAI086

/-- Cauchy–Schwarz on the actually participating set, not the global rows. -/
theorem v20_path_synthesis_square {I : Type*} [DecidableEq I]
    (s : Finset I) (b : I → ℝ) (D : ℝ) (hD : (s.card:ℝ) ≤ D) :
    (∑ i ∈ s, b i)^2 ≤ D*(∑ i ∈ s, (b i)^2) := by
  classical
  have h := finite_row_cauchy_schwarz (fun i : s => b i) (fun _ : s => (1:ℝ))
  have hs : (∑ i ∈ s, (b i)^2) ≥ 0 := Finset.sum_nonneg (fun i _ => sq_nonneg (b i))
  have h' : (∑ i ∈ s, b i)^2 ≤ (∑ i ∈ s, (b i)^2)*(s.card:ℝ) := by
    simpa [Finset.sum_attach] using h
  calc
    _ ≤ _ := h'
    _ ≤ _ := by rw [mul_comm (∑ i ∈ s, (b i)^2) (s.card:ℝ)]; exact mul_le_mul_of_nonneg_right hD hs

/-- Close the synthesis estimate once the integrated cross-term and
private-coordinate bounds of the paper have been obtained. -/
theorem v20_separated_synthesis_budget (S cross B D ε : ℝ)
    (hD : 0 ≤ D) (hε : 0 ≤ ε)
    (hdiag : S ≤ B+cross) (hcross : cross ≤ ε*D*D^2*B) :
    S ≤ (1+ε*D^3)*B := by
  calc
    S ≤ B+cross := hdiag
    _ ≤ B+ε*D*D^2*B := add_le_add_left hcross B
    _ = _ := by ring

end OpenAI086
