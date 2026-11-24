import OpenAI086.PaperHeightScaleCorrection
import OpenAI086.PaperEvaluationDominance

/-! Corrected Lemma 3.5: finite separated-cover construction and its
integer-scale consequence. The input bound on the number of separated
points is not assumed to follow from a dimension without proof; the
bounded integer dependence argument is isolated below. -/
namespace OpenAI086
open scoped BigOperators

/-- Construct a maximal separated net by finite insertion. Unlike a
preassigned collection of intervals, both the centers and the covering
property are obtained from the input finite set. -/
theorem v32_separated_net (S : Finset ℝ) (W : ℝ) (hW : 0 ≤ W) :
    ∃ P : Finset ℝ, P ⊆ S ∧
      (∀ x ∈ S, ∃ y ∈ P, |x-y| ≤ W) ∧
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → W < |x-y|) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨P, hPS, hc, hs⟩ := ih
    by_cases h : ∃ y ∈ P, |a-y| ≤ W
    · refine ⟨P, ?_, ?_, hs⟩
      · intro x hx
        exact Finset.mem_insert_of_mem (hPS hx)
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact h
        · exact hc x hx
    · refine ⟨insert a P, ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hPS hx)
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨a, Finset.mem_insert_self _ _, by simpa using hW⟩
        · obtain ⟨y, hy, hxy⟩ := hc x hx
          exact ⟨y, Finset.mem_insert_of_mem hy, hxy⟩
      · intro x hx y hy hne
        rcases Finset.mem_insert.mp hx with rfl | hx
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · exact (hne rfl).elim
          · exact lt_of_not_ge (fun hh => h ⟨y, hy, hh⟩)
        · rcases Finset.mem_insert.mp hy with rfl | hy
          · rw [abs_sub_comm]
            exact lt_of_not_ge (fun hh => h ⟨x, hx, hh⟩)
          · exact hs x hx y hy hne

/-- A dimension/packing bound on separated centers now implies a bound
for the full family of integer scales; the annulus width is paid per center.
All coordinates here are logarithms, so a common shift is harmless. -/
theorem v32_separated_scale_count (S : Finset ℝ) (W U : ℝ) (d : ℕ)
    (hW : 0 ≤ W) (hU : 0 ≤ U)
    (hpack : ∀ P : Finset ℝ, P ⊆ S →
      (∀ x ∈ P, ∀ y ∈ P, x ≠ y → W < |x-y|) → P.card ≤ d)
    (N : Finset ℤ)
    (hN : ∀ n ∈ N, ∃ x ∈ S, (n:ℝ) ≤ x ∧ x ≤ (n:ℝ)+U) :
    (N.card : ℝ) ≤ (d:ℝ)*(2*W+U+1) := by
  obtain ⟨P, hPS, hc, hs⟩ := v32_separated_net S W hW
  have hcard : (P.card : ℝ) ≤ (d:ℝ) := by exact_mod_cast hpack P hPS hs
  have hcover : ∀ n ∈ N, ∃ p ∈ P, p-W-U ≤ (n:ℝ) ∧ (n:ℝ) ≤ p+W := by
    intro n hn
    obtain ⟨x, hx, h1, h2⟩ := hN n hn
    obtain ⟨p, hp, hab⟩ := hc x hx
    rw [abs_le] at hab
    exact ⟨p, hp, by linarith, by linarith⟩
  have h := v31_corrected_packet_count P (fun p => p-W-U) (fun p => p+W)
    (2*W) U N (by linarith) hU (by intro p hp; linarith)
    (by intro p hp; linarith) hcover
  exact h.trans (mul_le_mul_of_nonneg_right hcard (by linarith))

/-- A bounded integer dependence cannot involve a dominating last value.
This packages the application of the earlier dominant-relation lemma;
no dimension or determinant assertion is hidden in the result. -/
theorem v32_no_bounded_relation_at_maximum {I : Type*} [DecidableEq I]
    (s : Finset I) (j : I) (hj : j ∈ s) (c : I → ℤ) (v : I → ℝ)
    (H M : ℝ) (hH : 0 ≤ H) (hM : 0 ≤ M) (hc : c j ≠ 0)
    (hcoeff : ∀ i ∈ s, |(c i:ℝ)| ≤ H)
    (hval : ∀ i ∈ s.erase j, |v i| ≤ M)
    (hgap : (s.erase j).card * H * M < |v j|) :
    (∑ i ∈ s, (c i:ℝ)*v i) ≠ 0 := by
  apply v29_dominant_integer_relation s j hj c v H M hH hM hc _ hgap
  intro i hi
  exact ⟨hcoeff i (Finset.mem_of_mem_erase hi), hval i hi⟩

end OpenAI086
