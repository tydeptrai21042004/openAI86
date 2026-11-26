import OpenAI086.PaperV42AccuracyTail

/-! Section 10.4: the actual weighted accuracy series controls all finite
cutoffs, after accounting for the number of tuples at each level. The
analytic per-tuple estimate and convergence of the base expansion remain
hypotheses; this module does not assume the desired total coefficient. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

/-- Sum the individual tuple bounds using the O(t) multiplicity. No
uniform bound on the total number of tuples across levels is required. -/
theorem v57_tuple_cutoff_bound {I : Type*} (S : ℕ → Finset I)
    (cost : ℕ → I → ℝ) (w : ℕ → ℝ) (B CN R ε : ℝ) (m n : ℕ)
    (hB : 0 ≤ B) (hCN : 0 ≤ CN) (hR : 0 ≤ R)
    (hw : ∀ j, 0 ≤ w j)
    (hcount : ∀ j, ((S j).card : ℝ) ≤ B*((j:ℝ)+m))
    (hcost : ∀ j i, i ∈ S j → cost j i ≤ w j*(1+CN)*R)
    (hs : Summable (fun j : ℕ => ((j:ℝ)+m)*w j))
    (ht : (∑' j : ℕ, ((j:ℝ)+m)*w j) ≤ ε) :
    (∑ j ∈ Finset.range n, ∑ i ∈ S j, cost j i) ≤ B*ε*(1+CN)*R := by
  classical
  have hlevel : ∀ j, (∑ i ∈ S j, cost j i) ≤ B*(((j:ℝ)+m)*w j)*(1+CN)*R := by
    intro j
    calc
      _ ≤ ∑ _i ∈ S j, w j*(1+CN)*R := Finset.sum_le_sum fun i hi => hcost j i hi
      _ = ((S j).card:ℝ)*(w j*(1+CN)*R) := by simp [nsmul_eq_mul]
      _ ≤ (B*((j:ℝ)+m))*(w j*(1+CN)*R) :=
        mul_le_mul_of_nonneg_right (hcount j) (mul_nonneg (mul_nonneg (hw j) (by linarith)) hR)
      _ = _ := by ring
  have hnonneg : ∀ j : ℕ, 0 ≤ ((j:ℝ)+m)*w j := fun j => mul_nonneg (by positivity) (hw j)
  have hcut : (∑ j ∈ Finset.range n, ((j:ℝ)+m)*w j) ≤ ε :=
    (hs.sum_le_tsum _ (fun j _ => hnonneg j)).trans ht
  calc
    _ ≤ ∑ j ∈ Finset.range n, B*(((j:ℝ)+m)*w j)*(1+CN)*R := Finset.sum_le_sum fun j _ => hlevel j
    _ = B*(∑ j ∈ Finset.range n, ((j:ℝ)+m)*w j)*(1+CN)*R := by
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcut hB) (by linarith)) hR

/-- A single initial accuracy works for every finite cutoff and every
choice of tuple sets obeying the stated multiplicity and per-tuple estimate.
B is the constant that includes the segment/restart packing cost. -/
theorem v57_choose_uniform_tuple_cutoff (A c θ ε K B : ℝ) (m : ℕ)
    (hA : 2 ≤ A) (hc : 0 < c) (hθ : 0 < θ) (hε : 0 < ε) (hB : 0 < B) (hm : 0 < m) :
    ∃ k : ℝ, K ≤ k ∧ 1 ≤ k ∧
      ∀ {I : Type} (S : ℕ → Finset I) (cost : ℕ → I → ℝ) (CN R : ℝ) (n : ℕ),
        0 ≤ CN → 0 ≤ R →
        (∀ j, ((S j).card : ℝ) ≤ B*((j:ℝ)+m)) →
        (∀ j i, i ∈ S j → cost j i ≤ Real.exp (-c*(v42Accuracy A k j)^θ)*(1+CN)*R) →
        (∑ j ∈ Finset.range n, ∑ i ∈ S j, cost j i) ≤ ε*(1+CN)*R := by
  obtain ⟨k,hK,hk,hs,ht⟩ := v42_choose_accuracy_start A c θ (ε/B) K m hA hc hθ
    (div_pos hε hB) hm
  refine ⟨k,hK,hk,?_⟩
  intro I S cost CN R n hCN hR hcount hcost
  have hb := v57_tuple_cutoff_bound S cost (fun j => Real.exp (-c*(v42Accuracy A k j)^θ))
    B CN R (ε/B) m n hB.le hCN hR (fun j => (Real.exp_pos _).le) hcount hcost hs ht
  rw [show B*(ε/B)=ε by field_simp [hB.ne']] at hb
  exact hb

/-- The uniform estimate survives a limit of cutoff costs with a vanishing
remainder. This is the last limiting deduction, not a construction of the
analytic convergence of the actual staggered expansion. -/
theorem v57_cutoff_limit_bound (a : ℕ → ℝ) (L R A c CN : ℝ)
    (hlim : Filter.Tendsto a Filter.atTop (nhds L))
    (hb : ∀ n, a n ≤ (A+c*CN)*R) : L ≤ (A+c*CN)*R := by
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hb)

end OpenAI086
