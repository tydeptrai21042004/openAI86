import OpenAI086.PaperHeightBoundedRelation
import OpenAI086.PaperEvaluationDominance

/-! Bounded rational dependence applied to real evaluations. Integer
vectors v represent the cleared rational columns q_i a_i. This connects
integer-box dependence to the obstruction for d+1 separated magnitudes.
Actual rational denominator selection and the net-to-vector lift are separate. -/
namespace OpenAI086
open scoped BigOperators

/-- A chain of d+1 evaluations cannot grow by the stated factor once the
rational columns have been cleared with bounded positive denominators. -/
theorem v32_no_long_cleared_chain (d M Q : ℕ)
    (v : Fin (d+1) → Fin d → ℤ) (q : Fin (d+1) → ℤ)
    (ξ : Fin d → ℝ) (u : Fin (d+1) → ℝ)
    (hv : ∀ i j, |v i j| ≤ (M:ℤ))
    (hq : ∀ i, 0 < q i ∧ q i ≤ (Q:ℤ))
    (hu : ∀ i, (q i:ℝ)*u i = ∑ j, (v i j:ℝ)*ξ j)
    (hpos : ∀ i, 0 < |u i|)
    (hgap : ∀ i j : Fin (d+1), i < j →
      (d:ℝ)*(((2*(d+1)*M+1)^d:ℕ):ℝ)*(Q:ℝ)*|u i| < |u j|) : False := by
  classical
  let K : ℕ := (2*(d+1)*M+1)^d
  obtain ⟨c, hc, hcB, hrel⟩ := v32_integer_box_dependence d M v hv
  let s : Finset (Fin (d+1)) := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hc
    exact ⟨i, by simp [s, hi]⟩
  let j := s.max' hs
  have hj : j ∈ s := Finset.max'_mem s hs
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hj).2
  let a : Fin (d+1) → ℤ := fun i => c i*q i
  have haj : a j ≠ 0 := mul_ne_zero hcj (ne_of_gt (hq j).1)
  have hcoeff : ∀ i ∈ s, |(a i:ℝ)| ≤ (K:ℝ)*(Q:ℝ) := by
    intro i hi
    have hc' : |(c i:ℝ)| ≤ (K:ℝ) := by exact_mod_cast hcB i
    have hq' : (q i:ℝ) ≤ (Q:ℝ) := by exact_mod_cast (hq i).2
    have hq0 : (0:ℝ) ≤ (q i:ℝ) := by exact_mod_cast (hq i).1.le
    dsimp [a]
    rw [Int.cast_mul, abs_mul, abs_of_nonneg hq0]
    exact mul_le_mul hc' hq' hq0 (by positivity)
  have hz : (∑ i : Fin (d+1), (a i:ℝ)*u i) = 0 := by
    calc
      _ = ∑ i : Fin (d+1), ∑ k : Fin d, (c i:ℝ)*((v i k:ℝ)*ξ k) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [a]
        rw [Int.cast_mul, mul_assoc, hu, Finset.mul_sum]
      _ = ∑ k : Fin d, (∑ i : Fin (d+1), (c i:ℝ)*(v i k:ℝ))*ξ k := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have h : (∑ i : Fin (d+1), (c i:ℝ)*(v i k:ℝ)) = 0 := by exact_mod_cast hrel k
        rw [h, zero_mul]
  have hzs : (∑ i ∈ s, (a i:ℝ)*u i) = 0 := by
    rw [show (∑ i ∈ s, (a i:ℝ)*u i) = ∑ i : Fin (d+1), (a i:ℝ)*u i by
      apply Finset.sum_subset (Finset.subset_univ s)
      intro i hi hni
      have hci : c i = 0 := by simpa [s] using hni
      simp [a, hci]]
    exact hz
  -- A dependence supported only at j already contradicts positivity.
  by_cases he : (s.erase j).Nonempty
  · -- Pick the largest magnitude among the remaining terms.
    obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (s.erase j) (fun i => |u i|) he
    have hkj : k < j := lt_of_le_of_ne
      (Finset.le_max' s k (Finset.mem_of_mem_erase hk)) (Finset.ne_of_mem_erase hk)
    have hcard : (s.erase j).card ≤ d := by
      have hsub := Finset.card_le_card (Finset.subset_univ s)
      rw [Finset.card_univ, Fintype.card_fin] at hsub
      have h := Finset.card_erase_of_mem hj
      omega
    have hcardR : ((s.erase j).card:ℝ) ≤ (d:ℝ) := by exact_mod_cast hcard
    have hgap' : ((s.erase j).card:ℝ)*((K:ℝ)*(Q:ℝ))*|u k| < |u j| := by
      calc
        _ ≤ (d:ℝ)*((K:ℝ)*(Q:ℝ))*|u k| := by gcongr
        _ = (d:ℝ)*(K:ℝ)*(Q:ℝ)*|u k| := by ring
        _ < _ := by simpa [K] using hgap k j hkj
    exact (v29_dominant_integer_relation s j hj a u ((K:ℝ)*(Q:ℝ)) |u k|
      (by positivity) (abs_nonneg _) haj
      (fun i hi => ⟨hcoeff i (Finset.mem_of_mem_erase hi), hkmax i hi⟩) hgap') hzs
  · have hgap' : ((s.erase j).card:ℝ)*((K:ℝ)*(Q:ℝ))*0 < |u j| := by simpa using hpos j
    exact (v29_dominant_integer_relation s j hj a u ((K:ℝ)*(Q:ℝ)) 0
      (by positivity) (by norm_num) haj
      (fun i hi => (he ⟨i, hi⟩).elim) hgap') hzs

end OpenAI086
