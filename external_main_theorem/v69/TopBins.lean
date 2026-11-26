import TrilinearHT.Auto.Sec16_2QuantitativeInequality

/-! Proposition 8.12, equation (28), on the reference's actual representative
classes and retained uses. Convert tested threshold counts to counts in
amplitude bins, including bins below Dstar^-1 and above the amplitude cap.
This does not identify the reference dyadic types with the paper's floor-log
base 1.1 types, or establish the analytic overhead M. -/
namespace OpenAI086.ReferenceV69
open Auto
open scoped BigOperators

open Classical in
noncomputable def binCount {Gd : RealDyadicGrid} {ι : Type*} [Fintype ι] {n : ℕ}
    (Ms : ι → ModeSystem Gd n) (S : ModeSchedule) (hA : 6 ≤ S.A0) (SP : SideParams)
    (q : ι → ℕ) {Δ h : ℕ}
    (R : ∀ G, (Ms G).RepClass (S.withQ0 (q G)) hA SP Δ h)
    (X : ∀ G, Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md)))
    (sz : ∀ G, (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md) → ℝ) (σ y : ℝ) : ℝ :=
  ∑ G, (((X G).filter fun p => y ∈ dyadicGridCell Gd p.1.1 p.1.2 ∧
    σ ^ 2 ≤ sz G p ∧ sz G p < (2 * σ) ^ 2).image (fun p => (R G).rep p.2)).card

open Classical in
theorem actual_bin_bound {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀}
    {ι : Type*} [Fintype ι] {n : ℕ} (Ms : ι → ModeSystem A.G n)
    (S : ModeSchedule) (hA : 6 ≤ S.A0) (SP : SideParams) (q : ι → ℕ) {Δ h : ℕ}
    (R : ∀ G, (Ms G).RepClass (S.withQ0 (q G)) hA SP Δ h)
    (X : ∀ G, Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md))) (hX : ∀ G, (R G).Inst (X G))
    (hpath : ∀ y, (∑ G, ((Ms G).ptSet y).card : ℝ) ≤ S.Dstar)
    (sz : ∀ G, (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × (Ms G).Md) → ℝ)
    {U M : ℝ} (hD : 2 ≤ S.Dstar) (hM : 1 ≤ M) (hU : S.Dstar⁻¹ ≤ U)
    (hsize : ∀ G p, p ∈ X G → sz G p ≤ U ^ 2)
    (hTop : ∀ σ ∈ dyThr S.Dstar⁻¹ U S.Dstar, ∀ y,
      (∑ G, (((X G).filter fun p => y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
        σ ^ 2 ≤ sz G p).image (fun p => (R G).rep p.2)).card : ℝ) ≤ M / σ ^ 2)
    (σ y : ℝ) (hσ : 0 < σ) (hdy : ∃ j : ℤ, σ = (2 : ℝ) ^ j) :
    binCount Ms S hA SP q R X sz σ y ≤ min S.Dstar (M / σ ^ 2) := by
  have hsub : binCount Ms S hA SP q R X sz σ y ≤
      (∑ G, (((X G).filter fun p => y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
        σ ^ 2 ≤ sz G p).image (fun p => (R G).rep p.2)).card : ℝ) := by
    unfold binCount
    refine Finset.sum_le_sum fun G _ => Nat.cast_le.mpr (Finset.card_le_card ?_)
    apply Finset.image_subset_image
    intro p hp
    obtain ⟨hpX, hy, hlo, _⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpX, hy, hlo⟩
  have hglobal := hsub.trans (ActiveSetup.BasicFamilies.FamParams.usedReps_le_Dstar (A := A)
    Ms S hA SP q R X hX hpath sz σ y)
  refine le_min hglobal ?_
  have hDp : 0 < S.Dstar := by linarith
  have hinv : 0 < S.Dstar⁻¹ := inv_pos.mpr hDp
  by_cases hlo : S.Dstar⁻¹ ≤ σ
  · by_cases hhi : σ ≤ U
    · have hs := (dyThr_spec hinv hU hU).2.2.1 σ hlo hhi hdy hlo
      exact hsub.trans (hTop σ hs y)
    · have hz : binCount Ms S hA SP q R X sz σ y = 0 := by
        unfold binCount
        apply Finset.sum_eq_zero
        intro G _
        have he : (X G).filter (fun p => y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
            σ ^ 2 ≤ sz G p ∧ sz G p < (2 * σ) ^ 2) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro p hp
          obtain ⟨hpX, _, hlow, _⟩ := Finset.mem_filter.mp hp
          have hU0 : 0 < U := hinv.trans_le hU
          have hlt : U ^ 2 < σ ^ 2 := by
            nlinarith [mul_pos (sub_pos.mpr (not_le.mp hhi)) (add_pos hσ hU0)]
          exact (not_lt_of_ge (hlow.trans (hsize G p hpX))) hlt
        simp [he]
      rw [hz]
      positivity
  · apply hglobal.trans
    apply (le_div_iff₀ (sq_pos_of_pos hσ)).2
    have hs : σ ≤ S.Dstar⁻¹ := (not_le.mp hlo).le
    have hsq : σ ^ 2 ≤ (S.Dstar⁻¹) ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ σ + S.Dstar⁻¹ by positivity)]
    calc
      S.Dstar * σ ^ 2 ≤ S.Dstar * (S.Dstar⁻¹) ^ 2 := mul_le_mul_of_nonneg_left hsq hDp.le
      _ = S.Dstar⁻¹ := by field_simp
      _ ≤ 1 := (inv_le_one₀ hDp).2 (by linarith)
      _ ≤ M := hM

end OpenAI086.ReferenceV69
#print axioms OpenAI086.ReferenceV69.actual_bin_bound
