import ReferenceV60CorePath

/-! V63: simultaneous pair-mass and powered-mass estimates for the actual
pinned reference progression tests. The reference path and mode hypotheses
are retained; this is not an independent proof or a manuscript-data isomorphism. -/
namespace OpenAI086.ReferenceV63
open Auto MeasureTheory Metric
open scoped BigOperators ENNReal
noncomputable section
open Classical

variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams} (D : fp.SideInput)

theorem four_joint_count {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (G : bf.Grp) (h : ℕ) (hh : 10 ≤ h) (hhJ : h ≤ D.SP.Jst)
    (Cs : Finset (ℤ × ℤ)) (rep : ∀ j, ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j G).Md)
    (hrep : ∀ j, D.RepOK G j h Cs (rep j)) (hΛ : ∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) (z : ChartTag)
    (hz : ∀ j, (D.Ms j G).zc = z) (hdim : z.dim ≤ D.S.dmax) {S : Finset ℤ}
    {cellOf : ℤ → ℤ × ℤ} {xs : ℝ}
    (hpath : ∀ s ∈ S, cellOf s ∈ Cs ∧ xs ∈ dyadicGridCell A.G (cellOf s).1 (cellOf s).2)
    (hcell : ∀ s, (cellOf s).1 = s)
    {ancOf : ∀ s, D.AncNe G (cellOf s) → ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G
      (D.preAt (cellOf s)) (A.blkStart D.S.K (cellOf s).1 - 4 * D.S.K))}
    (hanc : D.FourPathAnc G h Cs rep hrep cellOf ancOf S) (c : ℝ × ℝ × (Fin 4 → ℝ))
    (hc : 0 < c.1 ∧ 0 ≤ c.2.1) (κ : Fin 4 → ℕ × ℕ) {M : ℝ}
    (hM : ∀ i, ((S.biUnion fun s => (D.fourPathE G h xs cellOf ancOf c κ s).image
      fun x => x i).card : ℝ) ≤ M) (hMp : 0 < M) :
    let m : Fin 4 → ℝ := fun i => ((S.biUnion fun s => (D.fourPathE G h xs cellOf ancOf c κ s).image fun x => x i).card : ℝ)
    let L₀ : ℝ := max 1 (fourMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1))
    (∀ i j, i ≠ j → ∑ s ∈ S, ((D.fourPathE G h xs cellOf ancOf c κ s).card : ℝ) ≤ L₀ * m i * m j) ∧
    ∑ t ∈ S, ((D.fourPathE G h xs cellOf ancOf c κ t).card : ℝ) ^ (1 - 1 / 4160 : ℝ) ≤
      2 * max 1 (3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (4 * (2 * c.2.1)) / c.1)) * fourMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12) * M ^ (2 - 1 / 2080 : ℝ) := by
  have hΔ : D.SP.Δ = 10 := by rw [hSP]; rfl
  have ht := D.four_core_total_side hV hCA hd2 hD hB hΔ G h hh Cs rep hrep hΛ z hz hpath hcell hanc c κ
  refine ⟨?_, OpenAI086.ReferenceV60.four_paper_powered D hV hCA hCT hd2 hD hB hQ0 hSP hdD G h hh hhJ Cs rep hrep hΛ z hz hdim hpath hcell hanc c hc κ hM hMp⟩
  intro i j hij
  refine (ht.1 i j hij).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem three_joint_count {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (G : bf.Grp) (h : ℕ) (hh : 10 ≤ h) (hhJ : h ≤ D.SP.Jst)
    (l : Fin 4) (Cs : Finset (ℤ × ℤ))
    (rep : ∀ j, ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j G).Md)
    (hrep : ∀ j, D.RepOK G j h Cs (rep j)) (hΛ : ∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) (z : ChartTag)
    (hz : ∀ j, (D.Ms j G).zc = z) (hdim : z.dim ≤ D.S.dmax) {S : Finset ℤ}
    {cellOf : ℤ → ℤ × ℤ} {xs : ℝ}
    (hpath : ∀ s ∈ S, cellOf s ∈ Cs ∧ xs ∈ dyadicGridCell A.G (cellOf s).1 (cellOf s).2)
    (hcell : ∀ s, (cellOf s).1 = s)
    {ancOf : ∀ s, D.AncNe3 G (cellOf s) l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G
      (D.preAt (cellOf s)) (A.blkStart D.S.K (cellOf s).1 - 4 * D.S.K))}
    (hanc : D.ThreePathAnc G h l Cs rep hrep cellOf ancOf S) {Iw : ℕ}
    (hIw : (2 : ℝ) ^ Iw ≤ 2 * D.U0) (c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ))
    (hc : 0 < c.1 ∧ 0 ≤ c.2.1) (κ : Fin 4 → ℕ × ℕ) {M : ℝ}
    (hM : ∀ i, i ≠ l → ((S.biUnion fun s => (D.threePathE G h xs l cellOf ancOf Iw c κ s).image
      fun x => x i).card : ℝ) ≤ M)
    (hMl : ∑ s ∈ S, D.sideWeight G l cellOf c.2.2.2.1 s ≤ M) (hMp : 0 < M) :
    let m : Fin 4 → ℝ := fun i => if i = l then (∑ s ∈ S, D.sideWeight G l cellOf c.2.2.2.1 s) else ((S.biUnion fun s => (D.threePathE G h xs l cellOf ancOf Iw c κ s).image fun x => x i).card : ℝ)
    let L₀ : ℝ := max 1 (threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1))
    (∀ i j, i ≠ j → ∑ s ∈ S, ((D.threePathE G h xs l cellOf ancOf Iw c κ s).card : ℝ) ≤ L₀ * m i * m j) ∧
    ∑ t ∈ S, ((D.threePathE G h xs l cellOf ancOf Iw c κ t).card : ℝ) ^ (1 - 1 / 4160 : ℝ) ≤
      2 * max 1 (3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (2 * c.2.1) / c.1)) * threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12) * M ^ (2 - 1 / 2080 : ℝ) := by
  have hΔ : D.SP.Δ = 10 := by rw [hSP]; rfl
  have ht := D.three_core_total_side hV hCA hd2 hD hB hΔ G h hh l Cs rep hrep hΛ z hz hpath hcell hanc hIw c κ
  refine ⟨?_, OpenAI086.ReferenceV60.three_paper_powered D hV hCA hCT hd2 hD hB hQ0 hSP hdD G h hh hhJ l Cs rep hrep hΛ z hz hdim hpath hcell hanc hIw c hc κ hM hMl hMp⟩
  intro i j hij
  have hw : 0 ≤ ∑ s ∈ S, D.sideWeight G l cellOf c.2.2.2.1 s :=
    Finset.sum_nonneg fun s hs => D.sideWeight_nonneg G l cellOf c.2.2.2.1 s
  by_cases hi : i = l
  · subst i
    have hj : j ≠ l := Ne.symm hij
    simp only [if_pos rfl, if_neg hj]
    refine (ht.2.1 j hj).trans ?_
    have hc : (1 : ℝ) ≤ max 1 (threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1)) := le_max_left _ _
    calc
      _ = 1 * (∑ s ∈ S, D.sideWeight G l cellOf c.2.2.2.1 s) * _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hw) (Nat.cast_nonneg _)
  · by_cases hj : j = l
    · subst j
      simp only [if_pos rfl, if_neg hi]
      refine (ht.2.1 i hi).trans ?_
      have hc : (1 : ℝ) ≤ max 1 (threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1)) := le_max_left _ _
      calc
        _ = 1 * ((S.biUnion fun s => (D.threePathE G h xs l cellOf ancOf Iw c κ s).image fun x => x i).card : ℝ) * _ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)) hw
    · simp only [if_neg hi, if_neg hj]
      refine (ht.1 i j hij hi hj).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

end
end OpenAI086.ReferenceV63
#print axioms OpenAI086.ReferenceV63.four_joint_count
#print axioms OpenAI086.ReferenceV63.three_joint_count
