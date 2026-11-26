import TrilinearHT.Auto.Sec15_5OneDistributionCalculationFinalSums

/-! Reference-backed applications of Lemma 9.1, with the printed density
exponent and the actual path/anchor data, not abstract tuple counts. -/
namespace OpenAI086.ReferenceV60
open Auto MeasureTheory Metric
open scoped BigOperators ENNReal
noncomputable section
open Classical
theorem paper_powered_count_ref {ι : Type*} (s : Finset ι) (N : ι → ℝ)
    {M B : ℝ} (hM : 0 < M) (hB : 0 < B)
    (hN0 : ∀ i ∈ s, 0 ≤ N i) (hNM : ∀ i ∈ s, N i ≤ M ^ 2)
    (hsparse : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∑ i ∈ s.filter (fun i => N i ≤ δ * M ^ 2), N i ≤
        B * δ ^ (1 / 2080 : ℝ) * M ^ 2) :
    ∑ i ∈ s, N i ^ (1 - 1 / 4160 : ℝ) ≤ 2 * B * M ^ (2 - 1 / 2080 : ℝ) := by
  classical
  have hA := hsparse 1 one_pos le_rfl
  have heq : s.filter (fun i => N i ≤ 1 * M ^ 2) = s :=
    Finset.filter_true_of_mem (fun i hi => by simpa using hNM i hi)
  rw [heq, Real.one_rpow, mul_one] at hA
  have h := Auto.distribution_power s N hM hN0 hNM hA (by positivity : 0 < B * M ^ 2)
    hB hsparse (by norm_num) (by norm_num) (ε := 1 / 4160) (by norm_num) (by norm_num)
  calc
    _ ≤ (1 / 2080 : ℝ) / (1 / 2080 - 1 / 4160) *
      (B * M ^ 2) ^ (1 - (1 / 4160) / (1 / 2080) : ℝ) *
      B ^ ((1 / 4160) / (1 / 2080) : ℝ) *
      M ^ (2 * (1 / 4160) * (1 / (1 / 2080) - 1) : ℝ) := h
    _ = 2 * B * M ^ (2 - 1 / 2080 : ℝ) := by
      rw [show (1 / 2080 : ℝ) / (1 / 2080 - 1 / 4160) = 2 by norm_num,
        show (1 - (1 / 4160) / (1 / 2080) : ℝ) = 1/2 by norm_num,
        show ((1 / 4160) / (1 / 2080) : ℝ) = 1/2 by norm_num,
        show (2 * (1 / 4160) * (1 / (1 / 2080) - 1) : ℝ) = 1 - 1/2080 by norm_num,
        Real.mul_rpow hB.le (sq_nonneg M)]
      have hMs : (M ^ 2) ^ (1/2 : ℝ) = M := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
        norm_num
      rw [hMs]
      calc
        2 * (B ^ (1/2 : ℝ) * M) * B ^ (1/2 : ℝ) * M ^ (1 - 1/2080 : ℝ) =
            2 * (B ^ (1/2 : ℝ) * B ^ (1/2 : ℝ)) *
              (M ^ (1 : ℝ) * M ^ (1 - 1/2080 : ℝ)) := by rw [Real.rpow_one]; ring
        _ = _ := by
          rw [← Real.rpow_add hB, ← Real.rpow_add hM,
            show (1/2 + 1/2 : ℝ) = 1 by norm_num, Real.rpow_one]
          rw [show (1 + (1 - 1/2080) : ℝ) = 2 - 1/2080 by ring]


variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams} (D : fp.SideInput)

theorem four_paper_density {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
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
      fun x => x i).card : ℝ) ≤ M) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∑ s ∈ S.filter (fun s => ((D.fourPathE G h xs cellOf ancOf c κ s).card : ℝ) ≤ δ * M ^ 2),
        ((D.fourPathE G h xs cellOf ancOf c κ s).card : ℝ) ≤
      3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (4 * (2 * c.2.1)) / c.1)) *
        fourMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12 *
        δ ^ (1 / 2080 : ℝ) * M ^ 2 := by
  have hb := D.four_core_applied_side hV hCA hCT hd2 hD hB hQ0 hSP hdD G h hh hhJ Cs rep hrep hΛ z hz hdim hpath hcell hanc c κ hM hδ0 hδ1
  have hd : δ ^ (1 / 300 : ℝ) ≤ δ ^ (1 / 2080 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hδ0.le hδ1 (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (4 * (2 * c.2.1)) / c.1) := by
    apply Real.logb_nonneg (by norm_num)
    have hh : 0 ≤ ((z.dim : ℝ) + 1) ^ 2 * (4 * (2 * c.2.1)) / c.1 := by
      have := hc.1
      have := hc.2
      positivity
    linarith
  have hpow : 0 ≤ fourMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12 := by
    rw [show (12 : ℕ) = 6 + 6 by norm_num, pow_add, ← sq]
    exact sq_nonneg _
  have hcoef : 0 ≤ 3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (4 * (2 * c.2.1)) / c.1)) * fourMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12 := by positivity
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hcoef) (sq_nonneg M))

theorem three_paper_density {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
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
    (hMl : ∑ s ∈ S, D.sideWeight G l cellOf c.2.2.2.1 s ≤ M) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∑ s ∈ S.filter (fun s =>
        ((D.threePathE G h xs l cellOf ancOf Iw c κ s).card : ℝ) ≤ δ * M ^ 2),
        ((D.threePathE G h xs l cellOf ancOf Iw c κ s).card : ℝ) ≤
      3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (2 * c.2.1) / c.1)) *
        threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12 *
        δ ^ (1 / 2080 : ℝ) * M ^ 2 := by
  have hb := D.three_core_applied_side hV hCA hCT hd2 hD hB hQ0 hSP hdD G h hh hhJ l Cs rep hrep hΛ z hz hdim hpath hcell hanc hIw c κ hM hMl hδ0 hδ1
  have hd : δ ^ (1 / 300 : ℝ) ≤ δ ^ (1 / 2080 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hδ0.le hδ1 (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (2 * c.2.1) / c.1) := by
    apply Real.logb_nonneg (by norm_num)
    have hh : 0 ≤ ((z.dim : ℝ) + 1) ^ 2 * (2 * c.2.1) / c.1 := by
      have := hc.1
      have := hc.2
      positivity
    linarith
  have hpow : 0 ≤ threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12 := by
    rw [show (12 : ℕ) = 6 + 6 by norm_num, pow_add, ← sq]
    exact sq_nonneg _
  have hcoef : 0 ≤ 3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (2 * c.2.1) / c.1)) * threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12 := by positivity
  exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hcoef) (sq_nonneg M))

theorem four_paper_powered {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
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
    ∑ t ∈ S, ((D.fourPathE G h xs cellOf ancOf c κ t).card : ℝ) ^ (1 - 1 / 4160 : ℝ) ≤
      2 * max 1 (3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (4 * (2 * c.2.1)) / c.1)) * fourMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12) * M ^ (2 - 1 / 2080 : ℝ) := by
  have hΔ : D.SP.Δ = 10 := by rw [hSP]; rfl
  have ht := D.four_core_total_side hV hCA hd2 hD hB hΔ G h hh Cs rep hrep hΛ z hz hpath hcell hanc c κ
  let N : ℤ → ℝ := fun t => ((D.fourPathE G h xs cellOf ancOf c κ t).card : ℝ)
  have hN0 : ∀ t ∈ S, 0 ≤ N t := fun t _ => Nat.cast_nonneg _
  have hNM : ∀ t ∈ S, N t ≤ M ^ 2 := by
    intro t htS
    have h := ht.2 0 1 (by decide) t htS
    have h0 := hM 0
    have h1 := hM 1
    refine h.trans ?_
    rw [pow_two]
    exact mul_le_mul h0 h1 (Nat.cast_nonneg _) hMp.le
  refine paper_powered_count_ref S N hMp (lt_of_lt_of_le one_pos (le_max_left _ _)) hN0 hNM ?_
  intro δ hδ0 hδ1
  have hb := four_paper_density D hV hCA hCT hd2 hD hB hQ0 hSP hdD G h hh hhJ Cs rep hrep hΛ z hz hdim hpath hcell hanc c κ hM hδ0 hδ1
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδ0.le _)) (sq_nonneg M)

theorem three_paper_powered {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
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
    ∑ t ∈ S, ((D.threePathE G h xs l cellOf ancOf Iw c κ t).card : ℝ) ^ (1 - 1 / 4160 : ℝ) ≤
      2 * max 1 (3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((z.dim : ℝ) + 1) ^ 2 * (2 * c.2.1) / c.1)) * threeMult z.dim (D.S.Dstar ^ 5 * D.S.Eh (h - D.SP.Δ)) c.1 (2 * c.2.1) ^ 12) * M ^ (2 - 1 / 2080 : ℝ) := by
  have hΔ : D.SP.Δ = 10 := by rw [hSP]; rfl
  have ht := D.three_core_total_side hV hCA hd2 hD hB hΔ G h hh l Cs rep hrep hΛ z hz hpath hcell hanc hIw c κ
  let N : ℤ → ℝ := fun t => ((D.threePathE G h xs l cellOf ancOf Iw c κ t).card : ℝ)
  have hN0 : ∀ t ∈ S, 0 ≤ N t := fun t _ => Nat.cast_nonneg _
  have hNM : ∀ t ∈ S, N t ≤ M ^ 2 := by
    intro t htS
    obtain ⟨i, j, hij, hil, hjl⟩ := Auto.exists_two_core l
    have h := ht.2.2 i j hij hil hjl t htS
    refine h.trans ?_
    rw [pow_two]
    exact mul_le_mul (hM i hil) (hM j hjl) (Nat.cast_nonneg _) hMp.le
  refine paper_powered_count_ref S N hMp (lt_of_lt_of_le one_pos (le_max_left _ _)) hN0 hNM ?_
  intro δ hδ0 hδ1
  have hb := three_paper_density D hV hCA hCT hd2 hD hB hQ0 hSP hdD G h hh hhJ l Cs rep hrep hΛ z hz hdim hpath hcell hanc hIw c κ hM hMl hδ0 hδ1
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hδ0.le _)) (sq_nonneg M)

end
end OpenAI086.ReferenceV60
#print axioms OpenAI086.ReferenceV60.paper_powered_count_ref
#print axioms OpenAI086.ReferenceV60.four_paper_powered
#print axioms OpenAI086.ReferenceV60.three_paper_powered
#print axioms OpenAI086.ReferenceV60.four_paper_density
#print axioms OpenAI086.ReferenceV60.three_paper_density
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.four_core_final_side
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.SideInput.three_core_final_side
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.linear_energy
