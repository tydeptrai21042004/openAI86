/-
Adapted from TrilinearHT/Auto/Sec15_4VerificationCountingHypotheses.lean
Copyright (c) 2026 Joris Roos. Authors: Claude. Apache-2.0.
This wrapper uses the exact printed good predicate and the actual reference
pure-shift theorem; it does not assume the pure-shift gap.
-/
import ReferenceV70PaperTypes

namespace OpenAI086.ReferenceV70
open Auto MeasureTheory Metric
open scoped BigOperators FourierTransform ComplexConjugate ENNReal
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams} (D : fp.SideInput)

open Classical in
theorem paper_side_pure_gap {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) (I : ℤ × ℤ)
    (G : bf.Grp) (j : Fin 4) (z : ChartTag) (hz : (D.Ms j G).zc = z) (hdim : z.dim ≤ D.S.dmax)
    {h : ℕ} (hh : 10 ≤ h) (hhJ : h ≤ D.SP.Jst)
    {m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hgood : ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).PaperGood D.SP.Δ
      ((D.Ms j G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m)
    {μ ν : ℝ} (hμ : D.U0⁻¹ / 2 < μ) (hν : ν ≤ 8 * D.U0) (n : Fin z.dim → ℤ)
    (hn : ∀ k, |(n k : ℝ)| ≤ D.S.Eh h / ((6 ^ 8 : ℕ) : ℝ)) :
    |∑ k, (n k : ℝ) * zetaVec z D.S.Q0 h k| ∉
      Set.Icc (μ * (dyadicGridLength A.G I.1)⁻¹ / 1000)
        (1000 * ν * (dyadicGridLength A.G I.1)⁻¹) := by
  exact D.side_pure_gap hV hCA hCT hd2 hD hB hQ hSP I G j z hz hdim hh hhJ
    (Auto.ModeComponents.paperGood_to_good _ D.SP.Δ _ hgood) hμ hν n hn

end OpenAI086.ReferenceV70

#print axioms OpenAI086.ReferenceV70.paper_side_pure_gap

namespace OpenAI086.ReferenceV70
open Auto
open scoped BigOperators

/-- Section 9.1 for the actual printed core predicate. The roles can have
 different mode and primary types. First-success weights sum to one with
 the uniform success lower bound obtained from Lemma 8.4. -/
open Classical in
theorem paper_common_height {m₀ : ℕ} {M P : Fin m₀ → Type*}
    [∀ j, DecidableEq (M j)] [∀ j, DecidableEq (P j)]
    (C : ∀ j, ModeComponents (M j) (P j)) (Δ : ℕ)
    (goodP : ∀ j, ℕ → P j → Prop) [∀ j h, DecidablePred (goodP j h)]
    (m : ∀ j, M j) {J : ℕ} (hJ : 2 ≤ J) {δ : ℝ}
    (hδ : 0 < δ) (hδ16 : δ ≤ 1/16) (hsmall : 2*(m₀:ℝ)*δ < 1)
    (hcore : ∀ j, (C j).PaperCore Δ (goodP j) J δ (m j)) :
    let H := ModeComponents.upperHeights J δ
    let bad := fun j => (C j).paperBadHeights Δ (goodP j) J (m j)
    let p : ℝ := ((H.filter fun h => ∀ j, h ∉ bad j).card : ℝ) / H.card
    1-2*(m₀:ℝ)*δ ≤ p ∧ p ≤ 1 ∧ HasSum (fun n : ℕ => (1-p)^n*p) 1 := by
  classical
  dsimp only
  let H := ModeComponents.upperHeights J δ
  let bad := fun j => (C j).paperBadHeights Δ (goodP j) J (m j)
  have hJr : (2:ℝ) ≤ J := by exact_mod_cast hJ
  have hceil : (⌈4*δ*J⌉₊ : ℝ) < 4*δ*J+1 := Nat.ceil_lt_add_one (by positivity)
  have hc : ⌈4*δ*J⌉₊ ≤ J := by
    have hr : (⌈4*δ*J⌉₊ : ℝ) ≤ (J:ℝ) := by nlinarith
    exact_mod_cast hr
  have hH : 0 < H.card := Finset.card_pos.mpr ⟨J, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_self J), hc⟩⟩
  have hHr : (0:ℝ) < H.card := by exact_mod_cast hH
  have hb : ∀ j, ((bad j ∩ H).card:ℝ) ≤ 2*δ*H.card := fun j =>
    (C j).paper_core_bad_proportion Δ (goodP j) hJ hδ hδ16 (hcore j)
  have hall := Auto.all_good_proportion H bad hb
  let p : ℝ := ((H.filter fun h => ∀ j, h ∉ bad j).card:ℝ) / H.card
  have hlo : 1-2*(m₀:ℝ)*δ ≤ p := by
    apply (le_div_iff₀ hHr).mpr
    convert hall using 1 <;> ring
  have hhi : p ≤ 1 := by
    apply (div_le_iff₀ hHr).mpr
    rw [one_mul]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun h => ∀ j, h ∉ bad j) H)
  exact ⟨hlo, hhi, Auto.first_success_weights_sum (lt_of_lt_of_le (by linarith) hlo) hhi⟩

end OpenAI086.ReferenceV70
#print axioms OpenAI086.ReferenceV70.paper_common_height
