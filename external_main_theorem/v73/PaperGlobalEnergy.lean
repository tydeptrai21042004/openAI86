/-
Adapted from TrilinearHT/Auto/Sec13_3BesselRowsLinearSideEnergy.lean.
Copyright (c) 2026 Joris Roos; original authors: Claude. Apache-2.0.
V73 replaces the event family and chain length in the reference proof by
V71-V72's exact paper-specific definitions and Bessel-row estimates.
The analytic hypotheses and local normalization are unchanged.
Uncompiled proof candidates.
-/
import ReferenceV72PaperEventEnergy

namespace Auto
open MeasureTheory Metric OpenAI086.AdaptedV56
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc)

open Classical in
theorem paper_class_count (S : ModeSchedule) (hA : 6 ≤ S.A0) (SP : SideParams) (s : Finset Ms.Event)
    (hev : ∀ e ∈ s, e.2.2 ∈ Ms.paperSideEvents S hA SP e.1 e.2.1)
    (hdepth : ∀ e ∈ s, e.2.1.1 = e.1 - 2 * S.K) {L : ℕ}
    (hL : ∀ k e, LinkedChain (s : Set Ms.Event) (Ms.Linked S) k e → k ≤ L) (y : ℝ) :
    (s.filter fun e => y ∈ Ms.evCell e).card ≤ (L + 1) * (Ms.ptSet y).card := by
  set lev : Ms.Event → ℕ := chainLevel (s : Set Ms.Event) (Ms.Linked S) L
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  set t := s.filter fun e => y ∈ Ms.evCell e
  rw [Finset.card_eq_sum_card_fiberwise (f := lev) (t := Finset.range (L + 1))
    (fun e _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (chainLevel_le _ _ L e)))]
  calc ∑ ℓ ∈ Finset.range (L + 1), (t.filter fun e => lev e = ℓ).card ≤
      ∑ _ℓ ∈ Finset.range (L + 1), (Ms.ptSet y).card := Finset.sum_le_sum fun ℓ _ => ?_
    _ = (L + 1) * (Ms.ptSet y).card := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  -- the level set of the class
  set sl := s.filter fun e => lev e = ℓ
  have hsl : ∀ e ∈ t.filter (fun e => lev e = ℓ), e ∈ sl ∧ y ∈ Ms.evCell e := by
    intro e he
    obtain ⟨het, hl⟩ := Finset.mem_filter.mp he
    obtain ⟨he1, hy⟩ := Finset.mem_filter.mp het
    exact ⟨Finset.mem_filter.mpr ⟨he1, hl⟩, hy⟩
  have h3 : ∀ e ∈ sl, ∀ e' ∈ sl, e ≠ e' → e.1 = e'.1 → e.2.1 = e'.2.1 →
      Disjoint e.2.2 e'.2.2 ∧ ∀ m ∈ e.2.2, ∀ m' ∈ e'.2.2, ¬ Ms.pre0Edge S e.2.1 m m' := by
    intro e he e' he' hne hb hJ
    have he1 := (Finset.mem_filter.mp he).1
    have he1' := (Finset.mem_filter.mp he').1
    have hEne : e.2.2 ≠ e'.2.2 := fun h => hne (Prod.ext hb (Prod.ext hJ h))
    have h1 := hev e he1
    have h2 := hev e' he1'
    rw [← hb, ← hJ] at h2
    exact Ms.paperSideEvents_pair S hA SP (by rw [hdepth e he1]; omega) h1 h2 hEne
  have h4 : ∀ e ∈ sl, ∀ e' ∈ sl, ¬ Ms.Linked S e e' := by
    intro e he e' he' hlink
    have he1 := (Finset.mem_filter.mp he).1
    have he1' := (Finset.mem_filter.mp he').1
    have hlt := chainLevel_lt (s : Set Ms.Event) (Ms.Linked S) hL he1 he1' hlink
    have h1 := (Finset.mem_filter.mp he).2
    have h2 := (Finset.mem_filter.mp he').2
    simp only [lev] at h1 h2
    omega
  refine card_le_of_pairwiseDisjoint_subset _ (fun e => e.2.2) _ (fun e he => ?_)
    (fun e he m hm => ?_) (fun e he e' he' hne => ?_)
  · exact Ms.paperSideEvents_nonempty S hA SP (hev e (Finset.mem_filter.mp (hsl e he).1).1)
  · obtain ⟨hel, hy⟩ := hsl e he
    have he1 := (Finset.mem_filter.mp hel).1
    exact (Ms.mem_ptSet).mpr
      (Ms.paperSideEvents_alive S hA SP (by rw [hdepth e he1]; omega) (hev e he1) hm hy)
  · obtain ⟨hel, hy⟩ := hsl e he
    obtain ⟨hel', hy'⟩ := hsl e' he'
    obtain ⟨c, -, -, hdis, -⟩ := Ms.level_pair S (fun e he => hdepth e (Finset.mem_filter.mp he).1)
      h3 h4 hel hel' hne ⟨y, hy, hy'⟩
    exact hdis

open Classical in
theorem paper_group_count (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : S.Valid Cj CA CT CK δs W) (hCj : 340 ≤ Cj) (hCA : 1 ≤ CA) (hδs : 0 < δs)
    (hδ1 : δs ≤ 1) (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) (hQ : 1 ≤ S.Q0)
    (hDm : 2 ≤ S.Dm) (hW : 8 * ((S.dmax : ℝ) + 1) ^ 3 * Real.log (2 * S.H) / Real.log 2 ≤ W)
    (hdim : ∀ p, Ms.dvOf p + Ms.zc.dim ≤ S.dmax) {M : ℕ} (hM1 : 1 ≤ M)
    (hMD : (M : ℝ) ≤ 2 * S.Dm) (hM : ∀ U : ℤ × ℤ, ((Ms.alive U).image Ms.keyOf).card ≤ M)
    (R₀ : ℤ) (Bs : Finset ℤ) (cells : ℤ → Finset (ℤ × ℤ))
    (hdepth : ∀ b ∈ Bs, ∀ J ∈ cells b, J.1 = b - 2 * S.K)
    (hgrid : ∀ b ∈ Bs, (S.K : ℤ) ∣ b - R₀) (y : ℝ) :
    ((Ms.paperEvents S (hV.six_le_A0 hCA hd2 hD hB) (S.sideParams δs) Bs cells).filter
        fun e => y ∈ Ms.evCell e).card ≤
      3 * (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1) * (Ms.ptSet y).card := by
  have hA := hV.six_le_A0 hCA hd2 hD hB
  set SP := S.sideParams δs
  set ev := Ms.paperEvents S hA SP Bs cells
  set L := ⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊
  obtain ⟨κ, hκ⟩ := hV.K_dyadic
  have hK1 : 1 ≤ S.K := by rw [hκ]; exact Nat.one_le_two_pow
  rw [Finset.card_eq_sum_card_fiberwise (f := fun e => blockClass R₀ S.K e.1)
    (t := Finset.univ) (fun e _ => Finset.mem_univ _)]
  calc ∑ i : Fin 3, ((ev.filter fun e => y ∈ Ms.evCell e).filter
        fun e => blockClass R₀ S.K e.1 = i).card ≤
      ∑ _i : Fin 3, (L + 1) * (Ms.ptSet y).card := Finset.sum_le_sum fun i _ => ?_
    _ = 3 * (L + 1) * (Ms.ptSet y).card := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
  set! s := ev.filter (fun e => blockClass R₀ S.K e.1 = i)
  have hmem : ∀ e ∈ s, e.1 ∈ Bs ∧ e.2.1 ∈ cells e.1 ∧
      e.2.2 ∈ Ms.paperSideEvents S hA SP e.1 e.2.1 ∧ blockClass R₀ S.K e.1 = i := by
    intro e he
    obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
    exact ⟨(Ms.paper_mem_events S hA SP he1).1, (Ms.paper_mem_events S hA SP he1).2.1,
      (Ms.paper_mem_events S hA SP he1).2.2, he2⟩
  have hswap : (ev.filter fun e => y ∈ Ms.evCell e).filter
      (fun e => blockClass R₀ S.K e.1 = i) = s.filter fun e => y ∈ Ms.evCell e := by
    simp only [s, Finset.filter_filter, and_comm]
  rw [hswap]
  refine Ms.paper_class_count S hA SP s (fun e he => (hmem e he).2.2.1)
    (fun e he => hdepth e.1 (hmem e he).1 e.2.1 (hmem e he).2.1) ?_ y
  intro k e hc
  have hb := Ms.paper_chain_length_valid S hV hCA hCj hδs hδ1 hd2 hD hB hQ hDm hW hdim hM1 hMD
    hM R₀ s (fun e he => (hmem e he).2.2.1)
    (fun e he => hdepth e.1 (hmem e he).1 e.2.1 (hmem e he).2.1)
    (fun e he => hgrid e.1 (hmem e he).1)
    (fun e he e' he' hlt => blockClass_sep hK1 (hgrid e.1 (hmem e he).1)
      (hgrid e'.1 (hmem e' he').1) (((hmem e he).2.2.2).trans ((hmem e' he').2.2.2).symm)
      hlt) hc
  have hk : (k : ℝ) ≤ (2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs) := by
    push_cast at hb; linarith
  exact Nat.le_floor hk

end ModeSystem

open Classical in
theorem ModeSystem.paper_side_errors_negligible (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : S.Valid Cj CA CT CK δs W) (hCj : 340 ≤ Cj) (hCA : 1 ≤ CA) (hδs : 0 < δs)
    (hδ1 : δs ≤ 1) (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) (_hQ : 1 ≤ S.Q0)
    (hDm : 2 ≤ S.Dm) (hW : 8 * ((S.dmax : ℝ) + 1) ^ 3 * Real.log (2 * S.H) / Real.log 2 ≤ W)
    {Gd : RealDyadicGrid} {Mc : ℕ} {ι : Type*} [Fintype ι] (Ms : ι → ModeSystem Gd Mc) (q : ι → ℕ)
        (hq : ∀ G, 1 ≤ q G ∧ q G ≤ S.Q0)
    (hdim : ∀ G p, (Ms G).dvOf p + (Ms G).zc.dim ≤ S.dmax) {M : ℕ} (hM1 : 1 ≤ M)
    (hMD : (M : ℝ) ≤ 2 * S.Dm)
    (hM : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).image (Ms G).keyOf).card ≤ M)
    (R₀ : ℤ) (Bs : ι → Finset ℤ) (cells : ι → ℤ → Finset (ℤ × ℤ))
    (hdepth : ∀ G, ∀ b ∈ Bs G, ∀ J ∈ cells G b, J.1 = b - 2 * S.K)
    (hgrid : ∀ G, ∀ b ∈ Bs G, (S.K : ℤ) ∣ b - R₀) {R : ℤ × ℤ}
    (hcR : ∀ G, ∀ b ∈ Bs G, ∀ J ∈ cells G b, dyadicGridCell Gd J.1 J.2 ⊆ dyadicGridCell Gd R.1 R.2)
    (hδc : ∀ G, 0 < (Ms G).δc) (Kf : ℕ) (hDg : ∀ G, gaugeSqNorm (Ms G).zc.dim (Ms G).δc ≤ S.Dstar)
    (hKf : ∀ G, 2 * gaugeTail (Ms G).zc.dim (Ms G).δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (halive : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).card : ℝ) ≤ S.Dstar)
    (hpath : ∀ y, (∑ G, ((Ms G).ptSet y).card : ℝ) ≤ S.Dstar)
    (c : ∀ G, ℤ → ℤ × ℤ → (Ms G).Md → ℂ) {Bc : ℝ} (hBc : 0 ≤ Bc)
    (hc : ∀ G, ∀ b ∈ Bs G, ∀ J ∈ cells G b,
      ∑ m ∈ (Ms G).alive (ancAt Gd J (b - 4 * S.K)), ‖c G b J m‖ ^ 2 ≤ Bc) :
    (∀ G, ∀ b ∈ Bs G, ∀ J ∈ cells G b,
      ∀ E ∈ (Ms G).paperSideEvents (S.withQ0 (q G)) (hV.six_le_A0 hCA hd2 hD hB) (S.sideParams δs) b J,
        (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ b J E (c G b J) ^ 2 * S.Dstar ^ 397 ≤
          Bc * dyadicGridLength Gd J.1) ∧
    (∑ G, ∑ b ∈ Bs G, ∑ J ∈ cells G b,
      ∑ E ∈ (Ms G).paperSideEvents (S.withQ0 (q G)) (hV.six_le_A0 hCA hd2 hD hB) (S.sideParams δs) b J,
        (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ b J E (c G b J) ^ 2) * S.Dstar ^ 396 ≤
      3 * (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1) * Bc *
        dyadicGridLength Gd R.1 := by
  have hA := hV.six_le_A0 hCA hd2 hD hB
  set SP := S.sideParams δs
  set L := ⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊
  have hDp : 0 < S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ S.Dstar := by linarith
  have hΞ : 0 < S.Ξ := pow_pos hDp 1000
  -- the error of one event
  have hone : ∀ G, ∀ b ∈ Bs G, ∀ J ∈ cells G b, ∀ E ∈ (Ms G).paperSideEvents (S.withQ0 (q G)) hA SP b J,
      (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ b J E (c G b J) ^ 2 * S.Dstar ^ 397 ≤
        Bc * dyadicGridLength Gd J.1 := by
    intro G b hb J hJ E hE
    have hJu : b - 4 * S.K ≤ J.1 := by rw [hdepth G b hb J hJ]; omega
    have h := (Ms G).eventErr_sq_le (S.withQ0 (q G)) Kf (inv_pos.mpr hDp) b J E
      ((Ms G).paperSideEvents_subset_alive (S.withQ0 (q G)) hA SP hE) (c G b J) (halive G _) (hc G b hb
          J hJ)
    have hP := S.pairConst_mul_le hD (hDg G) (hKf G)
    have hP0 := pairConst_nonneg (Ms G).zc.dim (hδc G) hΞ Kf
    set P := pairConst (Ms G).zc.dim (Ms G).δc S.Ξ Kf
    have hr := dyadicGridLength_pos Gd J.1
    -- `P² D² B / D⁻¹ · D^397 = (P D^200)² B ≤ B`
    have e : P ^ 2 * dyadicGridLength Gd J.1 * S.Dstar ^ 2 * Bc / S.Dstar⁻¹ * S.Dstar ^ 397 =
        (P * S.Dstar ^ 200) ^ 2 * (Bc * dyadicGridLength Gd J.1) := by
      rw [div_inv_eq_mul]
      ring
    have hP2 : (P * S.Dstar ^ 200) ^ 2 ≤ 1 := by
      have : 0 ≤ P * S.Dstar ^ 200 := mul_nonneg hP0 (pow_nonneg hDp.le _)
      nlinarith only [hP, this]
    calc (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ b J E (c G b J) ^ 2 * S.Dstar ^ 397 ≤
        P ^ 2 * dyadicGridLength Gd J.1 * S.Dstar ^ 2 * Bc / S.Dstar⁻¹ * S.Dstar ^ 397 :=
          mul_le_mul_of_nonneg_right h (pow_nonneg hDp.le _)
      _ = (P * S.Dstar ^ 200) ^ 2 * (Bc * dyadicGridLength Gd J.1) := e
      _ ≤ 1 * (Bc * dyadicGridLength Gd J.1) :=
          mul_le_mul_of_nonneg_right hP2 (mul_nonneg hBc hr.le)
      _ = _ := one_mul _
  refine ⟨hone, ?_⟩
  -- the paperEvents through a point, across the groups (path budget)
  have hcount : ∀ y, ∑ G, (((Ms G).paperEvents (S.withQ0 (q G)) hA SP (Bs G) (cells G)).filter
      fun e => y ∈ (Ms G).evCell e).card ≤ 3 * (L + 1) * ⌊S.Dstar⌋₊ := by
    intro y
    have hfl : ∑ G, ((Ms G).ptSet y).card ≤ ⌊S.Dstar⌋₊ :=
      Nat.le_floor (by exact_mod_cast hpath y)
    calc ∑ G, (((Ms G).paperEvents (S.withQ0 (q G)) hA SP (Bs G) (cells G)).filter
          fun e => y ∈ (Ms G).evCell e).card ≤
        ∑ G, 3 * (L + 1) * ((Ms G).ptSet y).card := Finset.sum_le_sum fun G _ =>
          (Ms G).paper_group_count (S.withQ0 (q G)) (hV.withQ0 (by linarith) (by linarith) (hq G).2) hCj
              hCA hδs hδ1 hd2 hD hB
            (hq G).1 hDm hW (hdim G) hM1 hMD (hM G) R₀
            (Bs G) (cells G) (hdepth G) (hgrid G) y
      _ = 3 * (L + 1) * ∑ G, ((Ms G).ptSet y).card := (Finset.mul_sum _ _ _).symm
      _ ≤ 3 * (L + 1) * ⌊S.Dstar⌋₊ := Nat.mul_le_mul_left _ hfl
  have hpack := sum_sum_measureReal_le_of_count Finset.univ
    (fun G => (Ms G).paperEvents (S.withQ0 (q G)) hA SP (Bs G) (cells G)) (fun G (e : (Ms G).Event) =>
        (Ms G).evCell e)
    (fun G e => dyadicGridCell_measurable Gd _ _) (R := dyadicGridCell Gd R.1 R.2)
    (dyadicGridCell_volume_ne_top Gd R) (fun G _ e he => ?_) (N := 3 * (L + 1) * ⌊S.Dstar⌋₊)
    (fun y _ => hcount y)
  swap
  · obtain ⟨h1, h2, -⟩ := (Ms G).paper_mem_events (S.withQ0 (q G)) hA SP he
    exact hcR G e.1 h1 e.2.1 h2
  have hvol : ∀ G (e : (Ms G).Event), volume.real ((Ms G).evCell e) =
      dyadicGridLength Gd e.2.1.1 := fun G e => by
    rw [ModeSystem.evCell, measureReal_def, dyadicGridCell_volume,
      ENNReal.toReal_ofReal (dyadicGridLength_pos Gd _).le]
  -- the total as a sum over the paperEvents of each group
  have hsum : (∑ G, ∑ b ∈ Bs G, ∑ J ∈ cells G b, ∑ E ∈ (Ms G).paperSideEvents (S.withQ0 (q G)) hA SP b J,
      (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ b J E (c G b J) ^ 2) =
      ∑ G, ∑ e ∈ (Ms G).paperEvents (S.withQ0 (q G)) hA SP (Bs G) (cells G),
        (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ e.1 e.2.1 e.2.2 (c G e.1 e.2.1) ^ 2 :=
    Finset.sum_congr rfl fun G _ => ((Ms G).paper_sum_events (S.withQ0 (q G)) hA SP (Bs G) (cells G)
      fun e => (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ e.1 e.2.1 e.2.2 (c G e.1 e.2.1) ^
          2).symm
  rw [hsum]
  set X := ∑ G, ∑ e ∈ (Ms G).paperEvents (S.withQ0 (q G)) hA SP (Bs G) (cells G),
    (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ e.1 e.2.1 e.2.2 (c G e.1 e.2.1) ^ 2
  have h1 : X * S.Dstar ^ 397 ≤ Bc * ∑ G, ∑ e ∈ (Ms G).paperEvents (S.withQ0 (q G)) hA SP (Bs G)
      (cells G),
      volume.real ((Ms G).evCell e) := by
    simp only [X, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun G _ => Finset.sum_le_sum fun e he => ?_
    obtain ⟨h1, h2, h3⟩ := (Ms G).paper_mem_events (S.withQ0 (q G)) hA SP he
    rw [hvol]
    exact hone G e.1 h1 e.2.1 h2 e.2.2 h3
  have hN : ((3 * (L + 1) * ⌊S.Dstar⌋₊ : ℕ) : ℝ) ≤ 3 * (L + 1) * S.Dstar := by
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hDp.le) (by positivity)
  have hR := dyadicGridLength_pos Gd R.1
  rw [measureReal_def, dyadicGridCell_volume, ENNReal.toReal_ofReal hR.le] at hpack
  have h2 : X * S.Dstar ^ 396 * S.Dstar ≤
      3 * (L + 1) * Bc * dyadicGridLength Gd R.1 * S.Dstar := by
    calc X * S.Dstar ^ 396 * S.Dstar = X * S.Dstar ^ 397 := by ring
      _ ≤ Bc * (((3 * (L + 1) * ⌊S.Dstar⌋₊ : ℕ) : ℝ) * dyadicGridLength Gd R.1) :=
          h1.trans (mul_le_mul_of_nonneg_left hpack hBc)
      _ ≤ Bc * (3 * (L + 1) * S.Dstar * dyadicGridLength Gd R.1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN hR.le) hBc
      _ = 3 * (L + 1) * Bc * dyadicGridLength Gd R.1 * S.Dstar := by ring
  exact le_of_mul_le_mul_right h2 hDp

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
theorem paper_linear_energy (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) (hanc : A.AncClosed)
    {ι : Type*} [Fintype ι] (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k : ℕ)
    (hcol : ∀ G, (grp G).1 = k) {j : ℕ} (hj : j ≤ 4) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool))
    (S : ModeSchedule) {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : S.Valid Cj CA CT CK δs W)
    (hCj : 340 ≤ Cj) (hCA : 1 ≤ CA) (hδs : 0 < δs) (hδ1 : δs ≤ 1) (hd2 : 2 ≤ S.dmax)
    (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar) (hQ : 1 ≤ S.Q0) (hDm : 2 ≤ S.Dm)
    (hW : 8 * ((S.dmax : ℝ) + 1) ^ 3 * Real.log (2 * S.H) / Real.log 2 ≤ W)
    (D dB : ℕ) {H δc N kk : ℝ} (hHed : 2 ≤ fp.Hed) (hH : 1 ≤ H) (hδc : 0 < δc) (hN0 : 0 ≤ N)
    (hNl : ∀ I ∈ A.cells,
      ((mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤ N)
    {n : ℕ} (Ms : ι → ModeSystem A.G n) (q : ι → ℕ) (hq : ∀ G, 1 ≤ q G ∧ q G ≤ S.Q0) (L : ∀ G,
        LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms G).Md)
    (gs : ι → ℤ)
    (hex : ∀ G, fp.MainLiftExports l s (grp G) j d D dB H (gs G) (L G) (Ms G).wave (Ms G).cellOf)
    (hεM : ∀ G m, (L G).εM m = (Ms G).L.εM m)
    (hdim : ∀ G p, (Ms G).dvOf p + (Ms G).zc.dim ≤ S.dmax) {M : ℕ} (hM1 : 1 ≤ M)
    (hMD : (M : ℝ) ≤ 2 * S.Dm)
    (hM : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).image (Ms G).keyOf).card ≤ M)
    (hδ : ∀ G, 0 < (Ms G).δc) (hΛ : ∀ G, (Ms G).Λ ≤ S.Dstar) (Kf : ℕ)
    (hDg : ∀ G, gaugeSqNorm (Ms G).zc.dim (Ms G).δc ≤ S.Dstar)
    (hKf : ∀ G, 2 * gaugeTail (Ms G).zc.dim (Ms G).δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hBox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Bstar) (hεw : ∀ G m, S.Dstar⁻¹ ≤ (Ms G).L.εM m)
    (halive : ∀ G (U : ℤ × ℤ), (((Ms G).alive U).card : ℝ) ≤ S.Dstar)
    (hpath : ∀ y, (∑ G, ((Ms G).ptSet y).card : ℝ) ≤ S.Dstar)
    (hstar : fp.modeStar D dB H δc N kk ≤ S.Dstar)
    {CF : ℝ} (hCF : 0 ≤ CF)
    (hnorm : ∀ jb : Fin 2, ∀ U ∈ A.cells, ‖columnL2Restriction (dyadicGridCell A.G U.1 U.2)
      (dyadicGridCell_measurable A.G U.1 U.2) (bf.P l jb).Z‖ ^ 2 ≤ CF * dyadicGridLength A.G U.1)
    (R₀ : ℤ) (Bs : Finset ℤ) (hgrid : ∀ b ∈ Bs, (S.K : ℤ) ∣ b - R₀)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHτ : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {Nq : ℕ} (hNq : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ Nq)
    (hτN : τ * Nq * A.colBudget ^ 2 ≤ 1) (cc : ℕ) (hcc : 1 ≤ cc) {kq : ℝ} (hkq : 1 ≤ kq)
    (hDmq : Real.log (2 * mb.B) ≤ kq ^ cc) (hDb : Real.log (2 * A.colBudget) ≤ kq ^ cc)
    (hn : (ls.length : ℝ) ≤ cc * (Real.log kq + 1)) :
    ∃ c : ∀ G, ℤ → ℤ × ℤ → (Ms G).Md → ℂ,
      (∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
        (Ms G).frozenEval (S.withQ0 (q G)) b J (c G b J) = columnL2Restriction (dyadicGridCell A.G
            J.1 J.2)
          (dyadicGridCell_measurable A.G J.1 J.2)
          ((L G).op (fp.frozenZ l s mb (grp G) j ls (b - 4 * S.K)))) ∧
      (∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K,
        ∑ m ∈ (Ms G).alive (ancAt A.G J (b - 4 * S.K)), ‖c G b J m‖ ^ 2 ≤ 4 * S.Dstar ^ 2 * CF) ∧
      ∑ G, ∑ b ∈ Bs, ‖(Ms G).paperBlockSide (S.withQ0 (q G)) (hV.six_le_A0 hCA hd2 hD hB)
          (S.sideParams δs) b
          (fp.retainedV (grp G) b S.K) (c G b)‖ ^ 2 ≤
        24 * (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1) *
          (Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
              (1 + Real.log (2 * kq)) ^ 2) + 2 * CF / S.Dstar ^ 394) *
          dyadicGridLength A.G A.R.1 := by
  have hA := hV.six_le_A0 hCA hd2 hD hB
  have hK0 : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  have hDp : 0 < S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ S.Dstar := by linarith
  have hR0 : 0 < dyadicGridLength A.G A.R.1 := dyadicGridLength_pos A.G A.R.1
  -- the frozen coefficients
  have hcex : ∀ G (b : ℤ) (J : ℤ × ℤ), ∃ β : (Ms G).Md → ℂ, J ∈ fp.retainedV (grp G) b S.K →
      (Ms G).frozenEval (S.withQ0 (q G)) b J β = columnL2Restriction (dyadicGridCell A.G J.1 J.2)
          (dyadicGridCell_measurable A.G J.1 J.2)
          ((L G).op (fp.frozenZ l s mb (grp G) j ls (b - 4 * S.K))) ∧
        ∑ m ∈ (Ms G).alive (ancAt A.G J (b - 4 * S.K)), ‖β m‖ ^ 2 ≤
          4 * S.Dstar ^ 2 * CF := by
    intro G b J
    by_cases hJ : J ∈ fp.retainedV (grp G) b S.K
    · obtain ⟨β, h1, h2⟩ := fp.frozen_coeffs l s mb hanc (grp G) hj ls d D dB kk hHed hH hδc
        hN0 hNl (Ms G) (L G) (hex G) (hεM G) (S.withQ0 (q G)) hCF hstar hnorm hJ
      exact ⟨β, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hJ⟩
  choose c hc using hcex
  refine ⟨c, fun G b _ J hJ => (hc G b J hJ).1, fun G b _ J hJ => (hc G b J hJ).2, ?_⟩
  -- the span projections of the paperEvents
  have inst : ∀ G (J : ℤ × ℤ) (E : Finset (Ms G).Md),
      (Submodule.span ℂ (((Ms G).cellMode J) '' (E : Set (Ms G).Md))).HasOrthogonalProjection :=
    fun G J E => by
      have : FiniteDimensional ℂ
          (Submodule.span ℂ (((Ms G).cellMode J) '' (E : Set (Ms G).Md))) :=
        FiniteDimensional.span_of_finite ℂ (E.finite_toSet.image _)
      infer_instance
  have hdepth : ∀ G, ∀ b ∈ Bs, ∀ J ∈ fp.retainedV (grp G) b S.K, J.1 = b - 2 * S.K :=
    fun G b _ J hJ => ((fp.mem_retainedV).mp hJ).2.1
  -- the numerical side conditions of lem:mode-rows at the schedule
  have hΞ : 0 < S.Ξ := pow_pos hDp 1000
  have hΛ8 : ∀ G, 8 * (Ms G).Λ ≤ S.Ξ := by
    intro G
    have h1 : 8 * S.Dstar ≤ S.Dstar ^ 1000 := by
      have h4 : S.Dstar ^ 4 ≤ S.Dstar ^ 1000 := pow_le_pow_right₀ hD1 (by norm_num)
      have h3 : 8 * S.Dstar ≤ S.Dstar ^ 4 := by
        have : S.Dstar ^ 4 = S.Dstar * S.Dstar ^ 3 := by ring
        have h8 : (8 : ℝ) ≤ S.Dstar ^ 3 :=
          le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hD 3)
        nlinarith only [hD, h8]
      linarith
    have : 8 * (Ms G).Λ ≤ 8 * S.Dstar := by linarith [hΛ G]
    exact this.trans h1
  have hQ0 : 0 < S.Q0 := by omega
  have hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0 := by
    have hBA : S.Bstar ≤ S.A0 := by
      have hb := hV.base_le_A0 hCA hd2 hD hB
      have hC := hV.two_le_Cstar hd2 hD
      have h6 : (1 : ℝ) ≤ 6 ^ S.Rht := one_le_pow₀ (by norm_num)
      have h1 : 1 ≤ S.Cstar * 6 ^ S.Rht := one_le_mul_of_one_le_of_one_le (by linarith) h6
      have h2 : S.Bstar ≤ S.Cstar * 6 ^ S.Rht * S.Bstar :=
        le_mul_of_one_le_left (by linarith) h1
      have h3 : S.Cstar * 6 ^ S.Rht * S.Bstar ≤ S.Cstar * 6 ^ S.Rht * S.Bstar * S.Dstar :=
        le_mul_of_one_le_right (by positivity) hD1
      linarith
    have hE0 : S.Eh 0 = S.A0 := by unfold ModeSchedule.Eh; ring
    rw [hE0]; linarith
  have hε : 0 < S.Dstar⁻¹ := inv_pos.mpr hDp
  have hpt : ∀ G y, (((Ms G).ptSet y).card : ℝ) ≤ S.Dstar := fun G y =>
    (Finset.single_le_sum (f := fun G => (((Ms G).ptSet y).card : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ G)).trans (hpath y)
  have hpt2 : ∀ G y, (((Ms G).ptSet y).card : ℝ) ≤ S.Dstar⁻¹ * S.Dstar ^ 2 := fun G y => by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hDp.ne', one_mul]; exact hpt G y
  have hη : ∀ G, pairConst (Ms G).zc.dim (Ms G).δc S.Ξ Kf * S.Dstar ^ 3 ≤ 1 := fun G => by
    have h := S.pairConst_mul_le hD (hDg G) (hKf G)
    have h0 := pairConst_nonneg (Ms G).zc.dim (hδ G) hΞ Kf
    have h3 : S.Dstar ^ 3 ≤ S.Dstar ^ 200 := pow_le_pow_right₀ hD1 (by norm_num)
    exact (mul_le_mul_of_nonneg_left h3 h0).trans h
  -- the energy of each group: side paperEvents and their errors (`paper_group_side_energy`)
  have hgroup : ∀ G, ∑ b ∈ Bs, ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA (S.sideParams δs) b
      (fp.retainedV (grp G) b S.K) (c G b)‖ ^ 2 ≤
      4 * (∑ e ∈ ((Ms G).paperEvents (S.withQ0 (q G)) hA (S.sideParams δs) Bs
          fun b => fp.retainedV (grp G) b S.K).filter (fun e => A.R.1 ≤ e.1 - 4 * S.K),
        ‖(Submodule.span ℂ (((Ms G).cellMode e.2.1) '' (e.2.2 : Set (Ms G).Md))).starProjection
          ((L G).op (fp.basicOut l s mb (grp G) j ls (ancAt A.G e.2.1 (e.1 - 4 * S.K)).1))‖ ^ 2 +
        ∑ b ∈ Bs, ∑ J ∈ fp.retainedV (grp G) b S.K,
          ∑ E ∈ (Ms G).paperSideEvents (S.withQ0 (q G)) hA (S.sideParams δs) b J,
            (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ b J E (c G b J) ^ 2) := by
    intro G
    refine ((Ms G).paper_group_side_energy (S.withQ0 (q G)) hA (S.sideParams δs) Bs
      (fun b => fp.retainedV (grp G) b S.K) (hdepth G) (c G) (inst := inst G) (hδ G) (hΛ8 G)
      hΞ (lt_of_lt_of_le zero_lt_one (hq G).1) Kf
      (ModeSchedule.withQ0_box (hq G).2 (by positivity) hbox) hε (hεw G) hDp.le (hpt G) (hpt2
          G)).trans ?_
    have h4 : 2 * (1 + pairConst (Ms G).zc.dim (Ms G).δc S.Ξ Kf * S.Dstar ^ 3) ≤ 4 := by
      linarith [hη G]
    refine (mul_le_mul_of_nonneg_right h4 (Finset.sum_nonneg fun b _ =>
      Finset.sum_nonneg fun J _ => Finset.sum_nonneg fun E _ => by positivity)).trans
      (mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num))
    simp only [Finset.sum_add_distrib]
    congr 1
    -- the row outputs on the frozen evaluations are the lifted coarse outputs at `u_b`
    rw [← (Ms G).paper_sum_events (S.withQ0 (q G)) hA (S.sideParams δs) Bs (fun b => fp.retainedV (grp G)
        b S.K)
      fun e => ‖(Submodule.span ℂ (((Ms G).cellMode e.2.1) ''
          (e.2.2 : Set (Ms G).Md))).starProjection
        ((Ms G).frozenEval (S.withQ0 (q G)) e.1 e.2.1 (c G e.1 e.2.1))‖ ^ 2, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨hb, hJ, -⟩ := (Ms G).paper_mem_events (S.withQ0 (q G)) hA (S.sideParams δs) he
    rw [(hc G e.1 e.2.1 hJ).1, (Ms G).eventProj_restrict e.2.1 e.2.2 _ le_rfl]
    split_ifs with hR
    · have hz : fp.frozenZ l s mb (grp G) j ls (e.1 - 4 * S.K) =
          fp.basicOut l s mb (grp G) j ls (ancAt A.G e.2.1 (e.1 - 4 * S.K)).1 := by
        simp [frozenZ, not_lt.mpr hR, ancAt]
      rw [hz]
    · have hz : fp.frozenZ l s mb (grp G) j ls (e.1 - 4 * S.K) = 0 := by
        simp [frozenZ, not_le.mp hR]
      rw [hz, map_zero, map_zero, norm_zero]
      norm_num
  -- the row outputs: lem:lift-composition with the event rows of `paper_group_event_rows_schedule`
  have hrows := fp.lift_composition_dep l s hT htag d mb hne (ρ := fun G => (Ms G).Event) grp hgrp
    k j hPH ls (fun G => (Ms G).Md) L (fun G => ColumnL2 (Ms G).Md)
    (fun G => ((Ms G).paperEvents (S.withQ0 (q G)) hA (S.sideParams δs) Bs
      fun b => fp.retainedV (grp G) b S.K).filter (fun e => A.R.1 ≤ e.1 - 4 * S.K))
    (fun G e => (Submodule.span ℂ (((Ms G).cellMode e.2.1) ''
      (e.2.2 : Set (Ms G).Md))).starProjection)
    (c := 6 * (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1)) (by positivity)
    (fun G x => (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => sq_nonneg _).trans ((Ms G).paper_group_event_rows_schedule (S.withQ0 (q G)) (hV.withQ0
          (by linarith) (by linarith) (hq G).2) hCj hCA hδs
        hδ1 hd2 hD hB (hq G).1 hDm hW (hdim G) hM1 hMD (hM G) R₀ Bs (fun b => fp.retainedV (grp G)
            b S.K)
        (hdepth G) hgrid (hδ G) (hΛ G) Kf (hDg G) (hKf G)
        (ModeSchedule.withQ0_box (hq G).2 (by positivity) hBox) (hεw G) (hpt G)
        (inst := inst G) x))
    (fun G e => ancAt A.G e.2.1 (e.1 - 4 * S.K))
    (fun G e he => by
      obtain ⟨he1, hR⟩ := Finset.mem_filter.mp he
      exact (fp.retained_decision hanc ((Ms G).paper_mem_events (S.withQ0 (q G)) hA (S.sideParams δs)
          he1).2.1
        hR).2.1)
    (fun G e he => by
      obtain ⟨he1, hR⟩ := Finset.mem_filter.mp he
      have hJu := (fp.retained_decision hanc
        ((Ms G).paper_mem_events (S.withQ0 (q G)) hA (S.sideParams δs) he1).2.1 hR).1
      exact ContinuousLinearMap.ext fun w => (Ms G).eventProj_restrict e.2.1 e.2.2 _ hJu w)
    (fun G e he => by
      obtain ⟨he1, hR⟩ := Finset.mem_filter.mp he
      have h := (fp.retained_decision hanc
        ((Ms G).paper_mem_events (S.withQ0 (q G)) hA (S.sideParams δs) he1).2.1 hR).2.2
      rwa [hcol G] at h)
    hroot hτ hτ1 hHτ (N := Nq) ?_
  swap
  · convert hNq using 0
  have hG0 := fp.liftConst_le_G0 l s mb ls
    (c := 6 * (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ + 1)) (by positivity) hτ hτN cc hcc
    hkq hDmq hDb hn
  -- the negligible errors of the exact subtotals
  have herr := (ModeSystem.paper_side_errors_negligible S hV hCj hCA hδs hδ1 hd2 hD hB hQ hDm hW Ms q hq
      hdim
    hM1 hMD hM R₀ (fun _ => Bs) (fun G b => fp.retainedV (grp G) b S.K) hdepth (fun _ => hgrid)
    (R := A.R) (fun G b _ J hJ => ((dyadicFiniteTree_mem_iff A.G A.R J _).mp
      ((fp.mem_retainedV).mp hJ).1).1) hδ Kf hDg hKf halive hpath c
    (Bc := 4 * S.Dstar ^ 2 * CF) (by positivity) fun G b _ J hJ => (hc G b J hJ).2).2
  -- combine
  set Lc : ℝ := (⌊(2 * ((v57FloorLog M : ℝ) + ((4 * S.dmax : ℕ) : ℝ) * (harmonic M : ℝ) / (1/10)) / δs)⌋₊ : ℝ) + 1 with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  set G0 := Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
    (1 + Real.log (2 * kq)) ^ 2)
  set X := ∑ G, ∑ e ∈ ((Ms G).paperEvents (S.withQ0 (q G)) hA (S.sideParams δs) Bs
      fun b => fp.retainedV (grp G) b S.K).filter (fun e => A.R.1 ≤ e.1 - 4 * S.K),
    ‖(Submodule.span ℂ (((Ms G).cellMode e.2.1) '' (e.2.2 : Set (Ms G).Md))).starProjection
      ((L G).op (fp.basicOut l s mb (grp G) j ls (ancAt A.G e.2.1 (e.1 - 4 * S.K)).1))‖ ^ 2
  set Y := ∑ G, ∑ b ∈ Bs, ∑ J ∈ fp.retainedV (grp G) b S.K,
    ∑ E ∈ (Ms G).paperSideEvents (S.withQ0 (q G)) hA (S.sideParams δs) b J,
      (Ms G).eventErr (S.withQ0 (q G)) Kf S.Dstar⁻¹ b J E (c G b J) ^ 2
  have hX : X ≤ 6 * Lc * G0 * dyadicGridLength A.G A.R.1 :=
    hrows.trans (mul_le_mul_of_nonneg_right hG0 hR0.le)
  have hY : Y * S.Dstar ^ 394 ≤ 12 * Lc * CF * dyadicGridLength A.G A.R.1 := by
    have hD2 : 0 < S.Dstar ^ 2 := by positivity
    have e1 : Y * S.Dstar ^ 396 = Y * S.Dstar ^ 394 * S.Dstar ^ 2 := by ring
    have e2 : 3 * Lc * (4 * S.Dstar ^ 2 * CF) * dyadicGridLength A.G A.R.1 =
        12 * Lc * CF * dyadicGridLength A.G A.R.1 * S.Dstar ^ 2 := by ring
    have h := herr
    rw [e1, e2] at h
    exact le_of_mul_le_mul_right h hD2
  have hY' : Y ≤ 12 * Lc * CF * dyadicGridLength A.G A.R.1 / S.Dstar ^ 394 := by
    rw [le_div_iff₀ (by positivity)]; exact hY
  calc ∑ G, ∑ b ∈ Bs, ‖(Ms G).paperBlockSide (S.withQ0 (q G)) hA (S.sideParams δs) b
        (fp.retainedV (grp G) b S.K) (c G b)‖ ^ 2 ≤ 4 * (X + Y) := by
        refine (Finset.sum_le_sum fun G _ => hgroup G).trans (le_of_eq ?_)
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 4 * (6 * Lc * G0 * dyadicGridLength A.G A.R.1 +
        12 * Lc * CF * dyadicGridLength A.G A.R.1 / S.Dstar ^ 394) := by gcongr
    _ = 24 * Lc * (G0 + 2 * CF / S.Dstar ^ 394) * dyadicGridLength A.G A.R.1 := by ring

end ActiveSetup.BasicFamilies.FamParams
end Auto

#print axioms Auto.ModeSystem.paper_class_count
#print axioms Auto.ModeSystem.paper_group_count
#print axioms Auto.ModeSystem.paper_side_errors_negligible
#print axioms Auto.ActiveSetup.BasicFamilies.FamParams.paper_linear_energy
