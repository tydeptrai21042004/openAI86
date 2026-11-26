/-
Adapted from the pinned Joris Roos reference, TrilinearHT/Auto/
Sec13_5RepresentativesComponentSizesFirstTops.lean and
Sec13_4SideStatesFixedOffsets.lean. Copyright (c) 2026 Joris Roos;
original authors: Claude. Apache-2.0. See LICENSE-REFERENCE-APACHE2.
V75 replaces the reference side/core and logarithmic type predicates
consistently. Proof candidates; no Lean elaboration was performed.
-/
import ReferenceV73PaperGlobalEnergy
import ReferenceV72PaperLocalForms
import TrilinearHT.Auto.Sec13_5RepresentativesComponentSizesFirstTops

set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace Auto
open MeasureTheory Metric OpenAI086.AdaptedV56 OpenAI086.ReferenceV70
open scoped FourierTransform ComplexConjugate ENNReal BigOperators
namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)
open Classical in
/-- A core mode of the block `b` on the pre-cell `J`: alive at the decision cell and with at most
`δ_* (J_* + 1)` bad heights (line 2037). -/
def paperIsCoreAt (b : ℤ) (J : ℤ × ℤ) (m : Ms.Md) : Prop :=
  ∃ hm : m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)),
    (Ms.blockComps S hA b J).PaperCore SP.Δ (Ms.goodP S SP b) SP.Jst SP.δs ⟨m, hm⟩

open Classical in
/-- Blueprint `eq:component-size` (lines 2196-2201) on the actual cell `I`:
`σ_F² = Σ_{D ⊆ F} (‖A_D‖_{2,I} + D_*^{-30} Σ_{m core in D} |α_m|)²` over the minimal CURRENT
components `D` of `F = F_h(x)`, with the full core subtotals `A_D = Σ_{m core in D} α_m Ψ_{I,m}` and
the normalized norm `‖f‖_{2,I} = |I|^{-1/2} ‖1_I f‖₂`. -/
noncomputable def paperCompSizeSq (I : ℤ × ℤ) (b : ℤ) (J : ℤ × ℤ) (h : ℕ)
    (x : Ms.alive (ancAt Gd J (b - 4 * S.K))) (c : Ms.Md → ℂ) : ℝ :=
  ∑ D ∈ Ms.minComps S hA b J h x,
    (‖∑ m ∈ D.filter (Ms.paperIsCoreAt S hA SP b J), c m • Ms.cellMode I m‖ /
        Real.sqrt (dyadicGridLength Gd I.1) +
      (S.Dstar ^ 30)⁻¹ * ∑ m ∈ D.filter (Ms.paperIsCoreAt S hA SP b J), ‖c m‖) ^ 2
open Classical in
/-- Blueprint `eq:size-comparison` (lines 2202-2209), first assertion, at an actual cell `I` of
length at least `r_{t_b}` inside the pre-cell `J` of the block `b`, for the CURRENT component
`F = F_h(x)`: with the frozen coefficients `c` of `Z̃_{l,G,b}` on `J` (square sum at most `B_c` over
the alive modes; `B_c = 4 D_*² C_F` by `frozen_coeffs`),
`σ_F² ≤ 12 (‖P_{F,I} Z̃‖²_{2,I} + ‖V_F‖²_{2,I}) + 3 B_c D_*^{-59}`, where `P_{F,I}` projects onto
the modes of `F` on `I` and `V_F` is the exact linear-side subtotal of `F` on `I`.

Proof as in the blueprint: the core subtotals of distinct minimal CURRENT components are almost
orthogonal (`actualCell_inner_le`, cross pairings `≤ 2 D_*^{-200} |I|`), so
`Σ_D ‖A_D‖² ≤ 2 ‖T_F - V_F‖²`; the coefficient floors cost at most `D_*^{-59} B_c`; and pairing the
complementary modes against the range of `P_{F,I}` gives
`‖P_{F,I} Z̃ - T_F‖² ≤ 4 D_*^{-397} B_c |I|`
(`projection_subtotal_close`). The schedule enters through `Ξ = D_*^{1000}`, `Λ ≤ D_*`, the Fourier
norm and tail of the squared gauge, the inverse private weights at most `D_*` and at most `D_*`
alive modes (line 2055). -/
theorem paper_size_comparison {b : ℤ} {J I : ℤ × ℤ} (hJ : J.1 = b - 2 * S.K)
    (hIJ : dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd J.1 J.2) (hIt : I.1 ≤ b + S.K)
    (hD : 2 ≤ S.Dstar) (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m)
    (halive : ((Ms.alive (ancAt Gd J (b - 4 * S.K))).card : ℝ) ≤ S.Dstar)
    (c : Ms.Md → ℂ) {Bc : ℝ}
    (hc : ∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), ‖c m‖ ^ 2 ≤ Bc)
    (h : ℕ) (x : Ms.alive (ancAt Gd J (b - 4 * S.K)))
    [(Submodule.span ℂ ((Ms.cellMode I) ''
      (Ms.compModes S hA b J h x : Set Ms.Md))).HasOrthogonalProjection] :
    Ms.paperCompSizeSq S hA SP I b J h x c ≤
      12 * ((‖(Submodule.span ℂ ((Ms.cellMode I) ''
          (Ms.compModes S hA b J h x : Set Ms.Md))).starProjection (Ms.frozenEval S b J c)‖ ^ 2 +
        ‖∑ m ∈ (Ms.compModes S hA b J h x).filter (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m),
          c m • Ms.cellMode I m‖ ^ 2) / dyadicGridLength Gd I.1) + 3 * Bc / S.Dstar ^ 59 := by
  have hDp : 0 < S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ S.Dstar := by linarith
  have hΞ : 0 < S.Ξ := pow_pos hDp 1000
  have hΛ16 := Ms.sixteen_Λ_le S hD hΛ
  have hr : 0 < dyadicGridLength Gd I.1 := dyadicGridLength_pos Gd I.1
  have hε : 0 < S.Dstar⁻¹ := inv_pos.mpr hDp
  obtain ⟨η, hηe⟩ : ∃ η, η = pairConst Ms.zc.dim Ms.δc (S.Ξ / 2) Kf := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hηe]; exact pairConst_nonneg _ hδ (by linarith) Kf
  have hη200 : η * S.Dstar ^ 200 ≤ 2 := by rw [hηe]; exact S.pairConst_half_mul_le hD hδ hDg hKf
  have hBc : 0 ≤ Bc := le_trans (Finset.sum_nonneg fun _ _ => sq_nonneg _) hc
  obtain ⟨hηD, hη2⟩ := eta_sched_bounds hD hη0 hη200 hBc
  have hFal := Ms.compModes_subset_alive S hA b J h x
  -- pairings of modes in different minimal CURRENT components
  have hpairA : ∀ a a' : Ms.alive (ancAt Gd J (b - 4 * S.K)),
      a' ∉ (Ms.blockComps S hA b J).F 0 a →
      ‖inner ℂ (Ms.cellMode I a.1) (Ms.cellMode I a'.1)‖ ≤ η * dyadicGridLength Gd I.1 :=
    fun a a' h0 => by
      rw [hηe]; exact Ms.actualCell_inner_le S hA hJ hIJ hIt hδ hΛ16 hΞ hQ0 Kf hbox h0
  -- the projected frozen evaluation on `I`
  have hres : columnL2Restriction (dyadicGridCell Gd I.1 I.2)
      (dyadicGridCell_measurable Gd I.1 I.2) (Ms.frozenEval S b J c) =
      ∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), c m • Ms.cellMode I m := by
    unfold frozenEval
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, Ms.cellMode_restrict hIJ]
  have hPZ := Ms.eventProj_restrict I (Ms.compModes S hA b J h x)
    (dyadicGridCell_measurable Gd I.1 I.2) le_rfl (Ms.frozenEval S b J c)
  rw [hres] at hPZ
  rw [← hPZ]
  -- the complementary pairing error
  have hclose := projection_subtotal_close (Ms.compModes S hA b J h x)
    (Ms.alive (ancAt Gd J (b - 4 * S.K))) hFal (Ms.cellMode I) c (η := η)
    (L := dyadicGridLength Gd I.1) (ε := S.Dstar⁻¹) (ℓ := dyadicGridLength Gd I.1)
    (mul_nonneg hη0 hr.le) (mul_pos hε hr) (fun m hm m' hm' => ?_)
    (fun c' => Ms.cellMode_synthesis_ge I _ c' hε.le hεw)
  swap
  · obtain ⟨y, hy, rfl⟩ := (Ms.mem_compModes S hA).mp hm
    obtain ⟨hm'al, hm'F⟩ := Finset.mem_sdiff.mp hm'
    refine hpairA y ⟨m', hm'al⟩ fun h0 => hm'F ((Ms.mem_compModes S hA).mpr ⟨⟨m', hm'al⟩, ?_, rfl⟩)
    have := (Ms.blockComps S hA b J).F_mono 0 h y (Nat.zero_le _) h0
    rwa [(Ms.blockComps S hA b J).F_comp h x y hy] at this
  obtain ⟨εc, hεce⟩ : ∃ εc, εc = η * dyadicGridLength Gd I.1 *
      (Real.sqrt (Ms.compModes S hA b J h x).card *
        (Real.sqrt (Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x).card *
          Real.sqrt (∑ m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x,
            ‖c m'‖ ^ 2))) / Real.sqrt (S.Dstar⁻¹ * dyadicGridLength Gd I.1) := ⟨_, rfl⟩
  rw [← hεce] at hclose
  have hεc0 : 0 ≤ εc := by rw [hεce]; positivity
  have hεc2 : εc ^ 2 ≤ η ^ 2 * S.Dstar ^ 3 * Bc * dyadicGridLength Gd I.1 := by
    have hFc : ((Ms.compModes S hA b J h x).card : ℝ) ≤ S.Dstar :=
      le_trans (by exact_mod_cast Finset.card_le_card hFal) halive
    have hGc : ((Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x).card : ℝ) ≤
        S.Dstar := le_trans (by exact_mod_cast Finset.card_le_card Finset.sdiff_subset) halive
    have hS0 : 0 ≤ ∑ m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x,
        ‖c m'‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hSB : ∑ m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x,
        ‖c m'‖ ^ 2 ≤ Bc := le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          fun _ _ _ => sq_nonneg _) hc
    have e : εc ^ 2 = η ^ 2 * dyadicGridLength Gd I.1 * S.Dstar *
        ((Ms.compModes S hA b J h x).card *
          ((Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x).card *
            ∑ m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x,
              ‖c m'‖ ^ 2)) := by
      rw [hεce, div_pow, mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _),
        Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hS0, Real.sq_sqrt (by positivity)]
      field_simp
    rw [e]
    have h1 : ((Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x).card : ℝ) *
        ∑ m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x, ‖c m'‖ ^ 2 ≤
        S.Dstar * Bc := mul_le_mul hGc hSB hS0 hDp.le
    have h2 : ((Ms.compModes S hA b J h x).card : ℝ) *
        (((Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x).card : ℝ) *
          ∑ m' ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)) \ Ms.compModes S hA b J h x, ‖c m'‖ ^ 2) ≤
        S.Dstar * (S.Dstar * Bc) := mul_le_mul hFc h1 (by positivity) hDp.le
    have h3 : 0 ≤ η ^ 2 * dyadicGridLength Gd I.1 * S.Dstar := by positivity
    calc _ ≤ η ^ 2 * dyadicGridLength Gd I.1 * S.Dstar * (S.Dstar * (S.Dstar * Bc)) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = η ^ 2 * S.Dstar ^ 3 * Bc * dyadicGridLength Gd I.1 := by ring
  -- the decomposition of the core part into minimal CURRENT components
  have hdis : ∀ D ∈ Ms.minComps S hA b J h x, ∀ D' ∈ Ms.minComps S hA b J h x, D ≠ D' →
      Disjoint D D' := by
    intro D hD D' hD' hne
    obtain ⟨y, -, rfl⟩ := (Ms.mem_minComps S hA).mp hD
    obtain ⟨y', -, rfl⟩ := (Ms.mem_minComps S hA).mp hD'
    exact (Ms.comp_eq_or_disjoint S hA b J 0 y y').resolve_left hne
  have hT : ∑ m ∈ Ms.compModes S hA b J h x, c m • Ms.cellMode I m -
      ∑ m ∈ (Ms.compModes S hA b J h x).filter (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m),
        c m • Ms.cellMode I m =
      ∑ D ∈ Ms.minComps S hA b J h x, ∑ m ∈ D.filter (Ms.paperIsCoreAt S hA SP b J),
        c m • Ms.cellMode I m := by
    rw [sum_filter_disjoint_family _ hdis, Ms.biUnion_minComps S hA b J h x,
      ← Finset.sum_filter_add_sum_filter_not (Ms.compModes S hA b J h x)
        (Ms.paperIsCoreAt S hA SP b J), add_sub_cancel_right]
  -- the floors
  obtain ⟨y, hye⟩ : ∃ y : Finset Ms.Md → ℝ, y = fun D => (S.Dstar ^ 30)⁻¹ *
      (∑ m ∈ D.filter (Ms.paperIsCoreAt S hA SP b J), ‖c m‖) * Real.sqrt (dyadicGridLength Gd I.1) :=
    ⟨_, rfl⟩
  have hy : ∑ D ∈ Ms.minComps S hA b J h x, y D ^ 2 ≤
      Bc * dyadicGridLength Gd I.1 / S.Dstar ^ 59 := by
    have hsq : ∀ D, y D ^ 2 = ((S.Dstar ^ 30)⁻¹) ^ 2 * dyadicGridLength Gd I.1 *
        (∑ m ∈ D.filter (Ms.paperIsCoreAt S hA SP b J), ‖c m‖) ^ 2 := fun D => by
      rw [hye]; simp only; rw [mul_pow, mul_pow, Real.sq_sqrt hr.le]; ring
    simp only [hsq]
    rw [← Finset.mul_sum]
    have hsum : ∑ D ∈ Ms.minComps S hA b J h x,
        (∑ m ∈ D.filter (Ms.paperIsCoreAt S hA SP b J), ‖c m‖) ^ 2 ≤ S.Dstar * Bc := by
      refine (Finset.sum_sq_le_sq_sum_of_nonneg fun D _ =>
        Finset.sum_nonneg fun _ _ => norm_nonneg _).trans ?_
      rw [sum_filter_disjoint_family _ hdis, Ms.biUnion_minComps S hA b J h x]
      have h1 : ∑ m ∈ (Ms.compModes S hA b J h x).filter (Ms.paperIsCoreAt S hA SP b J), ‖c m‖ ≤
          ∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), ‖c m‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg ((Finset.filter_subset _ _).trans hFal)
          fun _ _ _ => norm_nonneg _
      have h2 := sq_sum_le_card_mul_sum_sq (s := Ms.alive (ancAt Gd J (b - 4 * S.K)))
        (f := fun m => ‖c m‖)
      have hS0 : 0 ≤ ∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), ‖c m‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc (∑ m ∈ (Ms.compModes S hA b J h x).filter (Ms.paperIsCoreAt S hA SP b J), ‖c m‖) ^ 2
          ≤ (∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), ‖c m‖) ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) h1 2
        _ ≤ (Ms.alive (ancAt Gd J (b - 4 * S.K))).card *
            ∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), ‖c m‖ ^ 2 := h2
        _ ≤ S.Dstar * Bc := mul_le_mul halive hc hS0 hDp.le
    have hk : ((S.Dstar ^ 30)⁻¹) ^ 2 * dyadicGridLength Gd I.1 * (S.Dstar * Bc) =
        Bc * dyadicGridLength Gd I.1 / S.Dstar ^ 59 := by
      field_simp
    rw [← hk]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  have hcs := component_sizes (Ms.minComps S hA b J h x)
    (fun D => D.filter (Ms.paperIsCoreAt S hA SP b J)) (Ms.cellMode I) c hη0 hr.le hε hDp.le
    (fun D hD D' hD' hne m hm m' hm' => ?_)
    (fun D _ => Ms.cellMode_synthesis_ge I _ c hε.le hεw)
    (le_trans (by exact_mod_cast Ms.card_minComps_le S hA b J h x) halive)
    (fun D hD => ?_) hηD y hy hεc0 hT hclose
  rotate_left
  · obtain ⟨y1, -, rfl⟩ := (Ms.mem_minComps S hA).mp hD
    obtain ⟨y2, -, rfl⟩ := (Ms.mem_minComps S hA).mp hD'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hm).1
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hm').1
    exact hpairA a a' (Ms.not_mem_F_of_ne S hA b J 0 hne ha ha')
  · have hsub : D.filter (Ms.paperIsCoreAt S hA SP b J) ⊆ Ms.alive (ancAt Gd J (b - 4 * S.K)) :=
      (Finset.filter_subset _ _).trans (Ms.minComps_subset_alive S hA hD)
    have hc1 : ((D.filter (Ms.paperIsCoreAt S hA SP b J)).card : ℝ) ≤ S.Dstar :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) halive
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hDp.ne', one_mul]
    exact hc1
  -- normalize
  have hsizes : Ms.paperCompSizeSq S hA SP I b J h x c * dyadicGridLength Gd I.1 =
      ∑ D ∈ Ms.minComps S hA b J h x,
        (‖∑ m ∈ D.filter (Ms.paperIsCoreAt S hA SP b J), c m • Ms.cellMode I m‖ + y D) ^ 2 := by
    unfold paperCompSizeSq
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun D _ => ?_
    rw [hye]
    simp only
    rw [sq_div_sqrt_add_mul _ _ hr]
  have hεr : 12 * εc ^ 2 ≤ Bc / S.Dstar ^ 59 * dyadicGridLength Gd I.1 := by
    calc 12 * εc ^ 2 ≤ 12 * (η ^ 2 * S.Dstar ^ 3 * Bc * dyadicGridLength Gd I.1) :=
          mul_le_mul_of_nonneg_left hεc2 (by norm_num)
      _ = 12 * (η ^ 2 * S.Dstar ^ 3 * Bc) * dyadicGridLength Gd I.1 := by ring
      _ ≤ Bc / S.Dstar ^ 59 * dyadicGridLength Gd I.1 :=
          mul_le_mul_of_nonneg_right hη2 hr.le
  rw [← hsizes] at hcs
  exact size_final_arith hr hcs hεr
open Classical in
/-- Blueprint `eq:size-comparison` (lines 2202-2209), second assertion ("decomposing `V` into all
height-`h` CURRENT components and discarding unsuccessful ones"): on an actual cell `I` of length
at least `r_{t_b}` inside the pre-cell `J` of the block `b`, for any family `Fs` of CURRENT
components at height `h`, the exact side subtotals satisfy `Σ_{F ∈ Fs} ‖V_F‖² ≤ 2 ‖V‖²`, where
`V = Σ_{m alive, side} α_m Ψ_{I,m}` is the linear side on `I`. -/
theorem paper_side_comparison {b : ℤ} {J I : ℤ × ℤ} (hJ : J.1 = b - 2 * S.K)
    (hIJ : dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd J.1 J.2) (hIt : I.1 ≤ b + S.K)
    (hD : 2 ≤ S.Dstar) (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m)
    (halive : ((Ms.alive (ancAt Gd J (b - 4 * S.K))).card : ℝ) ≤ S.Dstar)
    (c : Ms.Md → ℂ) (h : ℕ) {Fs : Finset (Finset Ms.Md)} (hFs : Fs ⊆ Ms.curComps S hA b J h) :
    ∑ F ∈ Fs, ‖∑ m ∈ F.filter (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m), c m • Ms.cellMode I m‖ ^ 2 ≤
      2 * ‖∑ m ∈ (Ms.alive (ancAt Gd J (b - 4 * S.K))).filter
        (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m), c m • Ms.cellMode I m‖ ^ 2 := by
  have hDp : 0 < S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ S.Dstar := by linarith
  have hΞ : 0 < S.Ξ := pow_pos hDp 1000
  have hΛ16 := Ms.sixteen_Λ_le S hD hΛ
  have hr : 0 < dyadicGridLength Gd I.1 := dyadicGridLength_pos Gd I.1
  have hε : 0 < S.Dstar⁻¹ := inv_pos.mpr hDp
  obtain ⟨η, hηe⟩ : ∃ η, η = pairConst Ms.zc.dim Ms.δc (S.Ξ / 2) Kf := ⟨_, rfl⟩
  have hη0 : 0 ≤ η := by rw [hηe]; exact pairConst_nonneg _ hδ (by linarith) Kf
  have hη200 : η * S.Dstar ^ 200 ≤ 2 := by rw [hηe]; exact S.pairConst_half_mul_le hD hδ hDg hKf
  have hηD := (eta_sched_bounds hD hη0 hη200 le_rfl).1
  have hdis : ∀ F ∈ Ms.curComps S hA b J h, ∀ F' ∈ Ms.curComps S hA b J h, F ≠ F' →
      Disjoint F F' := by
    intro F hF F' hF' hne
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨y', -, rfl⟩ := Finset.mem_image.mp hF'
    exact (Ms.comp_eq_or_disjoint S hA b J h y y').resolve_left hne
  have hcover : (Ms.curComps S hA b J h).biUnion id = Ms.alive (ancAt Gd J (b - 4 * S.K)) := by
    ext m
    simp only [Finset.mem_biUnion, id]
    constructor
    · rintro ⟨F, hF, hmF⟩
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hmF
      exact a.2
    · intro hm
      refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨m, hm⟩), Finset.mem_map.mpr
        ⟨⟨m, hm⟩, (Ms.blockComps S hA b J).E_le_F h _ ((Ms.blockComps S hA b J).E_self h _), rfl⟩⟩
  have hsub := side_subtotals_le (Ms.curComps S hA b J h)
    (fun F => F.filter (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m)) (Ms.cellMode I) c hη0 hr.le hε
    hDp.le (fun F hF F' hF' hne m hm m' hm' => ?_)
    (fun F _ => Ms.cellMode_synthesis_ge I _ c hε.le hεw) ?_ (fun F hF => ?_) hηD
  rotate_left
  · obtain ⟨y1, -, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨y2, -, rfl⟩ := Finset.mem_image.mp hF'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hm).1
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp (Finset.mem_filter.mp hm').1
    have h0 : a' ∉ (Ms.blockComps S hA b J).F 0 a := fun h0 =>
      Ms.not_mem_F_of_ne S hA b J h hne ha ha'
        ((Ms.blockComps S hA b J).F_mono 0 h a (Nat.zero_le _) h0)
    rw [hηe]; exact Ms.actualCell_inner_le S hA hJ hIJ hIt hδ hΛ16 hΞ hQ0 Kf hbox h0
  · refine le_trans ?_ halive
    unfold curComps
    exact_mod_cast Finset.card_image_le.trans ((Finset.card_le_univ _).trans
      (le_of_eq (Fintype.card_coe _)))
  · have hFal : F ⊆ Ms.alive (ancAt Gd J (b - 4 * S.K)) := by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hF
      intro m hm
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hm
      exact a.2
    have hsub : F.filter (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m) ⊆
        Ms.alive (ancAt Gd J (b - 4 * S.K)) := (Finset.filter_subset _ _).trans hFal
    have hc1 : ((F.filter (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m)).card : ℝ) ≤ S.Dstar :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) halive
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hDp.ne', one_mul]
    exact hc1
  rw [sum_filter_disjoint_family _ hdis, hcover] at hsub
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hFs fun _ _ _ => sq_nonneg _) hsub
open Classical in
/-- The side events of a pre-cell partition its side modes (blueprint line 2084, "it is entirely
side by the predicate coherence", `paper_core_minimal_pre`). -/
theorem paper_sum_sideEvents_eq {b : ℤ} {J : ℤ × ℤ} (hJ : J.1 ≤ b + S.K) {M : Type*}
    [AddCommMonoid M] (f : Ms.Md → M) :
    ∑ E ∈ Ms.paperSideEvents S hA SP b J, ∑ m ∈ E, f m =
      ∑ m ∈ (Ms.alive (ancAt Gd J (b - 4 * S.K))).filter
        (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m), f m := by
  have hsum := Finset.sum_biUnion (s := Ms.paperSideEvents S hA SP b J) (t := id) (f := f)
    (fun E hE E' hE' hne => (Ms.paperSideEvents_pair S hA SP hJ hE hE' hne).1)
  simp only [id] at hsum
  rw [← hsum]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [Finset.mem_biUnion, Finset.mem_filter, id]
  constructor
  · rintro ⟨E, hE, hmE⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hmE
    refine ⟨y.2, fun ⟨hm, hcore⟩ => ?_⟩
    have hx' : ¬ (Ms.blockComps S hA b J).PaperCore SP.Δ (Ms.goodP S SP b) SP.Jst SP.δs x := by
      unfold paperSideModes at hx
      exact (Finset.mem_filter.mp hx).2
    apply hx'
    exact ((Ms.blockComps S hA b J).paper_core_minimal_pre SP.Δ (Ms.goodP S SP b) SP.Jst
      SP.δs hy).mpr hcore
  · rintro ⟨hm, hnc⟩
    refine ⟨_, Finset.mem_image_of_mem _ ?_,
      Finset.mem_map.mpr ⟨⟨m, hm⟩, ModeComponents.E_self _ 0 _, rfl⟩⟩
    unfold paperSideModes
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hc => hnc ⟨hm, hc⟩⟩

open Classical in
theorem paper_restrict_blockSide {b : ℤ} {cells : Finset (ℤ × ℤ)}
    (hdis : Set.PairwiseDisjoint (cells : Set (ℤ × ℤ)) fun J => dyadicGridCell Gd J.1 J.2)
    (c : ℤ × ℤ → Ms.Md → ℂ) {J : ℤ × ℤ} (hJ : J ∈ cells) :
    columnL2Restriction (dyadicGridCell Gd J.1 J.2) (dyadicGridCell_measurable Gd J.1 J.2)
        (Ms.paperBlockSide S hA SP b cells c) =
      ∑ E ∈ Ms.paperSideEvents S hA SP b J, ∑ m ∈ E, c J m • Ms.cellMode J m := by
  unfold paperBlockSide
  rw [map_sum, Finset.sum_eq_single_of_mem J hJ]
  · simp only [map_sum, map_smul, Ms.restrict_cellMode_self]
  · intro J' hJ' hne
    simp only [map_sum, map_smul, Ms.restrict_cellMode_disjoint (hdis hJ' hJ hne), smul_zero,
      Finset.sum_const_zero]
open Classical in
/-- The block side subtotal `V_{l,G,b}` restricted to an actual cell `I` inside one of its pre-cells
`J` is the side synthesis on `I` with the frozen coefficients of `J`. -/
theorem paper_restrict_blockSide_actual {b : ℤ} {cells : Finset (ℤ × ℤ)}
    (hdepth : ∀ J ∈ cells, J.1 = b - 2 * S.K) (c : ℤ × ℤ → Ms.Md → ℂ) {J I : ℤ × ℤ}
    (hJ : J ∈ cells) (hIJ : dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd J.1 J.2) :
    columnL2Restriction (dyadicGridCell Gd I.1 I.2) (dyadicGridCell_measurable Gd I.1 I.2)
        (Ms.paperBlockSide S hA SP b cells c) =
      ∑ m ∈ (Ms.alive (ancAt Gd J (b - 4 * S.K))).filter
        (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m), c J m • Ms.cellMode I m := by
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  have hdis : Set.PairwiseDisjoint (cells : Set (ℤ × ℤ)) fun J => dyadicGridCell Gd J.1 J.2 := by
    intro J hJ J' hJ' hne
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
    by_contra hov
    exact hne (dyadicGridCell_eq_of_meet Gd ((hdepth J hJ).trans (hdepth J' hJ').symm)
      (Set.nonempty_iff_ne_empty.mpr hov))
  have h1 : columnL2Restriction (dyadicGridCell Gd I.1 I.2) (dyadicGridCell_measurable Gd I.1 I.2)
        (Ms.paperBlockSide S hA SP b cells c) =
      columnL2Restriction (dyadicGridCell Gd I.1 I.2) (dyadicGridCell_measurable Gd I.1 I.2)
        (columnL2Restriction (dyadicGridCell Gd J.1 J.2) (dyadicGridCell_measurable Gd J.1 J.2)
          (Ms.paperBlockSide S hA SP b cells c)) := by
    rw [← ContinuousLinearMap.comp_apply (columnL2Restriction _ _),
      columnL2Restriction_comp_of_subset _ _ hIJ]
  rw [h1, Ms.paper_restrict_blockSide S hA SP hdis c hJ,
    Ms.paper_sum_sideEvents_eq S hA SP (by rw [hdepth J hJ]; omega)]
  simp only [map_sum, map_smul, Ms.cellMode_restrict hIJ]

open Classical in
/-- Blueprint `eq:size-comparison` (lines 2202-2209), second assertion, with `V = V_{l,G,b}`: on an
actual cell `I` of length at least `r_{t_b}` inside a pre-cell `J` of the block, for any family
`Fs` of CURRENT components at height `h`, `Σ_{F ∈ Fs} ‖V_F‖²_{2,I} ≤ 2 ‖V_{l,G,b}‖²_{2,I}`. -/
theorem paper_side_comparison_block {b : ℤ} {cells : Finset (ℤ × ℤ)}
    (hdepth : ∀ J ∈ cells, J.1 = b - 2 * S.K) (c : ℤ × ℤ → Ms.Md → ℂ) {J I : ℤ × ℤ}
    (hJ : J ∈ cells) (hIJ : dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd J.1 J.2)
    (hIt : I.1 ≤ b + S.K) (hD : 2 ≤ S.Dstar) (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar)
    (hQ0 : 0 < S.Q0) (Kf : ℕ) (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m)
    (halive : ((Ms.alive (ancAt Gd J (b - 4 * S.K))).card : ℝ) ≤ S.Dstar)
    (h : ℕ) {Fs : Finset (Finset Ms.Md)} (hFs : Fs ⊆ Ms.curComps S hA b J h) :
    ∑ F ∈ Fs, ‖∑ m ∈ F.filter (fun m => ¬ Ms.paperIsCoreAt S hA SP b J m),
        c J m • Ms.cellMode I m‖ ^ 2 ≤
      2 * ‖columnL2Restriction (dyadicGridCell Gd I.1 I.2) (dyadicGridCell_measurable Gd I.1 I.2)
        (Ms.paperBlockSide S hA SP b cells c)‖ ^ 2 := by
  rw [Ms.paper_restrict_blockSide_actual S hA SP hdepth c hJ hIJ]
  exact Ms.paper_side_comparison S hA SP (hdepth J hJ) hIJ hIt hD hδ hΛ hQ0 Kf hbox hDg hKf hεw halive
    (c J) h hFs

open Classical in
/-- The linking step of `attempt_representatives3` (blueprint lines 2176-2181): if the mode of an
earlier node is CURRENT-joined at height `h` in the later graph to the mode of a later comparable
node of the same first type, the earlier predecessor is contained in the later one. -/
theorem paper_pred_nested_of_link (Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md))
    (hNd : ∀ c ∈ Nd, c.2.1.1 = c.1 - 2 * S.K) (Δ h : ℕ)
    (halive : ∀ c ∈ Nd, c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)))
    (hgood : ∀ c (hc : c ∈ Nd), (Ms.blockComps S hA c.1 c.2.1).PaperGood Δ (Ms.goodP S SP c.1) h
      ⟨c.2.2, halive c hc⟩)
    (hstab : ∀ c ∈ Nd, ∀ z z', Ms.goodP S SP c.1 h ((Ms.blockComps S hA c.1 c.2.1).π z) →
      (Ms.blockComps S hA c.1 c.2.1).π z' = (Ms.blockComps S hA c.1 c.2.1).π z →
      z' ∈ (Ms.blockComps S hA c.1 c.2.1).F h z → z' ∈ (Ms.blockComps S hA c.1 c.2.1).E (h - Δ) z)
    {k1 : ℕ}
    (htype1 : ∀ c (hc : c ∈ Nd), v57FloorLog ((Ms.blockComps S hA c.1 c.2.1).labels
      ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ) ⟨c.2.2, halive c hc⟩)).card = k1)
    {c c' : ℤ × (ℤ × ℤ) × Ms.Md} (hc : c ∈ Nd) (hc' : c' ∈ Nd)
    (hsub : dyadicGridCell Gd c'.2.1.1 c'.2.1.2 ⊆ dyadicGridCell Gd c.2.1.1 c.2.1.2)
    (hlt : c.1 < c'.1)
    (hlink : Ms.aliveMap (ancAt_block_subset S (hNd c hc) hlt.le hsub) ⟨c.2.2, halive c hc⟩ ∈
      (Ms.blockComps S hA c'.1 c'.2.1).F h ⟨c'.2.2, halive c' hc'⟩) :
    Ms.predOfMode S hA Δ h c ⊆ Ms.predOfMode S hA Δ h c' := by
  have hUU := ancAt_block_subset S (hNd c hc) hlt.le hsub
  have hper := fun h' {x y : Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))} =>
    Ms.blockComps_persist S hA (hNd c hc) (hNd c' hc') hlt.le hsub h' hUU (x := x) (y := y)
  have hEc : Ms.predOfMode S hA Δ h c = ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ)
      ⟨c.2.2, halive c hc⟩).map ⟨Subtype.val, Subtype.val_injective⟩ :=
    Ms.predOfMode_eq S hA Δ h (halive c hc)
  have hEc' : Ms.predOfMode S hA Δ h c' = ((Ms.blockComps S hA c'.1 c'.2.1).E (h - Δ)
      ⟨c'.2.2, halive c' hc'⟩).map ⟨Subtype.val, Subtype.val_injective⟩ :=
    Ms.predOfMode_eq S hA Δ h (halive c' hc')
  rw [hEc, hEc']
  have htype : ((Ms.blockComps S hA c'.1 c'.2.1).labels ((Ms.blockComps S hA c'.1 c'.2.1).E
      (h - Δ) ⟨c'.2.2, halive c' hc'⟩)).card <
      2 * ((Ms.blockComps S hA c.1 c.2.1).labels ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ)
        ⟨c.2.2, halive c hc⟩)).card := by
    refine OpenAI086.ReferenceV70.card_lt_two_mul_of_floorlog_eq ?_
      ((htype1 c hc).trans (htype1 c' hc').symm)
    exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _
      ((Ms.blockComps S hA c.1 c.2.1).E_self _ _)⟩
  have hnest' := ModeComponents.predecessor_nesting (Ms.blockComps S hA c.1 c.2.1)
    (Ms.blockComps S hA c'.1 c'.2.1) (Ms.aliveMap hUU)
    (fun x => by simp only [blockComps_π]; rfl)
    (fun h' x y hy => (hper h').1 hy) (fun h' x y hy => (hper h').2 hy) Δ (Ms.goodP S SP c'.1)
    (hstab c' hc') ((Ms.blockComps S hA c'.1 c'.2.1).paperGood_to_good Δ (Ms.goodP S SP c'.1) (hgood c' hc')) hlink htype
  intro y hy
  obtain ⟨y1, hy1, rfl⟩ := Finset.mem_map.mp hy
  exact Finset.mem_map.mpr ⟨Ms.aliveMap hUU y1,
    hnest' (Finset.mem_image_of_mem _ hy1), rfl⟩

open Classical in
/-- Blueprint lines 2183-2185 ("different representatives on comparable actual-use cells have no
shared or adjacent cross modes in the later CURRENT graph"), at the level of whole components:
for representatives inherited under predecessor inclusion, if two comparable nodes of one type
class have different representatives, no mode of the earlier CURRENT component is equal or
CURRENT-adjacent (in one later CURRENT component at `h`) to a mode of the later component. -/
theorem paper_comp_cross_sep (Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md))
    (hNd : ∀ c ∈ Nd, c.2.1.1 = c.1 - 2 * S.K) (Δ h : ℕ)
    (halive : ∀ c ∈ Nd, c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)))
    (hgood : ∀ c (hc : c ∈ Nd), (Ms.blockComps S hA c.1 c.2.1).PaperGood Δ (Ms.goodP S SP c.1) h
      ⟨c.2.2, halive c hc⟩)
    (hstab : ∀ c ∈ Nd, ∀ z z', Ms.goodP S SP c.1 h ((Ms.blockComps S hA c.1 c.2.1).π z) →
      (Ms.blockComps S hA c.1 c.2.1).π z' = (Ms.blockComps S hA c.1 c.2.1).π z →
      z' ∈ (Ms.blockComps S hA c.1 c.2.1).F h z → z' ∈ (Ms.blockComps S hA c.1 c.2.1).E (h - Δ) z)
    {k1 : ℕ}
    (htype1 : ∀ c (hc : c ∈ Nd), v57FloorLog ((Ms.blockComps S hA c.1 c.2.1).labels
      ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ) ⟨c.2.2, halive c hc⟩)).card = k1)
    (rep : ℤ × (ℤ × ℤ) × Ms.Md → Ms.Md)
    (hinh : ∀ c c', nodeLt3 (Gd := Gd) Ms Nd c c' →
      Ms.predOfMode S hA Δ h c ⊆ Ms.predOfMode S hA Δ h c' → rep c' = rep c)
    {c c' : ℤ × (ℤ × ℤ) × Ms.Md} (hcc' : nodeLt3 (Gd := Gd) Ms Nd c c') (hne : rep c ≠ rep c')
    (z z' : Ms.alive (ancAt Gd c'.2.1 (c'.1 - 4 * S.K)))
    (hz : z.1 ∈ ((Ms.blockComps S hA c.1 c.2.1).F h ⟨c.2.2, halive c hcc'.1⟩).map
      ⟨Subtype.val, Subtype.val_injective⟩)
    (hz' : z' ∈ (Ms.blockComps S hA c'.1 c'.2.1).F h ⟨c'.2.2, halive c' hcc'.2.1⟩) :
    z ∉ (Ms.blockComps S hA c'.1 c'.2.1).F h z' := by
  obtain ⟨hc, hc', hsub, hlt⟩ := hcc'
  intro hzF
  have hUU := ancAt_block_subset S (hNd c hc) hlt.le hsub
  obtain ⟨y1, hy1, hy1e⟩ := Finset.mem_map.mp hz
  have hfy : Ms.aliveMap hUU y1 = z := Subtype.ext hy1e
  -- the earlier component persists into the later CURRENT graph
  have hper := (Ms.blockComps_persist S hA (hNd c hc) (hNd c' hc') hlt.le hsub h hUU
    (x := ⟨c.2.2, halive c hc⟩) (y := y1)).2 hy1
  rw [hfy] at hper
  have hlink : Ms.aliveMap hUU ⟨c.2.2, halive c hc⟩ ∈
      (Ms.blockComps S hA c'.1 c'.2.1).F h ⟨c'.2.2, halive c' hc'⟩ := by
    have e1 := (Ms.blockComps S hA c'.1 c'.2.1).F_comp h _ _ hper
    have e2 := (Ms.blockComps S hA c'.1 c'.2.1).F_comp h _ _ hzF
    have e3 := (Ms.blockComps S hA c'.1 c'.2.1).F_comp h _ _ hz'
    rw [← e3, ← e2, e1]
    exact (Ms.blockComps S hA c'.1 c'.2.1).E_le_F _ _ ((Ms.blockComps S hA c'.1 c'.2.1).E_self _ _)
  have hnest := Ms.paper_pred_nested_of_link S hA SP Nd hNd Δ h halive hgood hstab htype1 hc hc' hsub
    hlt hlink
  exact hne (hinh c c' ⟨hc, hc', hsub, hlt⟩ hnest).symm

open Classical in
theorem paper_firstTops_pair_sep (Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md))
    (hNd : ∀ c ∈ Nd, c.2.1.1 = c.1 - 2 * S.K) (Δ h : ℕ)
    (halive : ∀ c ∈ Nd, c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)))
    (hgood : ∀ c (hc : c ∈ Nd), (Ms.blockComps S hA c.1 c.2.1).PaperGood Δ (Ms.goodP S SP c.1) h
      ⟨c.2.2, halive c hc⟩)
    (hstab : ∀ c ∈ Nd, ∀ z z', Ms.goodP S SP c.1 h ((Ms.blockComps S hA c.1 c.2.1).π z) →
      (Ms.blockComps S hA c.1 c.2.1).π z' = (Ms.blockComps S hA c.1 c.2.1).π z →
      z' ∈ (Ms.blockComps S hA c.1 c.2.1).F h z → z' ∈ (Ms.blockComps S hA c.1 c.2.1).E (h - Δ) z)
    {k1 : ℕ}
    (htype1 : ∀ c (hc : c ∈ Nd), v57FloorLog ((Ms.blockComps S hA c.1 c.2.1).labels
      ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ) ⟨c.2.2, halive c hc⟩)).card = k1)
    (hdist : ∀ c (hc : c ∈ Nd) c' (hc' : c' ∈ Nd) (h1 : c.1 = c'.1) (h2 : c.2.1 = c'.2.1),
      c ≠ c' → (⟨c'.2.2, by rw [h1, h2]; exact halive c' hc'⟩ :
        Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) ∉
        (Ms.blockComps S hA c.1 c.2.1).F h ⟨c.2.2, halive c hc⟩)
    (rep : ℤ × (ℤ × ℤ) × Ms.Md → Ms.Md)
    (hrep : ∀ c, rep c ∈ Ms.predOfMode S hA Δ h c)
    (hinh : ∀ c c', nodeLt3 (Gd := Gd) Ms Nd c c' →
      Ms.predOfMode S hA Δ h c ⊆ Ms.predOfMode S hA Δ h c' → rep c' = rep c)
    (hsp : ∀ c ∈ Nd, ∀ c' ∈ Nd, c.1 ≠ c'.1 → c.1 + S.K ≤ c'.1 ∨ c'.1 + S.K ≤ c.1)
    (X : Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md)))
    (hX : ∀ p ∈ X, p.2 ∈ Nd ∧
      dyadicGridCell Gd p.1.1 p.1.2 ⊆ dyadicGridCell Gd p.2.2.1.1 p.2.2.1.2 ∧
      p.2.1 ≤ p.1.1 ∧ p.1.1 < p.2.1 + S.K)
    (σ : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md) → ℝ) (σ₀ : ℝ) (hΛ : 8 * Ms.Λ ≤ S.Ξ)
    {p p' : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md)} (hp : p ∈ Ms.firstTops X rep σ σ₀)
    (hp' : p' ∈ Ms.firstTops X rep σ σ₀)
    (hsub : dyadicGridCell Gd p.1.1 p.1.2 ⊆ dyadicGridCell Gd p'.1.1 p'.1.2)
    (hne : Ms.topRow S hA h p ≠ Ms.topRow S hA h p') :
    Disjoint (Ms.nodeComp S hA h p.2) (Ms.nodeComp S hA h p'.2) ∧
      ∀ m ∈ Ms.nodeComp S hA h p.2, ∀ m' ∈ Ms.nodeComp S hA h p'.2,
        ∀ n : Fin Ms.zc.dim → ℤ, (∀ i, |(n i : ℝ)| ≤ S.Eh 0) →
          S.Ξ / 2 / dyadicGridLength Gd p.1.1 <
            |Ms.slope m (dyadicGridLeft Gd p.1.1 p.1.2) -
              Ms.slope m' (dyadicGridLeft Gd p.1.1 p.1.2) +
                ∑ i, (n i : ℝ) * (Ms.zc.θ i / S.Q0)| := by
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  obtain ⟨I, c⟩ := p
  obtain ⟨I', c'⟩ := p'
  simp only at hsub hne ⊢
  obtain ⟨hpX, hσp, hmax⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp'X, hσp', -⟩ := Finset.mem_filter.mp hp'
  obtain ⟨hc, hIJ, hb1, hb2⟩ := hX _ hpX
  obtain ⟨hc', hIJ', hb1', hb2'⟩ := hX _ hp'X
  simp only at hc hIJ hb1 hb2 hc' hIJ' hb1' hb2' hσp hσp' hmax
  have hII := dyadicGridLength_le_of_subset Gd hsub
  have hIdepth : I'.1 ≤ I.1 := by
    by_contra hlt
    push Not at hlt
    have := (dyadicGridLength_strictAnti Gd) hlt
    linarith
  -- the later node is `c` (block of the inner cell); the earlier is `c'`
  have hbb : c'.1 ≤ c.1 := by
    by_contra hlt
    push Not at hlt
    rcases hsp c hc c' hc' (by omega) with h1 | h1 <;> omega
  have hJJ : dyadicGridCell Gd c.2.1.1 c.2.1.2 ⊆ dyadicGridCell Gd c'.2.1.1 c'.2.1.2 :=
    dyadicGridCell_subset_of_common_point Gd (hIJ (dyadicGridCell_left_mem Gd I.1 I.2))
      (hIJ' (hsub (dyadicGridCell_left_mem Gd I.1 I.2)))
      (by rw [hNd c hc, hNd c' hc']; omega)
  -- the alive transport from the earlier decision cell
  have hUU := ancAt_block_subset S (hNd c' hc') hbb hJJ
  -- the separation for modes of the later component against modes in other later components
  have hsepF : ∀ z z' : Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)),
      z ∉ (Ms.blockComps S hA c.1 c.2.1).F h z' →
      z.1 ≠ z'.1 ∧ ∀ n : Fin Ms.zc.dim → ℤ, (∀ i, |(n i : ℝ)| ≤ S.Eh 0) →
        S.Ξ / 2 / dyadicGridLength Gd I.1 < |Ms.slope z'.1 (dyadicGridLeft Gd I.1 I.2) -
          Ms.slope z.1 (dyadicGridLeft Gd I.1 I.2) + ∑ i, (n i : ℝ) * (Ms.zc.θ i / S.Q0)| := by
    intro z z' hzF
    refine ⟨fun he => hzF ?_, fun n hn => Ms.alive_sep_at_cell S hA (hNd c hc) hIJ (by omega) hΛ
      (fun h0 => hzF ((Ms.blockComps S hA c.1 c.2.1).F_mono 0 h z' (Nat.zero_le _) h0)) n hn⟩
    rw [show z = z' from Subtype.ext he]
    exact (Ms.blockComps S hA c.1 c.2.1).E_le_F _ _ ((Ms.blockComps S hA c.1 c.2.1).E_self _ _)
  -- the representatives differ
  have hrne : rep c ≠ rep c' := by
    intro hreq
    have hI'I : I' = I := hmax _ hp'X hσp' hreq.symm hsub
    subst hI'I
    have hbe : c.1 = c'.1 := by
      by_contra hb
      rcases hsp c hc c' hc' hb with h1 | h1 <;> omega
    have hJe : c.2.1 = c'.2.1 := dyadicGridCell_eq_of_meet Gd
      (by rw [hNd c hc, hNd c' hc', hbe])
      ⟨_, hIJ (dyadicGridCell_left_mem Gd I'.1 I'.2), hIJ' (dyadicGridCell_left_mem Gd I'.1 I'.2)⟩
    have hcc : c ≠ c' := fun h => hne (by rw [h])
    have hd := hdist c hc c' hc' hbe hJe hcc
    -- the representatives lie in the two distinct components
    have h1 := Ms.predOfMode_subset_nodeComp S hA Δ h (halive c hc) (hrep c)
    have h2 := Ms.predOfMode_subset_nodeComp S hA Δ h (halive c' hc') (hrep c')
    rw [Ms.nodeComp_eq S hA h (halive c hc)] at h1
    rw [Ms.nodeComp_eq S hA h (halive c' hc')] at h2
    obtain ⟨y1, hy1, hy1e⟩ := Finset.mem_map.mp h1
    obtain ⟨y2, hy2, hy2e⟩ := Finset.mem_map.mp h2
    have hy2' : (⟨y2.1, by rw [hbe, hJe]; exact y2.2⟩ : Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)))
        ∈ (Ms.blockComps S hA c.1 c.2.1).F h ⟨c'.2.2, by rw [hbe, hJe]; exact halive c' hc'⟩ := by
      obtain ⟨b1, J1, m1⟩ := c
      obtain ⟨b2, J2, m2⟩ := c'
      simp only at hbe hJe y2 hy2 ⊢
      subst hbe hJe
      exact hy2
    have he : (⟨y2.1, by rw [hbe, hJe]; exact y2.2⟩ : Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) =
        y1 := Subtype.ext ((hy2e.trans hreq.symm).trans hy1e.symm)
    rw [he] at hy2'
    apply hd
    rw [← (Ms.blockComps S hA c.1 c.2.1).F_comp h _ _ hy1,
      (Ms.blockComps S hA c.1 c.2.1).F_comp h _ _ hy2']
    exact (Ms.blockComps S hA c.1 c.2.1).E_le_F _ _ ((Ms.blockComps S hA c.1 c.2.1).E_self _ _)
  -- every outer mode, transported, is not CURRENT-joined to an inner mode
  have hkey : ∀ m ∈ Ms.nodeComp S hA h c, ∀ m' ∈ Ms.nodeComp S hA h c',
      ∃ (z z' : Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))), z'.1 = m ∧ z.1 = m' ∧
        z ∉ (Ms.blockComps S hA c.1 c.2.1).F h z' := by
    intro m hm m' hm'
    rw [Ms.nodeComp_eq S hA h (halive c hc)] at hm
    rw [Ms.nodeComp_eq S hA h (halive c' hc')] at hm'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hm
    obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp hm'
    refine ⟨Ms.aliveMap hUU a', a, rfl, rfl, ?_⟩
    rcases hbb.lt_or_eq with hlt | heq
    · -- different blocks: `paper_comp_cross_sep` on the comparable nodes `c' < c`
      exact Ms.paper_comp_cross_sep S hA SP Nd hNd Δ h halive hgood hstab htype1 rep hinh
        ⟨hc', hc, hJJ, hlt⟩ hrne.symm _ a (Finset.mem_map.mpr ⟨a', ha', rfl⟩) ha
    · -- one block: the pre-cells agree and the nodes lie in different components
      have hJe : c'.2.1 = c.2.1 := dyadicGridCell_eq_of_meet Gd
        (by rw [hNd c hc, hNd c' hc', heq])
        ⟨_, hJJ (dyadicGridCell_left_mem Gd c.2.1.1 c.2.1.2),
          dyadicGridCell_left_mem Gd c.2.1.1 c.2.1.2⟩
      have hcc : c' ≠ c := fun h => hrne (by rw [h])
      have hd := hdist c hc c' hc' heq.symm hJe.symm hcc.symm
      intro hmem
      apply hd
      have ha'' : Ms.aliveMap hUU a' ∈ (Ms.blockComps S hA c.1 c.2.1).F h
          ⟨c'.2.2, by rw [← heq, ← hJe]; exact halive c' hc'⟩ := by
        obtain ⟨b1, J1, m1⟩ := c
        obtain ⟨b2, J2, m2⟩ := c'
        simp only at heq hJe a' ha' hUU ⊢
        subst heq hJe
        exact ha'
      rw [← (Ms.blockComps S hA c.1 c.2.1).F_comp h _ _ ha,
        ← (Ms.blockComps S hA c.1 c.2.1).F_comp h _ _ hmem,
        (Ms.blockComps S hA c.1 c.2.1).F_comp h _ _ ha'']
      exact (Ms.blockComps S hA c.1 c.2.1).E_le_F _ _ ((Ms.blockComps S hA c.1 c.2.1).E_self _ _)
  refine ⟨Finset.disjoint_left.mpr fun m hm hm' => ?_, fun m hm m' hm' n hn => ?_⟩
  · obtain ⟨z, z', hz', hz, hzF⟩ := hkey m hm m hm'
    exact (hsepF z z' hzF).1 (hz.trans hz'.symm)
  · obtain ⟨z, z', rfl, rfl, hzF⟩ := hkey m hm m' hm'
    exact (hsepF z z' hzF).2 n hn

open Classical in
/-- Hereditary representatives of one type class at height `h` (blueprint lines 2172-2185): the
nodes `(b, J, m)` (one good mode per successful CURRENT component of a pre-cell) with the
hypotheses and conclusions of `typed_representatives`, the blocks being `K`-spaced. -/
structure PaperRepClass (Δ h : ℕ) where
  Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md)
  hNd : ∀ c ∈ Nd, c.2.1.1 = c.1 - 2 * S.K
  halive : ∀ c ∈ Nd, c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))
  hgood : ∀ c (hc : c ∈ Nd), (Ms.blockComps S hA c.1 c.2.1).PaperGood Δ (Ms.goodP S SP c.1) h
    ⟨c.2.2, halive c hc⟩
  hstab : ∀ c ∈ Nd, ∀ z z', Ms.goodP S SP c.1 h ((Ms.blockComps S hA c.1 c.2.1).π z) →
    (Ms.blockComps S hA c.1 c.2.1).π z' = (Ms.blockComps S hA c.1 c.2.1).π z →
    z' ∈ (Ms.blockComps S hA c.1 c.2.1).F h z → z' ∈ (Ms.blockComps S hA c.1 c.2.1).E (h - Δ) z
  k1 : ℕ
  htype1 : ∀ c (hc : c ∈ Nd), v57FloorLog ((Ms.blockComps S hA c.1 c.2.1).labels
    ((Ms.blockComps S hA c.1 c.2.1).E (h - Δ) ⟨c.2.2, halive c hc⟩)).card = k1
  hdist : ∀ c (hc : c ∈ Nd) c' (hc' : c' ∈ Nd) (h1 : c.1 = c'.1) (h2 : c.2.1 = c'.2.1),
    c ≠ c' → (⟨c'.2.2, by rw [h1, h2]; exact halive c' hc'⟩ :
      Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) ∉
      (Ms.blockComps S hA c.1 c.2.1).F h ⟨c.2.2, halive c hc⟩
  rep : ℤ × (ℤ × ℤ) × Ms.Md → Ms.Md
  hrep : ∀ c, rep c ∈ Ms.predOfMode S hA Δ h c
  hinh : ∀ c c', nodeLt3 (Gd := Gd) Ms Nd c c' →
    Ms.predOfMode S hA Δ h c ⊆ Ms.predOfMode S hA Δ h c' → rep c' = rep c
  hsepP : ∀ c c', nodeLt3 (Gd := Gd) Ms Nd c c' → rep c ≠ rep c' →
    ∀ z z' : Ms.alive (ancAt Gd c'.2.1 (c'.1 - 4 * S.K)), z.1 ∈ Ms.predOfMode S hA Δ h c →
      z'.1 ∈ Ms.predOfMode S hA Δ h c' → z ∉ (Ms.blockComps S hA c'.1 c'.2.1).F h z'
  hsp : ∀ c ∈ Nd, ∀ c' ∈ Nd, c.1 ≠ c'.1 → c.1 + S.K ≤ c'.1 ∨ c'.1 + S.K ≤ c.1

variable {Ms S hA SP}

/-- The instances of a type class: use cells `I` inside the pre-cell of a node `c`, at a depth of
its block. -/
def PaperRepClass.Inst {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    (X : Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md))) : Prop :=
  ∀ p ∈ X, p.2 ∈ R.Nd ∧
    dyadicGridCell Gd p.1.1 p.1.2 ⊆ dyadicGridCell Gd p.2.2.1.1 p.2.2.1.2 ∧
    p.2.1 ≤ p.1.1 ∧ p.1.1 < p.2.1 + S.K

theorem PaperRepClass.pair_sep {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    {X : Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md))} (hX : R.Inst X)
    (σ : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md) → ℝ) (σ₀ : ℝ) (hΛ : 8 * Ms.Λ ≤ S.Ξ)
    {p p' : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md)} (hp : p ∈ Ms.firstTops X R.rep σ σ₀)
    (hp' : p' ∈ Ms.firstTops X R.rep σ σ₀)
    (hsub : dyadicGridCell Gd p.1.1 p.1.2 ⊆ dyadicGridCell Gd p'.1.1 p'.1.2)
    (hne : Ms.topRow S hA h p ≠ Ms.topRow S hA h p') :
    Disjoint (Ms.nodeComp S hA h p.2) (Ms.nodeComp S hA h p'.2) ∧
      ∀ m ∈ Ms.nodeComp S hA h p.2, ∀ m' ∈ Ms.nodeComp S hA h p'.2,
        ∀ n : Fin Ms.zc.dim → ℤ, (∀ i, |(n i : ℝ)| ≤ S.Eh 0) →
          S.Ξ / 2 / dyadicGridLength Gd p.1.1 <
            |Ms.slope m (dyadicGridLeft Gd p.1.1 p.1.2) -
              Ms.slope m' (dyadicGridLeft Gd p.1.1 p.1.2) + ∑ i, (n i : ℝ) * (Ms.zc.θ i / S.Q0)| :=
  Ms.paper_firstTops_pair_sep S hA SP R.Nd R.hNd Δ h R.halive R.hgood R.hstab R.htype1 R.hdist R.rep
    R.hrep R.hinh R.hsp X hX σ σ₀ hΛ hp hp' hsub hne

open Classical in
/-- Distinct first tops have distinct rows. -/
theorem PaperRepClass.topRow_injOn {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    {X : Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md))} (hX : R.Inst X)
    (σ : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md) → ℝ) (σ₀ : ℝ) :
    Set.InjOn (Ms.topRow S hA h) (Ms.firstTops X R.rep σ σ₀ : Set _) := by
  intro p hp p' hp' heq
  obtain ⟨I, c⟩ := p
  obtain ⟨I', c'⟩ := p'
  have hpX := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1
  have hp'X := (Finset.mem_filter.mp (Finset.mem_coe.mp hp')).1
  obtain ⟨hc, hIJ, -, -⟩ := hX _ hpX
  obtain ⟨hc', hIJ', -, -⟩ := hX _ hp'X
  simp only [topRow, Prod.mk.injEq] at heq hc hIJ hc' hIJ'
  obtain ⟨hbe, hIe, hcomp⟩ := heq
  subst hIe
  have hJe : c.2.1 = c'.2.1 := dyadicGridCell_eq_of_meet Gd
    (by rw [R.hNd c hc, R.hNd c' hc', hbe])
    ⟨_, hIJ (dyadicGridCell_left_mem Gd I.1 I.2), hIJ' (dyadicGridCell_left_mem Gd I.1 I.2)⟩
  by_contra hne
  have hcc : c ≠ c' := fun h => hne (by rw [h])
  apply R.hdist c hc c' hc' hbe hJe hcc
  -- the mode of `c'` lies in the component of `c`
  have hm' : c'.2.2 ∈ Ms.nodeComp S hA h c := by
    rw [hcomp, Ms.nodeComp_eq S hA h (R.halive c' hc')]
    exact Finset.mem_map.mpr ⟨_, (Ms.blockComps S hA c'.1 c'.2.1).E_le_F _ _
      ((Ms.blockComps S hA c'.1 c'.2.1).E_self _ _), rfl⟩
  rw [Ms.nodeComp_eq S hA h (R.halive c hc)] at hm'
  obtain ⟨a, ha, hae⟩ := Finset.mem_map.mp hm'
  rw [show (⟨c'.2.2, by rw [hbe, hJe]; exact R.halive c' hc'⟩ :
      Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) = a from Subtype.ext hae.symm]
  exact ha

open Classical in
theorem PaperRepClass.firstTops_rows {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    {X : Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md))} (hX : R.Inst X)
    (σ : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md) → ℝ) (σ₀ : ℝ)
    (hD : 2 ≤ S.Dstar) (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m) (hpt : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ S.Dstar)
    [inst : ∀ e, (Submodule.span ℂ ((Ms.evMode e) '' (e.2.2 : Set Ms.Md))).HasOrthogonalProjection]
    (F : ColumnL2 Ms.Md) :
    ∑ e ∈ (Ms.firstTops X R.rep σ σ₀).image (Ms.topRow S hA h),
        ‖(Submodule.span ℂ ((Ms.evMode e) '' (e.2.2 : Set Ms.Md))).starProjection F‖ ^ 2 ≤
      2 * ‖F‖ ^ 2 := by
  classical
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  have hDp : 0 < S.Dstar := by linarith
  have hΞ : 0 < S.Ξ := pow_pos hDp 1000
  have hΛ16 := Ms.sixteen_Λ_le S hD hΛ
  have hε : 0 < S.Dstar⁻¹ := inv_pos.mpr hDp
  have hη0 := pairConst_nonneg Ms.zc.dim hδ (by linarith : 0 < S.Ξ / 2) Kf
  have hη200 := S.pairConst_half_mul_le hD hδ hDg hKf
  have hηD := (eta_sched_bounds hD hη0 hη200 le_rfl).1
  have hpt2 : ∀ y, ((Ms.ptSet y).card : ℝ) ≤ S.Dstar⁻¹ * S.Dstar ^ 2 := fun y => by
    rw [sq, ← mul_assoc, inv_mul_cancel₀ hDp.ne', one_mul]; exact hpt y
  have hrows := Ms.tops_rows_path S (s := (Ms.firstTops X R.rep σ σ₀).image (Ms.topRow S hA h))
    hδ ?_ ?_ (Ξ' := S.Ξ / 2) ?_ (by linarith) (by linarith) hQ0 Kf hbox hε hεw hDp.le hpt hpt2
    (inst := inst) F
  · refine hrows.trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
    linarith
  · -- the rows are nonempty
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hc, -, -, -⟩ := hX _ (Finset.mem_filter.mp hp).1
    rw [topRow, Ms.nodeComp_eq S hA h (R.halive _ hc)]
    exact ⟨_, Finset.mem_map.mpr ⟨_, (Ms.blockComps S hA _ _).E_le_F _ _
      ((Ms.blockComps S hA _ _).E_self _ _), rfl⟩⟩
  · -- the modes are alive on the top cells
    intro e he m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hc, hIJ, hb1, -⟩ := hX _ (Finset.mem_filter.mp hp).1
    simp only [topRow] at hm
    rw [Ms.nodeComp_eq S hA h (R.halive _ hc)] at hm
    obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hm
    have hJU := subset_ancAt Gd p.2.2.1 (show p.2.1 - 4 * S.K ≤ p.2.2.1.1 by
      rw [R.hNd _ hc]; omega)
    exact hIJ.trans (hJU.trans ((Ms.mem_alive).mp a.2))
  · -- overlapping rows
    intro e he e' he' hne hov
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp he'
    obtain ⟨y, hy, hy'⟩ := hov
    simp only [evCell, topRow] at hy hy' ⊢
    rcases le_total p'.1.1 p.1.1 with hle | hle
    · have hsub := dyadicGridCell_subset_of_common_point Gd hy hy' hle
      obtain ⟨hdis, hsep⟩ := R.pair_sep hX σ σ₀ (by linarith) hp hp' hsub hne
      refine ⟨p.1, Set.inter_eq_left.mpr hsub, hdis, fun m hm m' hm' n hn =>
        ⟨_, ⟨le_rfl, by linarith [dyadicGridLength_pos Gd p.1.1]⟩, (hsep m hm m' hm' n hn).le⟩⟩
    · have hsub := dyadicGridCell_subset_of_common_point Gd hy' hy hle
      obtain ⟨hdis, hsep⟩ := R.pair_sep hX σ σ₀ (by linarith) hp' hp hsub (Ne.symm hne)
      refine ⟨p'.1, Set.inter_eq_right.mpr hsub, hdis.symm, fun m hm m' hm' n hn =>
        ⟨_, ⟨le_rfl, by linarith [dyadicGridLength_pos Gd p'.1.1]⟩, ?_⟩⟩
      have hn' : ∀ i, |((-n i : ℤ) : ℝ)| ≤ S.Eh 0 := fun i => by
        push_cast; rw [abs_neg]; exact hn i
      have := (hsep m' hm' m hm (fun i => -n i) hn').le
      rw [abs_slope_flip] at this
      exact this

end ModeSystem

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} {Ms : ModeSystem Gd Mc} {S : ModeSchedule}
  {hA : 6 ≤ S.A0} {SP : SideParams}

open Classical in
theorem PaperRepClass.tops_side {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    {X : Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md))} (hX : R.Inst X)
    (σ : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md) → ℝ) (σ₀ : ℝ)
    (cells : ℤ → Finset (ℤ × ℤ)) (hdepth : ∀ b, ∀ J ∈ cells b, J.1 = b - 2 * S.K)
    (hXc : ∀ p ∈ X, p.2.2.1 ∈ cells p.2.1) (Bs : Finset ℤ) (hXB : ∀ p ∈ X, p.2.1 ∈ Bs)
    (c : ℤ → ℤ × ℤ → Ms.Md → ℂ)
    (hD : 2 ≤ S.Dstar) (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m)
    (hal : ∀ b, ∀ J ∈ cells b, ((Ms.alive (ancAt Gd J (b - 4 * S.K))).card : ℝ) ≤ S.Dstar) :
    ∑ p ∈ Ms.firstTops X R.rep σ σ₀,
        ‖∑ m ∈ (Ms.nodeComp S hA h p.2).filter (fun m => ¬ Ms.paperIsCoreAt S hA SP p.2.1 p.2.2.1 m),
          c p.2.1 p.2.2.1 m • Ms.cellMode p.1 m‖ ^ 2 ≤
      2 * S.K * ∑ b ∈ Bs, ‖Ms.paperBlockSide S hA SP b (cells b) (c b)‖ ^ 2 := by
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  set T := Ms.firstTops X R.rep σ σ₀ with hT
  have hTX : ∀ p ∈ T, p ∈ X := fun p hp => (Finset.mem_filter.mp hp).1
  set f : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md) → ℝ := fun p =>
    ‖∑ m ∈ (Ms.nodeComp S hA h p.2).filter (fun m => ¬ Ms.paperIsCoreAt S hA SP p.2.1 p.2.2.1 m),
      c p.2.1 p.2.2.1 m • Ms.cellMode p.1 m‖ ^ 2 with hf
  set! g : ℤ × (ℤ × ℤ) → ℝ := fun k => ‖columnL2Restriction (dyadicGridCell Gd k.2.1 k.2.2)
    (dyadicGridCell_measurable Gd k.2.1 k.2.2) (Ms.paperBlockSide S hA SP k.1 (cells k.1) (c k.1))‖ ^ 2
    with hg
  -- step 1: the tops at one block and cell
  have hstep1 : ∀ k ∈ T.image (fun p => (p.2.1, p.1)),
      ∑ p ∈ T.filter (fun p => (p.2.1, p.1) = k), f p ≤ 2 * g k := by
    intro k hk
    obtain ⟨p0, hp0, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hc0, hIJ0, hb10, hb20⟩ := hX _ (hTX p0 hp0)
    -- all tops of the fiber share the pre-cell of `p0`
    have hJ : ∀ p ∈ T.filter (fun p => (p.2.1, p.1) = (p0.2.1, p0.1)), p.2.2.1 = p0.2.2.1 := by
      intro p hp
      obtain ⟨hpT, hpk⟩ := Finset.mem_filter.mp hp
      simp only [Prod.mk.injEq] at hpk
      obtain ⟨hc, hIJ, -, -⟩ := hX _ (hTX p hpT)
      refine dyadicGridCell_eq_of_meet Gd (by rw [R.hNd _ hc, R.hNd _ hc0, hpk.1])
        ⟨dyadicGridLeft Gd p.1.1 p.1.2, ?_, ?_⟩
      · exact hIJ (dyadicGridCell_left_mem Gd p.1.1 p.1.2)
      · rw [hpk.2]; exact hIJ0 (dyadicGridCell_left_mem Gd p0.1.1 p0.1.2)
    -- the components of the fiber
    have hinj : Set.InjOn (fun p : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md) => Ms.nodeComp S hA h p.2)
        (T.filter (fun p => (p.2.1, p.1) = (p0.2.1, p0.1)) : Set _) := by
      intro p hp p' hp' heq
      obtain ⟨hpT, hpk⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      obtain ⟨hp'T, hp'k⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp')
      simp only [Prod.mk.injEq] at hpk hp'k
      refine R.topRow_injOn hX σ σ₀ (Finset.mem_coe.mpr hpT) (Finset.mem_coe.mpr hp'T) ?_
      simp only [topRow, Prod.mk.injEq]
      exact ⟨hpk.1.trans hp'k.1.symm, hpk.2.trans hp'k.2.symm, heq⟩
    have hsum : ∑ p ∈ T.filter (fun p => (p.2.1, p.1) = (p0.2.1, p0.1)), f p =
        ∑ F ∈ (T.filter (fun p => (p.2.1, p.1) = (p0.2.1, p0.1))).image
          (fun p => Ms.nodeComp S hA h p.2),
          ‖∑ m ∈ F.filter (fun m => ¬ Ms.paperIsCoreAt S hA SP p0.2.1 p0.2.2.1 m),
            c p0.2.1 p0.2.2.1 m • Ms.cellMode p0.1 m‖ ^ 2 := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨-, hpk⟩ := Finset.mem_filter.mp hp
      simp only [Prod.mk.injEq] at hpk
      simp only [hf, hpk.1, hpk.2, hJ p hp]
    rw [hsum]
    have hFs : (T.filter (fun p => (p.2.1, p.1) = (p0.2.1, p0.1))).image
        (fun p => Ms.nodeComp S hA h p.2) ⊆ Ms.curComps S hA p0.2.1 p0.2.2.1 h := by
      intro F hF
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨hpT, hpk⟩ := Finset.mem_filter.mp hp
      simp only [Prod.mk.injEq] at hpk
      obtain ⟨hc, -, -, -⟩ := hX _ (hTX p hpT)
      have hJp := hJ p hp
      rw [Ms.nodeComp_eq S hA h (R.halive _ hc)]
      have key : ∀ (b : ℤ) (J : ℤ × ℤ) (m : Ms.Md) (hm : m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K))),
          b = p0.2.1 → J = p0.2.2.1 → ((Ms.blockComps S hA b J).F h ⟨m, hm⟩).map
            ⟨Subtype.val, Subtype.val_injective⟩ ∈ Ms.curComps S hA p0.2.1 p0.2.2.1 h := by
        rintro b J m hm rfl rfl
        exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
      exact key _ _ _ _ hpk.1 hJp
    have hside := Ms.paper_side_comparison_block S hA SP (hdepth p0.2.1) (c p0.2.1)
      (hXc p0 (hTX p0 hp0)) hIJ0 (by omega) hD hδ hΛ hQ0 Kf hbox hDg hKf hεw
      (hal _ _ (hXc p0 (hTX p0 hp0))) h hFs
    exact hside
  -- step 2: group the tops by block and cell
  have hT1 : ∑ p ∈ T, f p = ∑ k ∈ T.image (fun p => (p.2.1, p.1)),
      ∑ p ∈ T.filter (fun p => (p.2.1, p.1) = k), f p :=
    (Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_image_of_mem _ hp) f).symm
  -- step 3: the cells of one block and depth are disjoint
  have hkey : ∀ k ∈ T.image (fun p => (p.2.1, p.1)),
      k.1 ∈ Bs ∧ k.1 ≤ k.2.1 ∧ k.2.1 < k.1 + S.K := by
    intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨-, -, hb1, hb2⟩ := hX _ (hTX p hp)
    exact ⟨hXB p (hTX p hp), hb1, hb2⟩
  have hstep3 : ∑ k ∈ T.image (fun p => (p.2.1, p.1)), g k ≤
      S.K * ∑ b ∈ Bs, ‖Ms.paperBlockSide S hA SP b (cells b) (c b)‖ ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun k : ℤ × (ℤ × ℤ) => (k.1, k.2.1))
      (t := (T.image (fun p => (p.2.1, p.1))).image (fun k : ℤ × (ℤ × ℤ) => (k.1, k.2.1)))
      (fun k hk => Finset.mem_image_of_mem _ hk)]
    refine le_trans (Finset.sum_le_sum fun bd _ => ?_)
      (sum_pairs_le_card_mul (w := fun b => ‖Ms.paperBlockSide S hA SP b (cells b) (c b)‖ ^ 2)
        (fun b => sq_nonneg _) fun bd hbd => ?_)
    · -- one block and depth
      set Φ := (T.image (fun p => (p.2.1, p.1))).filter
        (fun k : ℤ × (ℤ × ℤ) => (k.1, k.2.1) = bd)
      have hΦ : ∀ k ∈ Φ, k.1 = bd.1 ∧ k.2.1 = bd.2 := fun k hk => by
        have := (Finset.mem_filter.mp hk).2
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
      have hinjΦ : Set.InjOn (fun k : ℤ × (ℤ × ℤ) => k.2) (Φ : Set _) := by
        intro x hx y hy hxy
        exact Prod.ext ((hΦ x hx).1.trans (hΦ y hy).1.symm) hxy
      have hsumΦ : ∑ k ∈ Φ, g k = ∑ I ∈ Φ.image (fun k => k.2),
          ‖columnL2Restriction (dyadicGridCell Gd I.1 I.2) (dyadicGridCell_measurable Gd I.1 I.2)
            (Ms.paperBlockSide S hA SP bd.1 (cells bd.1) (c bd.1))‖ ^ 2 := by
        rw [Finset.sum_image hinjΦ]
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [hg, (hΦ k hk).1]
      rw [hsumΦ, sum_norm_sq_restrict_le Gd _ ?_]
      · exact columnL2Restriction_norm_sq_le _ _ _
      · intro I hI I' hI' hne
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hI
        obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hI'
        rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
        by_contra hov
        exact hne (dyadicGridCell_eq_of_meet Gd ((hΦ k hk).2.trans (hΦ k' hk').2.symm)
          (Set.nonempty_iff_ne_empty.mpr hov))
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hbd
      exact hkey k hk
  have hg0 : ∀ k, 0 ≤ g k := fun k => sq_nonneg _
  calc ∑ p ∈ T, f p = ∑ k ∈ T.image (fun p => (p.2.1, p.1)),
        ∑ p ∈ T.filter (fun p => (p.2.1, p.1) = k), f p := hT1
    _ ≤ ∑ k ∈ T.image (fun p => (p.2.1, p.1)), 2 * g k := Finset.sum_le_sum hstep1
    _ = 2 * ∑ k ∈ T.image (fun p => (p.2.1, p.1)), g k := by rw [Finset.mul_sum]
    _ ≤ 2 * (S.K * ∑ b ∈ Bs, ‖Ms.paperBlockSide S hA SP b (cells b) (c b)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep3 (by norm_num)
    _ = 2 * S.K * ∑ b ∈ Bs, ‖Ms.paperBlockSide S hA SP b (cells b) (c b)‖ ^ 2 := by ring

end ModeSystem

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)
open Classical in
/-- The component size `σ_F²` (`eq:component-size`) of the node of an instance `(I, c)` on its
cell, with the frozen coefficients `c b J` of its block and pre-cell (zero off the alive modes). -/
noncomputable def paperNodeSize (c : ℤ → ℤ × ℤ → Ms.Md → ℂ) (h : ℕ)
    (p : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md)) : ℝ :=
  if hm : p.2.2.2 ∈ Ms.alive (ancAt Gd p.2.2.1 (p.2.1 - 4 * S.K)) then
    Ms.paperCompSizeSq S hA SP p.1 p.2.1 p.2.2.1 h ⟨p.2.2.2, hm⟩ (c p.2.1 p.2.2.1)
  else 0

theorem paperNodeSize_eq (c : ℤ → ℤ × ℤ → Ms.Md → ℂ) (h : ℕ)
    {p : (ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md)}
    (hm : p.2.2.2 ∈ Ms.alive (ancAt Gd p.2.2.1 (p.2.1 - 4 * S.K))) :
    Ms.paperNodeSize S hA SP c h p =
      Ms.paperCompSizeSq S hA SP p.1 p.2.1 p.2.2.1 h ⟨p.2.2.2, hm⟩ (c p.2.1 p.2.2.1) := by
  unfold paperNodeSize
  rw [dite_eq_left_of_eq_true (eq_true hm)]

variable {Ms S hA SP}

open Classical in
theorem PaperRepClass.tops_absorb {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    {X : Finset ((ℤ × ℤ) × (ℤ × (ℤ × ℤ) × Ms.Md))} (hX : R.Inst X)
    (c : ℤ → ℤ × ℤ → Ms.Md → ℂ) {σ₀ Bc : ℝ}
    (hD : 2 ≤ S.Dstar) (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m)
    (hal : ∀ p ∈ X, ((Ms.alive (ancAt Gd p.2.2.1 (p.2.1 - 4 * S.K))).card : ℝ) ≤ S.Dstar)
    (hc : ∀ p ∈ X, ∑ m ∈ Ms.alive (ancAt Gd p.2.2.1 (p.2.1 - 4 * S.K)),
      ‖c p.2.1 p.2.2.1 m‖ ^ 2 ≤ Bc)
    (hab : 6 * Bc / S.Dstar ^ 59 ≤ σ₀)
    [inst : ∀ e,
      (Submodule.span ℂ ((Ms.evMode e) '' (e.2.2 : Set Ms.Md))).HasOrthogonalProjection] :
    σ₀ * ∑ p ∈ Ms.firstTops X R.rep (Ms.paperNodeSize S hA SP c h) σ₀, dyadicGridLength Gd p.1.1 ≤
      24 * (∑ p ∈ Ms.firstTops X R.rep (Ms.paperNodeSize S hA SP c h) σ₀,
          ‖(Submodule.span ℂ ((Ms.evMode (Ms.topRow S hA h p)) ''
            ((Ms.topRow S hA h p).2.2 : Set Ms.Md))).starProjection
            (Ms.frozenEval S p.2.1 p.2.2.1 (c p.2.1 p.2.2.1))‖ ^ 2 +
        ∑ p ∈ Ms.firstTops X R.rep (Ms.paperNodeSize S hA SP c h) σ₀,
          ‖∑ m ∈ (Ms.nodeComp S hA h p.2).filter
            (fun m => ¬ Ms.paperIsCoreAt S hA SP p.2.1 p.2.2.1 m),
            c p.2.1 p.2.2.1 m • Ms.cellMode p.1 m‖ ^ 2) := by
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  obtain ⟨hpX, hσp, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨hcN, hIJ, hb1, hb2⟩ := hX p hpX
  have hm := R.halive _ hcN
  have hr := dyadicGridLength_pos Gd p.1.1
  rw [Ms.paperNodeSize_eq S hA SP c h hm] at hσp
  have hinst : (Submodule.span ℂ ((Ms.cellMode p.1) ''
      (Ms.compModes S hA p.2.1 p.2.2.1 h ⟨p.2.2.2, hm⟩ : Set Ms.Md))).HasOrthogonalProjection := by
    have := inst (Ms.topRow S hA h p)
    simp only [topRow, Ms.nodeComp_eq_compModes S hA h hm] at this
    exact this
  have hsz := Ms.paper_size_comparison S hA SP (R.hNd _ hcN) hIJ (by omega) hD hδ hΛ hQ0 Kf hbox hDg hKf
    hεw (hal p hpX) (c p.2.1 p.2.2.1) (hc p hpX) h ⟨p.2.2.2, hm⟩
  -- the projections and side subtotals of the row are those of the size comparison
  have e1 : ‖(Submodule.span ℂ ((Ms.evMode (Ms.topRow S hA h p)) ''
      ((Ms.topRow S hA h p).2.2 : Set Ms.Md))).starProjection
        (Ms.frozenEval S p.2.1 p.2.2.1 (c p.2.1 p.2.2.1))‖ =
      ‖(Submodule.span ℂ ((Ms.cellMode p.1) ''
        (Ms.compModes S hA p.2.1 p.2.2.1 h ⟨p.2.2.2, hm⟩ : Set Ms.Md))).starProjection
        (Ms.frozenEval S p.2.1 p.2.2.1 (c p.2.1 p.2.2.1))‖ := by
    simp only [topRow, Ms.nodeComp_eq_compModes S hA h hm, evMode_eq]
  have e2 : (Ms.nodeComp S hA h p.2).filter (fun m => ¬ Ms.paperIsCoreAt S hA SP p.2.1 p.2.2.1 m) =
      (Ms.compModes S hA p.2.1 p.2.2.1 h ⟨p.2.2.2, hm⟩).filter
        (fun m => ¬ Ms.paperIsCoreAt S hA SP p.2.1 p.2.2.1 m) := by
    rw [Ms.nodeComp_eq_compModes S hA h hm]
  rw [e1, e2]
  set P2 := ‖(Submodule.span ℂ ((Ms.cellMode p.1) ''
      (Ms.compModes S hA p.2.1 p.2.2.1 h ⟨p.2.2.2, hm⟩ : Set Ms.Md))).starProjection
      (Ms.frozenEval S p.2.1 p.2.2.1 (c p.2.1 p.2.2.1))‖ ^ 2
  set V2 := ‖∑ m ∈ (Ms.compModes S hA p.2.1 p.2.2.1 h ⟨p.2.2.2, hm⟩).filter
      (fun m => ¬ Ms.paperIsCoreAt S hA SP p.2.1 p.2.2.1 m), c p.2.1 p.2.2.1 m • Ms.cellMode p.1 m‖ ^ 2
  have h1 : σ₀ ≤ 12 * ((P2 + V2) / dyadicGridLength Gd p.1.1) + σ₀ / 2 := by
    have : 3 * Bc / S.Dstar ^ 59 ≤ σ₀ / 2 := by
      have e : 3 * Bc / S.Dstar ^ 59 = (6 * Bc / S.Dstar ^ 59) / 2 := by ring
      rw [e]; linarith
    linarith [hσp.trans hsz]
  have h2 : σ₀ ≤ 24 * ((P2 + V2) / dyadicGridLength Gd p.1.1) := by linarith
  have e3 : 24 * ((P2 + V2) / dyadicGridLength Gd p.1.1) * dyadicGridLength Gd p.1.1 =
      24 * (P2 + V2) := by field_simp
  calc σ₀ * dyadicGridLength Gd p.1.1 ≤ 24 * ((P2 + V2) / dyadicGridLength Gd p.1.1) *
        dyadicGridLength Gd p.1.1 := mul_le_mul_of_nonneg_right h2 hr.le
    _ = 24 * (P2 + V2) := e3

end ModeSystem

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0)

open Classical in
/-- The empty representative class (no nodes; every mode represents itself). -/
def PaperRepClass.trivial (SP : SideParams) (Δ h : ℕ) : Ms.PaperRepClass S hA SP Δ h where
  Nd := ∅
  hNd := fun _ hc => absurd hc (Finset.notMem_empty _)
  halive := fun _ hc => absurd hc (Finset.notMem_empty _)
  hgood := fun _ hc => absurd hc (Finset.notMem_empty _)
  hstab := fun _ hc => absurd hc (Finset.notMem_empty _)
  k1 := 0
  htype1 := fun _ hc => absurd hc (Finset.notMem_empty _)
  hdist := fun _ hc => absurd hc (Finset.notMem_empty _)
  rep := fun c => c.2.2
  hrep := fun c => by
    by_cases hm : c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))
    · rw [Ms.predOfMode_eq S hA Δ h hm]
      exact Finset.mem_map.mpr ⟨⟨c.2.2, hm⟩, ModeComponents.E_self _ _ _, rfl⟩
    · unfold predOfMode
      rw [dite_eq_right_of_eq_false (eq_false hm)]
      exact Finset.mem_singleton_self _
  hinh := fun _ _ hcc => absurd hcc.1 (Finset.notMem_empty _)
  hsepP := fun _ _ hcc => absurd hcc.1 (Finset.notMem_empty _)
  hsp := fun _ hc => absurd hc (Finset.notMem_empty _)

open Classical in
/-- Blueprint lines 2172-2185 at the schedule, for one height `h ≤ J_*` and one type `(k₁, k₂)`:
nodes `(b, J, m)` (one good mode per successful CURRENT component of a pre-cell of depth `v_b`,
nodes on one pre-cell lying in different components) of this type, with their hereditary
representatives (`typed_representatives_sched`), form a `PaperRepClass` (`Δ = 10`, the side parameters
of the schedule). The blocks are `K`-spaced (`K ∣ b - R₀`), at most `D_*` modes are alive at each
decision cell and `D_*` covers the heights of mode differences. -/
theorem exists_paperRepClass {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : S.Valid Cj CA CT CK δs W)
    (hCA : 5 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ S.dmax) (hD : 2 ≤ S.Dstar) (hB : 2 ≤ S.Bstar)
    (hQ : 1 ≤ S.Q0) (hdim : ∀ p, Ms.dvOf p + Ms.zc.dim ≤ S.dmax)
    (hBσ : 2 * (S.Q0 * (3 * (Ms.Bσ * Ms.Bσ) ^ 2)) ^ 2 ≤ (⌊S.Dstar⌋₊ : ℝ))
    (Nd : Finset (ℤ × (ℤ × ℤ) × Ms.Md)) (hNd : ∀ c ∈ Nd, c.2.1.1 = c.1 - 2 * S.K)
    (halive : ∀ c ∈ Nd, c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)))
    {h : ℕ} (hJh : h ≤ S.Jstar)
    (hgood : ∀ c (hc : c ∈ Nd), (Ms.blockComps S hA c.1 c.2.1).PaperGood 10
      (Ms.goodP S (S.sideParams δs) c.1) h ⟨c.2.2, halive c hc⟩)
    (hdist : ∀ c (hc : c ∈ Nd) c' (hc' : c' ∈ Nd) (h1 : c.1 = c'.1) (h2 : c.2.1 = c'.2.1),
      c ≠ c' → (⟨c'.2.2, by rw [h1, h2]; exact halive c' hc'⟩ :
        Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) ∉
        (Ms.blockComps S hA c.1 c.2.1).F h ⟨c.2.2, halive c hc⟩)
    (R₀ : ℤ) (hblk : ∀ c ∈ Nd, (S.K : ℤ) ∣ c.1 - R₀)
    (hcard : ∀ c ∈ Nd, ((Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))).card : ℝ) ≤ S.Dstar)
    (k1 k2 : ℕ) :
    ∃ R : Ms.PaperRepClass S hA (S.sideParams δs) 10 h, R.Nd = Nd.filter
      (fun c => Ms.paperNodeType1 S hA 10 h c = k1 ∧ Ms.paperNodeType2 S hA 10 h c = k2) := by
  have hK : (0 : ℤ) ≤ S.K := Nat.cast_nonneg _
  by_cases hNd0 : Nd.Nonempty
  swap
  · refine ⟨PaperRepClass.trivial Ms S hA (S.sideParams δs) 10 h, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hNd0, Finset.filter_empty]
    rfl
  obtain ⟨Bmin, hBmin⟩ : ∃ Bmin : ℤ, ∀ c ∈ Nd, Bmin ≤ c.1 := by
    obtain ⟨B, hB'⟩ := (Nd.image Prod.fst).bddBelow
    exact ⟨B, fun c hc => hB' (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hc))⟩
  obtain ⟨rep, hrep⟩ := Ms.typed_representatives_paper S hA (S.sideParams δs) Nd
    hNd hBmin 10 h halive hgood
    (fun c hc z z' hg hπ hF => Ms.blockComps_stab S hV hCA hCT hd2 hD hB hQ hA
      hdim hBσ (hNd c hc) (hcard c hc) hJh z z' hg hπ hF)
    hdist hNd0.choose.2.2
  obtain ⟨hmem, hinh, -, hsepP⟩ := hrep k1 k2
  set Nk := Nd.filter fun c => Ms.paperNodeType1 S hA 10 h c = k1 ∧ Ms.paperNodeType2 S hA 10 h c = k2
  have hsub : ∀ c ∈ Nk, c ∈ Nd := fun c hc => (Finset.mem_filter.mp hc).1
  refine ⟨{ Nd := Nk
            hNd := fun c hc => hNd c (hsub c hc)
            halive := fun c hc => halive c (hsub c hc)
            hgood := fun c hc => hgood c (hsub c hc)
            hstab := fun c hc z z' hg hπ hF => Ms.blockComps_stab S hV hCA hCT hd2 hD hB hQ hA
              hdim hBσ (hNd c (hsub c hc)) (hcard c (hsub c hc)) hJh z z' hg hπ hF
            k1 := k1
            htype1 := fun c hc => by
              have h1 := (Finset.mem_filter.mp hc).2.1
              unfold paperNodeType1 at h1
              rwa [dite_eq_left_of_eq_true (eq_true (halive c (hsub c hc)))] at h1
            hdist := fun c hc c' hc' h1 h2 hne => hdist c (hsub c hc) c' (hsub c' hc') h1 h2 hne
            rep := rep k1 k2
            hrep := hmem
            hinh := hinh
            hsepP := hsepP
            hsp := fun c hc c' hc' hne => ?_ }, rfl⟩
  -- the blocks are `K`-spaced
  obtain ⟨q, hq⟩ := Int.dvd_sub (hblk c (hsub c hc)) (hblk c' (hsub c' hc'))
  have hq' : c.1 - c'.1 = S.K * q := by rw [← hq]; ring
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hne (by linarith [hq'])
  rcases lt_or_gt_of_ne hq0 with hlt | hgt
  · left
    have : q ≤ -1 := by omega
    have : (S.K : ℤ) * q ≤ S.K * (-1) := mul_le_mul_of_nonneg_left this hK
    linarith
  · right
    have : 1 ≤ q := by omega
    have : (S.K : ℤ) * 1 ≤ S.K * q := mul_le_mul_of_nonneg_left this hK
    linarith


open Classical in
/-- Blueprint lines 2172-2174 (successful components and their good modes): the modes alive at the
decision cell of the pre-cell `J` of the block `b` that are good at height `h`, lie in a CURRENT
component containing a core mode good at `h` (a successful component), and have the least index
among the good modes of their component: one good mode for each successful component. -/
noncomputable def paperSuccModes (SP : SideParams) (b : ℤ) (J : ℤ × ℤ) (h : ℕ) :
    Finset (Ms.alive (ancAt Gd J (b - 4 * S.K))) :=
  Finset.univ.filter fun x => (Ms.blockComps S hA b J).PaperGood SP.Δ (Ms.goodP S SP b) h x ∧
    (∃ y ∈ (Ms.blockComps S hA b J).F h x,
      (Ms.blockComps S hA b J).PaperCore SP.Δ (Ms.goodP S SP b) SP.Jst SP.δs y ∧
        (Ms.blockComps S hA b J).PaperGood SP.Δ (Ms.goodP S SP b) h y) ∧
    ∀ y ∈ (Ms.blockComps S hA b J).F h x,
      (Ms.blockComps S hA b J).PaperGood SP.Δ (Ms.goodP S SP b) h y → Ms.modeIdx x.1 ≤ Ms.modeIdx y.1

open Classical in
/-- The nodes `(b, J, m)` of the successful components over a set `P` of pairs (block, pre-cell). -/
noncomputable def paperSuccNodes (SP : SideParams) (P : Finset (ℤ × (ℤ × ℤ))) (h : ℕ) :
    Finset (ℤ × (ℤ × ℤ) × Ms.Md) :=
  P.biUnion fun bJ => (Ms.paperSuccModes S hA SP bJ.1 bJ.2 h).image fun x => (bJ.1, bJ.2, x.1)

theorem mem_paperSuccNodes {SP : SideParams} {P : Finset (ℤ × (ℤ × ℤ))} {h : ℕ}
    {c : ℤ × (ℤ × ℤ) × Ms.Md} :
    c ∈ Ms.paperSuccNodes S hA SP P h ↔
      ∃ bJ ∈ P, ∃ x ∈ Ms.paperSuccModes S hA SP bJ.1 bJ.2 h, c = (bJ.1, bJ.2, x.1) := by
  classical
  unfold paperSuccNodes
  simp only [Finset.mem_biUnion, Finset.mem_image]
  exact exists_congr fun bJ => and_congr_right fun _ =>
    exists_congr fun x => and_congr_right fun _ => eq_comm

open Classical in
/-- The successful nodes are alive, of depth `v_b`, good, and distinct nodes on one pre-cell lie in
different CURRENT components (the node hypotheses of `exists_paperRepClass`). -/
theorem paperSuccNodes_props (SP : SideParams) (P : Finset (ℤ × (ℤ × ℤ)))
    (hP : ∀ bJ ∈ P, bJ.2.1 = bJ.1 - 2 * S.K) (h : ℕ) :
    ∃ halive : ∀ c ∈ Ms.paperSuccNodes S hA SP P h,
        c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)),
      (∀ c ∈ Ms.paperSuccNodes S hA SP P h, c.2.1.1 = c.1 - 2 * S.K) ∧
      (∀ c (hc : c ∈ Ms.paperSuccNodes S hA SP P h),
        (Ms.blockComps S hA c.1 c.2.1).PaperGood SP.Δ (Ms.goodP S SP c.1) h ⟨c.2.2, halive c hc⟩) ∧
      (∀ c (hc : c ∈ Ms.paperSuccNodes S hA SP P h) c' (hc' : c' ∈ Ms.paperSuccNodes S hA SP P h)
        (h1 : c.1 = c'.1) (h2 : c.2.1 = c'.2.1), c ≠ c' →
        (⟨c'.2.2, by rw [h1, h2]; exact halive c' hc'⟩ :
          Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K))) ∉
          (Ms.blockComps S hA c.1 c.2.1).F h ⟨c.2.2, halive c hc⟩) := by
  have halive : ∀ c ∈ Ms.paperSuccNodes S hA SP P h,
      c.2.2 ∈ Ms.alive (ancAt Gd c.2.1 (c.1 - 4 * S.K)) := by
    intro c hc
    obtain ⟨bJ, -, x, -, rfl⟩ := (Ms.mem_paperSuccNodes S hA).mp hc
    exact x.2
  refine ⟨halive, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨bJ, hbJ, x, -, rfl⟩ := (Ms.mem_paperSuccNodes S hA).mp hc
    exact hP bJ hbJ
  · intro c hc
    obtain ⟨bJ, -, x, hx, rfl⟩ := (Ms.mem_paperSuccNodes S hA).mp hc
    exact (Finset.mem_filter.mp hx).2.1
  · intro c hc c' hc' h1 h2 hne
    obtain ⟨bJ, -, x, hx, rfl⟩ := (Ms.mem_paperSuccNodes S hA).mp hc
    obtain ⟨bJ', -, x', hx', rfl⟩ := (Ms.mem_paperSuccNodes S hA).mp hc'
    obtain ⟨b, J⟩ := bJ
    obtain ⟨b', J'⟩ := bJ'
    simp only at h1 h2 x hx x' hx' hne ⊢
    subst h1 h2
    intro hmem
    have hmem' : x' ∈ (Ms.blockComps S hA b J).F h x := hmem
    obtain ⟨-, hxg, -, hxmin⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hx'g, -, hx'min⟩ := Finset.mem_filter.mp hx'
    have hF := (Ms.blockComps S hA b J).F_comp h x x' hmem'
    have i1 := hxmin x' hmem' hx'g
    have i2 := hx'min x (by
      rw [hF]; exact (Ms.blockComps S hA b J).E_le_F _ _ ((Ms.blockComps S hA b J).E_self _ _)) hxg
    have he : x.1 = x'.1 := Ms.modeIdx_injective (le_antisymm i1 i2)
    exact hne (by rw [he])

end ModeSystem

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

/-- Every CURRENT component containing a paper-core mode good at h has a chosen
successful mode in the paper-specific enumeration, with the same CURRENT component. -/
open Classical in
theorem paperSuccModes_cover {b : ℤ} {J : ℤ × ℤ} {h : ℕ}
    (x : Ms.alive (ancAt Gd J (b - 4 * S.K)))
    (hc : (Ms.blockComps S hA b J).PaperCore SP.Δ (Ms.goodP S SP b) SP.Jst SP.δs x)
    (hg : (Ms.blockComps S hA b J).PaperGood SP.Δ (Ms.goodP S SP b) h x) :
    ∃ y ∈ Ms.paperSuccModes S hA SP b J h,
      (Ms.blockComps S hA b J).F h y = (Ms.blockComps S hA b J).F h x := by
  let C := Ms.blockComps S hA b J
  let U := (C.F h x).filter (fun y => C.PaperGood SP.Δ (Ms.goodP S SP b) h y)
  have hx : x ∈ U := Finset.mem_filter.mpr ⟨C.E_le_F h x (C.E_self h x), hg⟩
  obtain ⟨y, hy, hmin⟩ := U.exists_min_image (fun y => Ms.modeIdx y.1) ⟨x, hx⟩
  obtain ⟨hyF, hyg⟩ := Finset.mem_filter.mp hy
  have hF : C.F h y = C.F h x := by
    have he := C.F_comp h x y hyF
    first | exact he | exact he.symm
  refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyg, ?_, ?_⟩, hF⟩
  · refine ⟨x, ?_, hc, hg⟩
    change x ∈ C.F h y
    rw [hF]
    exact C.E_le_F h x (C.E_self h x)
  · intro z hz hzg
    apply hmin
    apply Finset.mem_filter.mpr
    refine ⟨?_, hzg⟩
    change z ∈ C.F h y at hz
    rwa [hF] at hz

variable {Ms S hA SP}

/-- The role-frequency separation required by the progression tests, for the
actual base-1.1 representative class rather than a dyadic type class. -/
theorem PaperRepClass.role_label_sep {Δ h : ℕ} (R : Ms.PaperRepClass S hA SP Δ h)
    (hΛ : 8 * Ms.Λ ≤ S.Ξ) {xs : ℝ}
    (hxs : ∀ c ∈ R.Nd, xs ∈ dyadicGridCell Gd c.2.1.1 c.2.1.2)
    {c c' : ℤ × (ℤ × ℤ) × Ms.Md} (hc : c ∈ R.Nd) (hc' : c' ∈ R.Nd)
    (hne : R.rep c ≠ R.rep c')
    (n : Fin Ms.zc.dim → ℤ) (hn : ∀ i, |(n i : ℝ)| ≤ S.Eh h)
    {rI rI' : ℝ}
    (hrI : dyadicGridLength Gd (max c.1 c'.1 + S.K) ≤ rI)
    (hrI' : dyadicGridLength Gd (max c.1 c'.1 + S.K) ≤ rI') :
    S.Ξ / 2 * max rI⁻¹ rI'⁻¹ < |Ms.slope (R.rep c) xs - Ms.slope (R.rep c') xs +
      (∑ i, (n i : ℝ) * (Ms.zc.θ i / S.Q0)) / ModeSchedule.Lh h| :=
  Ms.role_label_separation3 S hA R.Nd R.hNd Δ h R.halive R.hdist R.rep R.hrep
    R.hsepP hΛ hxs hc hc' hne n hn hrI hrI'

end ModeSystem

end Auto

#print axioms Auto.ModeSystem.paper_size_comparison
#print axioms Auto.ModeSystem.paper_side_comparison
#print axioms Auto.ModeSystem.paper_sum_sideEvents_eq
#print axioms Auto.ModeSystem.paper_restrict_blockSide
#print axioms Auto.ModeSystem.paper_restrict_blockSide_actual
#print axioms Auto.ModeSystem.paper_side_comparison_block
#print axioms Auto.ModeSystem.paper_pred_nested_of_link
#print axioms Auto.ModeSystem.paper_comp_cross_sep
#print axioms Auto.ModeSystem.paper_firstTops_pair_sep
#print axioms Auto.ModeSystem.PaperRepClass.pair_sep
#print axioms Auto.ModeSystem.PaperRepClass.topRow_injOn
#print axioms Auto.ModeSystem.PaperRepClass.firstTops_rows
#print axioms Auto.ModeSystem.PaperRepClass.tops_side
#print axioms Auto.ModeSystem.paperNodeSize_eq
#print axioms Auto.ModeSystem.PaperRepClass.tops_absorb
#print axioms Auto.ModeSystem.exists_paperRepClass
#print axioms Auto.ModeSystem.mem_paperSuccNodes
#print axioms Auto.ModeSystem.paperSuccNodes_props
#print axioms Auto.ModeSystem.paperSuccModes_cover
#print axioms Auto.ModeSystem.PaperRepClass.role_label_sep
