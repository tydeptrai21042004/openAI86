import TrilinearHT.Auto.Sec13_5RepresentativesComponentSizesFirstTops

/-! Lemma 8.11 in normalized cell energy. The reference proves the two
inequalities separately in unnormalized L2. Here the same frozen coefficients
and the same actual cell are used in both, with the paper's Dstar^-50 error.
The stronger coefficient reserve is explicit, not asserted to follow from
all of the paper's earlier constructions. -/
namespace OpenAI086.ReferenceV69
open Auto
open scoped BigOperators

open Classical in
theorem normalized_component_comparison {Gd : RealDyadicGrid} {Mc : ℕ}
    (Ms : ModeSystem Gd Mc) (S : ModeSchedule) (hA : 6 ≤ S.A0) (SP : SideParams)
    {b : ℤ} {J I : ℤ × ℤ} (hJ : J.1 = b - 2 * S.K)
    (hIJ : dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd J.1 J.2)
    (hIt : I.1 ≤ b + S.K) (hD : 2 ≤ S.Dstar)
    (hδ : 0 < Ms.δc) (hΛ : Ms.Λ ≤ S.Dstar) (hQ0 : 0 < S.Q0) (Kf : ℕ)
    (hbox : (S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ S.Eh 0)
    (hDg : gaugeSqNorm Ms.zc.dim Ms.δc ≤ S.Dstar)
    (hKf : 2 * gaugeTail Ms.zc.dim Ms.δc / 2 ^ Kf * S.Dstar ^ 300 ≤ 1)
    (hεw : ∀ m, S.Dstar⁻¹ ≤ Ms.L.εM m)
    (halive : ((Ms.alive (ancAt Gd J (b - 4 * S.K))).card : ℝ) ≤ S.Dstar)
    (c : Ms.Md → ℂ) {Bc : ℝ}
    (hc : ∑ m ∈ Ms.alive (ancAt Gd J (b - 4 * S.K)), ‖c m‖ ^ 2 ≤ Bc)
    (hBc : 3 * Bc ≤ S.Dstar ^ 9)
    (h : ℕ) (x : Ms.alive (ancAt Gd J (b - 4 * S.K)))
    {Fs : Finset (Finset Ms.Md)} (hFs : Fs ⊆ Ms.curComps S hA b J h)
    [(Submodule.span ℂ ((Ms.cellMode I) ''
      (Ms.compModes S hA b J h x : Set Ms.Md))).HasOrthogonalProjection] :
    Ms.compSizeSq S hA SP I b J h x c ≤
      12 * ((‖(Submodule.span ℂ ((Ms.cellMode I) ''
          (Ms.compModes S hA b J h x : Set Ms.Md))).starProjection (Ms.frozenEval S b J c)‖ ^ 2 +
        ‖∑ m ∈ (Ms.compModes S hA b J h x).filter (fun m => ¬ Ms.IsCoreAt S hA SP b J m),
          c m • Ms.cellMode I m‖ ^ 2) / dyadicGridLength Gd I.1) + (S.Dstar ^ 50)⁻¹ ∧
    (∑ F ∈ Fs, (‖∑ m ∈ F.filter (fun m => ¬ Ms.IsCoreAt S hA SP b J m),
        c m • Ms.cellMode I m‖ ^ 2 / dyadicGridLength Gd I.1)) ≤
      2 * (‖∑ m ∈ (Ms.alive (ancAt Gd J (b - 4 * S.K))).filter
        (fun m => ¬ Ms.IsCoreAt S hA SP b J m), c m • Ms.cellMode I m‖ ^ 2 /
          dyadicGridLength Gd I.1) := by
  have hDp : 0 < S.Dstar := by linarith
  have hpow : 0 < S.Dstar ^ 59 := pow_pos hDp _
  have herr : 3 * Bc / S.Dstar ^ 59 ≤ (S.Dstar ^ 50)⁻¹ := by
    apply (div_le_iff₀ hpow).2
    have he : (S.Dstar ^ 50)⁻¹ * S.Dstar ^ 59 = S.Dstar ^ 9 := by
      rw [show S.Dstar ^ 59 = S.Dstar ^ 50 * S.Dstar ^ 9 by ring, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ hDp.ne'), one_mul]
    rw [he]
    exact hBc
  constructor
  · exact (Ms.size_comparison S hA SP hJ hIJ hIt hD hδ hΛ hQ0 Kf hbox hDg hKf
      hεw halive c hc h x).trans (add_le_add_left herr _)
  · have hside := Ms.side_comparison S hA SP hJ hIJ hIt hD hδ hΛ hQ0 Kf hbox hDg hKf
      hεw halive c h hFs
    have hr := dyadicGridLength_pos Gd I.1
    have hdiv := div_le_div_of_nonneg_right hside hr.le
    simpa only [Finset.sum_div, mul_div_assoc] using hdiv

/-- The actual reference frozen coefficient bound suffices for the printed
error provided the normalization reserve is 12 CF ≤ Dstar^7. -/
theorem coefficient_reserve {D CF Bc : ℝ} (hD : 2 ≤ D)
    (hc : Bc ≤ 4 * D ^ 2 * CF) (hCF : 12 * CF ≤ D ^ 7) :
    3 * Bc ≤ D ^ 9 := by
  calc
    3 * Bc ≤ 3 * (4 * D ^ 2 * CF) := by linarith
    _ = D ^ 2 * (12 * CF) := by ring
    _ ≤ D ^ 2 * D ^ 7 := mul_le_mul_of_nonneg_left hCF (sq_nonneg D)
    _ = D ^ 9 := by ring

end OpenAI086.ReferenceV69
#print axioms OpenAI086.ReferenceV69.normalized_component_comparison
#print axioms OpenAI086.ReferenceV69.coefficient_reserve
