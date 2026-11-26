import TrilinearHT.Auto.Sec14_5bExportedSideEstimate

/-! Proposition 7.5: unclipped power cost, on the actual reference pattern
expansion. The reference's clipped estimate is not used as a substitute for
an unclipped bound. Based on Roos/Claude, Apache-2.0. -/
namespace OpenAI086.ReferenceV67
open Auto
open scoped Classical BigOperators

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The retained path cap implies every individual side size is bounded by
`sqrt T`, even when the number of cells and groups is unrestricted. -/
theorem side_size_of_path (Gd : RealDyadicGrid) {γ : Type*} (S : Finset (ℤ × ℤ))
    (Gs : ℤ × ℤ → Finset γ) (s : ℤ × ℤ → γ → Fin 4 → W) {T : ℝ}
    (hT : ∀ x : ℝ, ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell Gd I.1 I.2),
      ∑ G ∈ Gs I, ∑ l, ‖s I G l‖ ^ 2 / dyadicGridLength Gd I.1 ≤ T)
    {I : ℤ × ℤ} (hI : I ∈ S) {G : γ} (hG : G ∈ Gs I) (l : Fin 4) :
    ‖s I G l‖ ≤ Real.sqrt T * Real.sqrt (dyadicGridLength Gd I.1) := by
  classical
  have hr := dyadicGridLength_pos Gd I.1
  have hmem : I ∈ S.filter (fun J => dyadicGridLeft Gd I.1 I.2 ∈ dyadicGridCell Gd J.1 J.2) :=
    Finset.mem_filter.mpr ⟨hI, dyadicGridCell_left_mem Gd I.1 I.2⟩
  have h1 : ‖s I G l‖ ^ 2 / dyadicGridLength Gd I.1 ≤
      ∑ j, ‖s I G j‖ ^ 2 / dyadicGridLength Gd I.1 :=
    Finset.single_le_sum (fun j _ => div_nonneg (sq_nonneg _) hr.le) (Finset.mem_univ l)
  have h2 : (∑ j, ‖s I G j‖ ^ 2 / dyadicGridLength Gd I.1) ≤
      ∑ g ∈ Gs I, ∑ j, ‖s I g j‖ ^ 2 / dyadicGridLength Gd I.1 :=
    Finset.single_le_sum (fun g _ => Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) hr.le) hG
  have h3 : (∑ g ∈ Gs I, ∑ j, ‖s I g j‖ ^ 2 / dyadicGridLength Gd I.1) ≤
      ∑ J ∈ S.filter (fun J => dyadicGridLeft Gd I.1 I.2 ∈ dyadicGridCell Gd J.1 J.2),
        ∑ g ∈ Gs J, ∑ j, ‖s J g j‖ ^ 2 / dyadicGridLength Gd J.1 :=
    Finset.single_le_sum (fun J _ => Finset.sum_nonneg fun g _ =>
      Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (dyadicGridLength_pos Gd J.1).le) hmem
  have h4 := (h1.trans (h2.trans (h3.trans (hT (dyadicGridLeft Gd I.1 I.2)))))
  have hT0 : 0 ≤ T := (div_nonneg (sq_nonneg _) hr.le).trans h4
  have hs := (div_le_iff₀ hr).mp h4
  rw [← Real.sqrt_mul hT0]
  exact Real.le_sqrt_of_sq_le hs

/-- Unclipped version of the reference three-side pattern estimate. The
fourth argument is bounded by `Bc`; side sizes follow from the same path cap. -/
theorem three_side_power (Gd : RealDyadicGrid) {γ : Type*} (S : Finset (ℤ × ℤ))
    (root : ℤ × ℤ) (hroot : ∀ I ∈ S, dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd root.1 root.2)
    (Gs : ℤ × ℤ → Finset γ) (Λ : ℤ × ℤ → MultilinearMap ℂ (fun _ : Fin 4 => W) ℂ)
    {C Bc : ℝ} (hC : 0 ≤ C) (hBc : 0 ≤ Bc)
    (hΛ : ∀ I ∈ S, ∀ x : Fin 4 → W, ‖Λ I x‖ ≤
      C * ∏ l, (‖x l‖ / Real.sqrt (dyadicGridLength Gd I.1)))
    (a s e : ℤ × ℤ → γ → Fin 4 → W)
    (hcore : ∀ I ∈ S, ∀ G ∈ Gs I, ∀ l, ‖a I G l‖ ≤ Bc * Real.sqrt (dyadicGridLength Gd I.1))
    {T : ℝ} (hT : ∀ x : ℝ, ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell Gd I.1 I.2),
      ∑ G ∈ Gs I, ∑ l, ‖s I G l‖ ^ 2 / dyadicGridLength Gd I.1 ≤ T)
    {p : ℝ} (hp : 2 / 3 < p) :
    ∑ I ∈ S, dyadicGridLength Gd I.1 * (∑ σ ∈ Finset.univ.filter
        (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧ 3 ≤ patternCount σ 1),
          ‖∑ G ∈ Gs I, Λ I (patternPiece (a I G) (s I G) (e I G) σ)‖) ^ p ≤
      (81 * C * max Bc (Real.sqrt T)) ^ p *
        (T ^ (p / 2) * T ^ (p / 2) * T ^ (p / 2) * dyadicGridLength Gd root.1) := by
  classical
  let Bs := max Bc (Real.sqrt T)
  have hBs : 0 ≤ Bs := hBc.trans (le_max_left _ _)
  have hsize : ∀ I ∈ S, ∀ G ∈ Gs I, ∀ l, ‖a I G l‖ ≤ Bs * Real.sqrt (dyadicGridLength Gd I.1) ∧
      ‖s I G l‖ ≤ Bs * Real.sqrt (dyadicGridLength Gd I.1) := by
    intro I hI G hG l
    exact ⟨(hcore I hI G hG l).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)),
      (side_size_of_path Gd S Gs s hT hI hG l).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))⟩
  let u : ℤ × ℤ → ℝ := fun I => ∑ G ∈ Gs I, ∑ l, ‖s I G l‖ ^ 2 / dyadicGridLength Gd I.1
  have hu : ∀ I, 0 ≤ u I := fun I => Finset.sum_nonneg fun G _ =>
    Finset.sum_nonneg fun l _ => div_nonneg (sq_nonneg _) (dyadicGridLength_pos Gd I.1).le
  let F := Finset.univ.filter (fun σ : Fin 4 → Fin 3 => (∀ l, σ l ≠ 2) ∧ 3 ≤ patternCount σ 1)
  let X : ℤ × ℤ → ℝ := fun I => ∑ σ ∈ F, ‖∑ G ∈ Gs I, Λ I (patternPiece (a I G) (s I G) (e I G) σ)‖
  have hcard : F.card ≤ 81 := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  have hX0 : ∀ I, 0 ≤ X I := fun I => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hX : ∀ I ∈ S, X I ≤ 81 * C * Bs * (Real.sqrt (u I) * Real.sqrt (u I) * Real.sqrt (u I)) := by
    intro I hI
    calc X I ≤ ∑ _σ ∈ F, C * Bs * (u I * Real.sqrt (u I)) :=
          Finset.sum_le_sum fun σ hσ => three_side_pattern_cell Gd I (Gs I) (Λ I) hC (hΛ I hI)
            (a I) (s I) (e I) (hsize I hI) (Finset.mem_filter.mp hσ).2
      _ ≤ 81 * (C * Bs * (u I * Real.sqrt (u I))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by have := hu I; positivity)
      _ = _ := by rw [Real.mul_self_sqrt (hu I)]; ring
  have hpc := power_cost_bound Gd S (fun I => Real.sqrt (u I)) (fun I => Real.sqrt (u I))
    (fun I => Real.sqrt (u I)) (fun I _ => Real.sqrt_nonneg _) (fun I _ => Real.sqrt_nonneg _)
    (fun I _ => Real.sqrt_nonneg _) root hroot (Ca := T) (Cb := T) (Cc := T)
    (fun y => by simp_rw [Real.sq_sqrt (hu _)]; exact hT y)
    (fun y => by simp_rw [Real.sq_sqrt (hu _)]; exact hT y)
    (fun y => by simp_rw [Real.sq_sqrt (hu _)]; exact hT y) hp
  have hp0 : 0 ≤ p := by linarith
  change ∑ I ∈ S, dyadicGridLength Gd I.1 * X I ^ p ≤ _
  calc _ ≤ ∑ I ∈ S, dyadicGridLength Gd I.1 * ((81 * C * Bs) ^ p *
        (Real.sqrt (u I) * Real.sqrt (u I) * Real.sqrt (u I)) ^ p) := by
      refine Finset.sum_le_sum fun I hI => mul_le_mul_of_nonneg_left ?_ (dyadicGridLength_pos Gd I.1).le
      rw [← Real.mul_rpow (by positivity : 0 ≤ 81 * C * Bs) (by positivity)]
      exact Real.rpow_le_rpow (hX0 I) (hX I hI) hp0
    _ = (81 * C * Bs) ^ p * ∑ I ∈ S, dyadicGridLength Gd I.1 *
        (Real.sqrt (u I) * Real.sqrt (u I) * Real.sqrt (u I)) ^ p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpc (by positivity)

end OpenAI086.ReferenceV67
#print axioms OpenAI086.ReferenceV67.side_size_of_path
#print axioms OpenAI086.ReferenceV67.three_side_power
