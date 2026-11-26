/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license (LICENSE-REFERENCE-APACHE2).
Original authors: Claude. Adapted from the pinned reference snapshot;
new paper-facing deductions marked V60.
-/
import Mathlib

namespace OpenAI086.SourceV60
open scoped BigOperators ComplexConjugate

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem sum_norm_le_sqrt_card_mul {ν : Type*} (N : Finset ν) (γ : ν → ℂ) :
    ∑ n ∈ N, ‖γ n‖ ≤ Real.sqrt N.card * Real.sqrt (∑ n ∈ N, ‖γ n‖ ^ 2) := by
  have := Real.sum_mul_le_sqrt_mul_sqrt N (fun _ => (1 : ℝ)) (fun n => ‖γ n‖)
  simpa using this


theorem mode_combination_cross_le {μ μ' : Type*} (M : Finset μ) (M' : Finset μ')
    (β : μ → ℂ) (β' : μ' → ℂ) (x : μ → μ' → ℂ) {ε L : ℝ} (hεL : 0 ≤ ε * L)
    (hx : ∀ m ∈ M, ∀ m' ∈ M', ‖x m m'‖ ≤ ε * L) :
    ‖∑ m ∈ M, ∑ m' ∈ M', β m * β' m' * x m m'‖ ≤
      ε * L * (Real.sqrt M.card * Real.sqrt (∑ m ∈ M, ‖β m‖ ^ 2)) *
        (Real.sqrt M'.card * Real.sqrt (∑ m' ∈ M', ‖β' m'‖ ^ 2)) := by
  calc ‖∑ m ∈ M, ∑ m' ∈ M', β m * β' m' * x m m'‖ ≤
        ∑ m ∈ M, ∑ m' ∈ M', ‖β m‖ * ‖β' m'‖ * (ε * L) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m' hm' => ?_)
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hx m hm m' hm') (by positivity)
    _ = ε * L * ((∑ m ∈ M, ‖β m‖) * (∑ m' ∈ M', ‖β' m'‖)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m' _
        ring
    _ ≤ ε * L * ((Real.sqrt M.card * Real.sqrt (∑ m ∈ M, ‖β m‖ ^ 2)) *
          (Real.sqrt M'.card * Real.sqrt (∑ m' ∈ M', ‖β' m'‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (sum_norm_le_sqrt_card_mul M β)
          (sum_norm_le_sqrt_card_mul M' β') (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          (by positivity)) hεL
    _ = _ := by ring


theorem almost_orthogonal_synthesis {κ : Type*} (s : Finset κ) (v : κ → H)
    (b ℓ : κ → ℝ) (w : κ → κ → ℝ) {D η : ℝ} (hη : 0 ≤ η) (hD : 0 ≤ D)
    (hw0 : ∀ e e', 0 ≤ w e e') (hws : ∀ e e', w e e' = w e' e)
    (hcross : ∀ e ∈ s, ∀ e' ∈ s, e ≠ e' → ‖inner ℂ (v e) (v e')‖ ≤ η * w e e' * b e * b e')
    (hmult : ∀ e ∈ s, ∑ e' ∈ s, w e e' ≤ D * ℓ e)
    (hdiag : ∀ e ∈ s, ℓ e * b e ^ 2 ≤ D ^ 2 * ‖v e‖ ^ 2) :
    ‖∑ e ∈ s, v e‖ ^ 2 ≤ (1 + η * D ^ 3) * ∑ e ∈ s, ‖v e‖ ^ 2 := by
  classical
  have hexp : ‖∑ e ∈ s, v e‖ ^ 2 =
      ∑ e ∈ s, ∑ e' ∈ s, RCLike.re (inner ℂ (v e) (v e')) := by
    rw [@norm_sq_eq_re_inner ℂ, sum_inner]
    simp only [inner_sum, map_sum]
  have hpt : ∀ e ∈ s, ∀ e' ∈ s, RCLike.re (inner ℂ (v e) (v e')) ≤
      (if e = e' then ‖v e‖ ^ 2 else 0) + η * (w e e' * ((b e ^ 2 + b e' ^ 2) / 2)) := by
    intro e he e' he'
    have hw2 : 0 ≤ η * (w e e' * ((b e ^ 2 + b e' ^ 2) / 2)) := by
      have := hw0 e e'; positivity
    split_ifs with hee
    · subst hee
      rw [← @norm_sq_eq_re_inner ℂ]
      linarith only [hw2]
    · have h1 := (RCLike.re_le_norm (inner ℂ (v e) (v e'))).trans (hcross e he e' he' hee)
      have h2 : b e * b e' ≤ (b e ^ 2 + b e' ^ 2) / 2 := by nlinarith [sq_nonneg (b e - b e')]
      have h3 : η * w e e' * b e * b e' ≤ η * (w e e' * ((b e ^ 2 + b e' ^ 2) / 2)) := by
        have := mul_le_mul_of_nonneg_left h2 (mul_nonneg hη (hw0 e e'))
        linarith
      linarith
  have hsym : ∑ e ∈ s, ∑ e' ∈ s, w e e' * ((b e ^ 2 + b e' ^ 2) / 2) =
      ∑ e ∈ s, ∑ e' ∈ s, w e e' * b e ^ 2 := by
    have hswap : ∑ e ∈ s, ∑ e' ∈ s, w e e' * b e' ^ 2 = ∑ e ∈ s, ∑ e' ∈ s, w e e' * b e ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro e _
      apply Finset.sum_congr rfl; intro e' _
      rw [hws]
    have hsplit : ∑ e ∈ s, ∑ e' ∈ s, w e e' * ((b e ^ 2 + b e' ^ 2) / 2) =
        (∑ e ∈ s, ∑ e' ∈ s, w e e' * b e ^ 2 + ∑ e ∈ s, ∑ e' ∈ s, w e e' * b e' ^ 2) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro e _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl; intro e' _
      ring
    rw [hsplit, hswap]; ring
  have hmain : ∑ e ∈ s, ∑ e' ∈ s, w e e' * b e ^ 2 ≤ D ^ 3 * ∑ e ∈ s, ‖v e‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro e he
    rw [← Finset.sum_mul]
    calc (∑ e' ∈ s, w e e') * b e ^ 2 ≤ D * ℓ e * b e ^ 2 :=
          mul_le_mul_of_nonneg_right (hmult e he) (sq_nonneg _)
      _ = D * (ℓ e * b e ^ 2) := by ring
      _ ≤ D * (D ^ 2 * ‖v e‖ ^ 2) := mul_le_mul_of_nonneg_left (hdiag e he) hD
      _ = D ^ 3 * ‖v e‖ ^ 2 := by ring
  calc ‖∑ e ∈ s, v e‖ ^ 2 ≤ ∑ e ∈ s, ∑ e' ∈ s,
        ((if e = e' then ‖v e‖ ^ 2 else 0) + η * (w e e' * ((b e ^ 2 + b e' ^ 2) / 2))) := by
        rw [hexp]
        exact Finset.sum_le_sum fun e he => Finset.sum_le_sum fun e' he' => hpt e he e' he'
    _ = ∑ e ∈ s, ‖v e‖ ^ 2 + η * ∑ e ∈ s, ∑ e' ∈ s, w e e' * ((b e ^ 2 + b e' ^ 2) / 2) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl; intro e he
        simp [he]
    _ ≤ (1 + η * D ^ 3) * ∑ e ∈ s, ‖v e‖ ^ 2 := by
        rw [hsym]
        nlinarith [mul_le_mul_of_nonneg_left hmain hη]


theorem rows_bessel_of_synthesis {κ : Type*} (s : Finset κ) (g : κ → H) (F : H) {C : ℝ}
    (hC : 0 ≤ C) (hproj : ∀ e ∈ s, RCLike.re (inner ℂ (g e) F) = ‖g e‖ ^ 2)
    (hsyn : ‖∑ e ∈ s, g e‖ ^ 2 ≤ C * ∑ e ∈ s, ‖g e‖ ^ 2) :
    ∑ e ∈ s, ‖g e‖ ^ 2 ≤ C * ‖F‖ ^ 2 := by
  set E := ∑ e ∈ s, ‖g e‖ ^ 2
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE : E = RCLike.re (inner ℂ (∑ e ∈ s, g e) F) := by
    rw [sum_inner, map_sum]
    exact (Finset.sum_congr rfl hproj).symm
  have hle : E ≤ ‖∑ e ∈ s, g e‖ * ‖F‖ := by
    rw [hE]; exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hsq : E ^ 2 ≤ C * E * ‖F‖ ^ 2 := by
    calc E ^ 2 ≤ (‖∑ e ∈ s, g e‖ * ‖F‖) ^ 2 := pow_le_pow_left₀ hE0 hle 2
      _ = ‖∑ e ∈ s, g e‖ ^ 2 * ‖F‖ ^ 2 := by ring
      _ ≤ C * E * ‖F‖ ^ 2 := mul_le_mul_of_nonneg_right hsyn (sq_nonneg _)
  rcases hE0.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · nlinarith


theorem proj_complement_le {μ : Type*} (E A : Finset μ) (Ψ : μ → H)
    [(Submodule.span ℂ (Ψ '' (E : Set μ))).HasOrthogonalProjection] (β : μ → ℂ) {η L ε ℓ : ℝ}
    (hηL : 0 ≤ η * L) (hεℓ : 0 < ε * ℓ)
    (hpair : ∀ m ∈ E, ∀ m' ∈ A, ‖inner ℂ (Ψ m) (Ψ m')‖ ≤ η * L)
    (hpriv : ∀ c : μ → ℂ, ε * ℓ * ∑ m ∈ E, ‖c m‖ ^ 2 ≤ ‖∑ m ∈ E, c m • Ψ m‖ ^ 2) :
    ‖(Submodule.span ℂ (Ψ '' (E : Set μ))).starProjection (∑ m' ∈ A, β m' • Ψ m')‖ ≤
      η * L * (Real.sqrt E.card * (Real.sqrt A.card * Real.sqrt (∑ m' ∈ A, ‖β m'‖ ^ 2))) /
        Real.sqrt (ε * ℓ) := by
  classical
  set K := Submodule.span ℂ (Ψ '' (E : Set μ))
  set w := ∑ m' ∈ A, β m' • Ψ m'
  set g := K.starProjection w
  have hg : g ∈ K := Submodule.starProjection_apply_mem _ _
  rw [Submodule.mem_span_image_finset_iff_exists_fun'] at hg
  obtain ⟨c, hc⟩ := hg
  have hre : ‖g‖ ^ 2 = RCLike.re (inner ℂ g w) := by
    have := K.re_inner_starProjection_eq_normSq w
    rw [this, ← Submodule.norm_coe, ← Submodule.starProjection_apply]
  have hin : inner ℂ g w = ∑ m ∈ E, ∑ m' ∈ A, (starRingEnd ℂ) (c m) * β m' *
      inner ℂ (Ψ m) (Ψ m') := by
    rw [← hc, sum_inner]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [inner_smul_left, inner_smul_right]; ring
  have hcross := mode_combination_cross_le E A (fun m => (starRingEnd ℂ) (c m)) β
    (fun m m' => inner ℂ (Ψ m) (Ψ m')) hηL hpair
  simp only [RCLike.norm_conj] at hcross
  set X := η * L * (Real.sqrt E.card * (Real.sqrt A.card * Real.sqrt (∑ m' ∈ A, ‖β m'‖ ^ 2)))
  have hX0 : 0 ≤ X := by positivity
  have hcg : Real.sqrt (∑ m ∈ E, ‖c m‖ ^ 2) ≤ ‖g‖ / Real.sqrt (ε * ℓ) := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hεℓ), ← Real.sqrt_mul' _ hεℓ.le]
    rw [show ‖g‖ = Real.sqrt (‖g‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    refine Real.sqrt_le_sqrt ?_
    have := hpriv c; rw [hc] at this; linarith
  have h1 : ‖g‖ ^ 2 ≤ X * (‖g‖ / Real.sqrt (ε * ℓ)) := by
    rw [hre]
    refine (RCLike.re_le_norm _).trans ?_
    rw [hin]
    refine hcross.trans ?_
    have hs := Real.sqrt_nonneg (∑ m ∈ E, ‖c m‖ ^ 2)
    calc η * L * (Real.sqrt E.card * Real.sqrt (∑ m ∈ E, ‖c m‖ ^ 2)) *
          (Real.sqrt A.card * Real.sqrt (∑ m' ∈ A, ‖β m'‖ ^ 2)) =
        X * Real.sqrt (∑ m ∈ E, ‖c m‖ ^ 2) := by simp only [X]; ring
      _ ≤ X * (‖g‖ / Real.sqrt (ε * ℓ)) := mul_le_mul_of_nonneg_left hcg hX0
  have hs := Real.sqrt_pos.mpr hεℓ
  rcases (norm_nonneg g).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · rw [le_div_iff₀ hs]
    have : ‖g‖ * ‖g‖ ≤ ‖g‖ * (X / Real.sqrt (ε * ℓ)) := by
      rw [← sq]; refine h1.trans (le_of_eq ?_); ring
    have := le_of_mul_le_mul_left this hpos
    rwa [le_div_iff₀ hs] at this


theorem subtotals_almost_orthogonal {μ ι : Type*} (s : Finset ι) (E : ι → Finset μ)
    (Ψ : μ → H) (β : μ → ℂ) {η L ε D : ℝ} (hη : 0 ≤ η) (hL : 0 ≤ L) (hε : 0 < ε) (hD : 0 ≤ D)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ m ∈ E i, ∀ m' ∈ E j,
      ‖inner ℂ (Ψ m) (Ψ m')‖ ≤ η * L)
    (hpriv : ∀ i ∈ s, ε * L * ∑ m ∈ E i, ‖β m‖ ^ 2 ≤ ‖∑ m ∈ E i, β m • Ψ m‖ ^ 2)
    (hnum : (s.card : ℝ) ≤ D) (hcard : ∀ i ∈ s, ((E i).card : ℝ) ≤ ε * D ^ 2) :
    ‖∑ i ∈ s, ∑ m ∈ E i, β m • Ψ m‖ ^ 2 ≤
      (1 + η * D ^ 3) * ∑ i ∈ s, ‖∑ m ∈ E i, β m • Ψ m‖ ^ 2 := by
  classical
  set b : ι → ℝ := fun i => Real.sqrt (E i).card * Real.sqrt (∑ m ∈ E i, ‖β m‖ ^ 2)
  refine almost_orthogonal_synthesis s (fun i => ∑ m ∈ E i, β m • Ψ m) b (fun _ => L)
    (fun _ _ => L) hη hD (fun _ _ => hL) (fun _ _ => rfl) (fun i hi j hj hij => ?_)
    (fun i _ => ?_) (fun i hi => ?_)
  · have hin : inner ℂ (∑ m ∈ E i, β m • Ψ m) (∑ m ∈ E j, β m • Ψ m) =
        ∑ m ∈ E i, ∑ m' ∈ E j, (starRingEnd ℂ) (β m) * β m' * inner ℂ (Ψ m) (Ψ m') := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [inner_sum]
      refine Finset.sum_congr rfl fun m' _ => ?_
      rw [inner_smul_left, inner_smul_right]; ring
    rw [hin]
    have h := mode_combination_cross_le (E i) (E j) (fun m => (starRingEnd ℂ) (β m)) β
      (fun m m' => inner ℂ (Ψ m) (Ψ m')) (mul_nonneg hη hL) (hpair i hi j hj hij)
    simp only [RCLike.norm_conj] at h
    refine h.trans (le_of_eq ?_)
    simp only [b]
  · rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hnum hL
  · have h1 := hpriv i hi
    have hs0 : 0 ≤ ∑ m ∈ E i, ‖β m‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hb2 : b i ^ 2 = (E i).card * ∑ m ∈ E i, ‖β m‖ ^ 2 := by
      simp only [b]; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hs0]
    rw [hb2]
    have hc0 : (0 : ℝ) ≤ (E i).card := Nat.cast_nonneg _
    have h3 : L * ∑ m ∈ E i, ‖β m‖ ^ 2 ≤ ‖∑ m ∈ E i, β m • Ψ m‖ ^ 2 / ε := by
      rw [le_div_iff₀ hε]; linarith
    calc L * ((E i).card * ∑ m ∈ E i, ‖β m‖ ^ 2) =
        (E i).card * (L * ∑ m ∈ E i, ‖β m‖ ^ 2) := by ring
      _ ≤ (E i).card * (‖∑ m ∈ E i, β m • Ψ m‖ ^ 2 / ε) := mul_le_mul_of_nonneg_left h3 hc0
      _ ≤ ε * D ^ 2 * (‖∑ m ∈ E i, β m • Ψ m‖ ^ 2 / ε) :=
          mul_le_mul_of_nonneg_right (hcard i hi) (div_nonneg (sq_nonneg _) hε.le)
      _ = D ^ 2 * ‖∑ m ∈ E i, β m • Ψ m‖ ^ 2 := by field_simp


theorem projection_subtotal_close {μ : Type*} [DecidableEq μ] (E A : Finset μ) (hEA : E ⊆ A)
    (Ψ : μ → H) [(Submodule.span ℂ (Ψ '' (E : Set μ))).HasOrthogonalProjection] (c : μ → ℂ)
    {η L ε ℓ : ℝ} (hηL : 0 ≤ η * L) (hεℓ : 0 < ε * ℓ)
    (hpair : ∀ m ∈ E, ∀ m' ∈ A \ E, ‖inner ℂ (Ψ m) (Ψ m')‖ ≤ η * L)
    (hpriv : ∀ c : μ → ℂ, ε * ℓ * ∑ m ∈ E, ‖c m‖ ^ 2 ≤ ‖∑ m ∈ E, c m • Ψ m‖ ^ 2) :
    ‖(Submodule.span ℂ (Ψ '' (E : Set μ))).starProjection (∑ m ∈ A, c m • Ψ m) -
        ∑ m ∈ E, c m • Ψ m‖ ≤
      η * L * (Real.sqrt E.card * (Real.sqrt (A \ E).card *
        Real.sqrt (∑ m' ∈ A \ E, ‖c m'‖ ^ 2))) / Real.sqrt (ε * ℓ) := by
  set K := Submodule.span ℂ (Ψ '' (E : Set μ))
  have hsplit : ∑ m ∈ A, c m • Ψ m = ∑ m ∈ E, c m • Ψ m + ∑ m ∈ A \ E, c m • Ψ m := by
    rw [← Finset.sum_sdiff hEA, add_comm]
  have hT : ∑ m ∈ E, c m • Ψ m ∈ K :=
    Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨m, hm, rfl⟩)
  rw [hsplit, map_add, Submodule.starProjection_eq_self_iff.mpr hT, add_sub_cancel_left]
  exact proj_complement_le E (A \ E) Ψ c hηL hεℓ hpair hpriv


end
end OpenAI086.SourceV60
#print axioms OpenAI086.SourceV60.sum_norm_le_sqrt_card_mul
#print axioms OpenAI086.SourceV60.mode_combination_cross_le
#print axioms OpenAI086.SourceV60.almost_orthogonal_synthesis
#print axioms OpenAI086.SourceV60.rows_bessel_of_synthesis
#print axioms OpenAI086.SourceV60.proj_complement_le
#print axioms OpenAI086.SourceV60.subtotals_almost_orthogonal
#print axioms OpenAI086.SourceV60.projection_subtotal_close
