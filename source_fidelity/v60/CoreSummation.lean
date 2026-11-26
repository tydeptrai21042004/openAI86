/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license (LICENSE-REFERENCE-APACHE2).
Original authors: Claude. Adapted from the pinned reference snapshot;
new paper-facing deductions marked V60.
-/
import Mathlib

namespace OpenAI086.SourceV60
open MeasureTheory Metric
open scoped BigOperators ENNReal

theorem min_le_rpow_mul {η x p : ℝ} (hη : 0 ≤ η) (hx : 0 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    min η x ≤ η ^ (1 - p) * x ^ p := by
  rcases le_total η x with h | h
  · rw [min_eq_left h]
    calc η = η ^ (1 - p) * η ^ p := by
          rcases hη.eq_or_lt with h0 | h0
          · rw [← h0]
            rcases hp0.eq_or_lt with hp | hp
            · rw [← hp]; simp
            · rw [Real.zero_rpow hp.ne', mul_zero]
          · rw [← Real.rpow_add h0]; simp
      _ ≤ η ^ (1 - p) * x ^ p :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hη h hp0) (Real.rpow_nonneg hη _)
  · rw [min_eq_right h]
    calc x = x ^ (1 - p) * x ^ p := by
          rcases hx.eq_or_lt with h0 | h0
          · rw [← h0]
            rcases hp0.eq_or_lt with hp | hp
            · rw [← hp]; simp
            · rw [Real.zero_rpow hp.ne', mul_zero]
          · rw [← Real.rpow_add h0]; simp
      _ ≤ η ^ (1 - p) * x ^ p :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx h (by linarith))
            (Real.rpow_nonneg hx _)


theorem rpow_one_sub_eq_integral {N ε : ℝ} (hN : 0 < N) (hε : 0 < ε) :
    N ^ (1 - ε) = ε * N * ∫ t in Set.Ioi N, t ^ (-1 - ε) := by
  rw [integral_Ioi_rpow_of_lt (by linarith only [hε]) hN]
  rw [show -1 - ε + 1 = -ε by ring, Real.rpow_sub hN, Real.rpow_one, Real.rpow_neg hN.le]
  field_simp


theorem distribution_power {ι : Type*} (s : Finset ι) (N : ι → ℝ) {M A B c ε : ℝ}
    (hM : 0 < M) (hN0 : ∀ i ∈ s, 0 ≤ N i) (hNM : ∀ i ∈ s, N i ≤ M ^ 2)
    (hA : ∑ i ∈ s, N i ≤ A) (hApos : 0 < A) (hBpos : 0 < B)
    (hsparse : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∑ i ∈ s.filter (fun i => N i ≤ δ * M ^ 2), N i ≤
      B * δ ^ c * M ^ 2)
    (hc0 : 0 < c) (hc1 : c < 1) (hε : 0 < ε) (hεc : ε < c) :
    ∑ i ∈ s, N i ^ (1 - ε) ≤
      c / (c - ε) * A ^ (1 - ε / c) * B ^ (ε / c) * M ^ (2 * ε * (1 / c - 1)) := by
  classical
  set K : ℝ := B * M ^ (2 - 2 * c) with hK
  have hKpos : 0 < K := by positivity
  -- the cumulative mass `F(t) = Σ_{N_s < t} N_s`
  set F : ℝ → ℝ := fun t => ∑ i ∈ s, (Set.Ioi (N i)).indicator (fun _ => N i) t
  have hF0 : ∀ t, 0 ≤ F t := fun t =>
    Finset.sum_nonneg fun i hi => Set.indicator_nonneg (fun _ _ => hN0 i hi) _
  have hFle : ∀ t, F t ≤ ∑ i ∈ s.filter (fun i => N i < t), N i := by
    intro t
    simp only [F, Finset.sum_filter]
    apply Finset.sum_le_sum; intro i hi
    by_cases h : N i < t
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have hFA : ∀ t, F t ≤ A := fun t =>
    (hFle t).trans ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i hi _ => hN0 i hi).trans hA)
  have hFK : ∀ t, 0 < t → F t ≤ K * t ^ c := by
    intro t ht
    by_cases htM : t ≤ M ^ 2
    · have hδ : 0 < t / M ^ 2 := by positivity
      have hδ1 : t / M ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact htM
      have hsub := hsparse (t / M ^ 2) hδ hδ1
      have hfil : ∑ i ∈ s.filter (fun i => N i < t), N i ≤
          ∑ i ∈ s.filter (fun i => N i ≤ t / M ^ 2 * M ^ 2), N i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter] at hi ⊢
          refine ⟨hi.1, ?_⟩
          rw [div_mul_cancel₀ _ (by positivity)]; exact hi.2.le
        · intro i hi _; exact hN0 i (Finset.mem_filter.mp hi).1
      refine (hFle t).trans (hfil.trans (hsub.trans (le_of_eq ?_)))
      rw [hK, Real.div_rpow ht.le (by positivity)]
      rw [show (M ^ 2) ^ c = M ^ (2 * c) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num]
      rw [show M ^ (2 - 2 * c) = M ^ 2 / M ^ (2 * c) by
        rw [Real.rpow_sub hM]; norm_num]
      field_simp
    · push Not at htM
      have hall : F t ≤ B * M ^ 2 := by
        have h1 := hsparse 1 one_pos le_rfl
        have heq : s.filter (fun i => N i ≤ 1 * M ^ 2) = s :=
          Finset.filter_true_of_mem fun i hi => by rw [one_mul]; exact hNM i hi
        rw [heq, Real.one_rpow, mul_one] at h1
        exact (hFle t).trans ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i hi _ => hN0 i hi).trans h1)
      refine hall.trans ?_
      have hMc : M ^ (2 * c) ≤ t ^ c := by
        rw [show M ^ (2 * c) = (M ^ 2) ^ c by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]; norm_num]
        exact Real.rpow_le_rpow (by positivity) htM.le hc0.le
      have e : B * M ^ 2 = K * M ^ (2 * c) := by
        rw [hK, mul_assoc, ← Real.rpow_add hM]; norm_num
      rw [e]
      exact mul_le_mul_of_nonneg_left hMc hKpos.le
  -- layer cake: `Σ N^{1-ε} = ε ∫_{(0,∞)} t^{-1-ε} F(t) dt`
  set g : ℝ → ℝ := fun t => t ^ (-1 - ε)
  set f : ι → ℝ → ℝ := fun i t => N i * (Set.Ioi (N i)).indicator g t
  have hfint : ∀ i ∈ s, IntegrableOn (f i) (Set.Ioi 0) := by
    intro i hi
    rcases (hN0 i hi).eq_or_lt with h0 | hpos
    · simp [f, ← h0]
    · refine Integrable.const_mul ?_ (N i)
      exact ((integrableOn_Ioi_rpow_of_lt (a := -1 - ε) (by linarith) hpos).integrable_indicator
        measurableSet_Ioi).integrableOn
  have hfi : ∀ i ∈ s, N i ^ (1 - ε) = ε * ∫ t in Set.Ioi 0, f i t := by
    intro i hi
    rcases (hN0 i hi).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith)]; simp [f, ← h0]
    · rw [rpow_one_sub_eq_integral hpos hε]
      simp only [f]
      rw [integral_const_mul, setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hpos.le)]
      ring
  have hsumf : ∀ t, ∑ i ∈ s, f i t = g t * F t := by
    intro t
    simp only [f, F, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : t ∈ Set.Ioi (N i)
    · simp [Set.indicator_of_mem h]; ring
    · simp [Set.indicator_of_notMem h]
  have hlayer : ∑ i ∈ s, N i ^ (1 - ε) = ε * ∫ t in Set.Ioi 0, g t * F t := by
    rw [Finset.sum_congr rfl hfi, ← Finset.mul_sum, ← integral_finsetSum _ hfint]
    simp_rw [hsumf]
  have hgFint : IntegrableOn (fun t => g t * F t) (Set.Ioi 0) := by
    have := integrable_finsetSum s hfint
    refine this.congr (Filter.Eventually.of_forall fun t => ?_)
    exact hsumf t
  -- split at `t₀ = (A/K)^{1/c}`
  set! t₀ : ℝ := (A / K) ^ (1 / c)
  have ht₀ : 0 < t₀ := by positivity
  have hKt₀ : K * t₀ ^ c = A := by
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hc0.ne', Real.rpow_one]
    field_simp
  have hsplit : ∫ t in Set.Ioi 0, g t * F t =
      (∫ t in Set.Ioc 0 t₀, g t * F t) + ∫ t in Set.Ioi t₀, g t * F t := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hgFint.mono_set Set.Ioc_subset_Ioi_self) (hgFint.mono_set (Set.Ioi_subset_Ioi ht₀.le)),
      Set.Ioc_union_Ioi_eq_Ioi ht₀.le]
  have hr : -1 < c - 1 - ε := by linarith
  have hint1 : IntegrableOn (fun t : ℝ => K * t ^ (c - 1 - ε)) (Set.Ioc 0 t₀) :=
    ((intervalIntegral.intervalIntegrable_rpow' hr).1).const_mul K
  have hint2 : IntegrableOn (fun t : ℝ => A * g t) (Set.Ioi t₀) :=
    (integrableOn_Ioi_rpow_of_lt (a := -1 - ε) (by linarith) ht₀).const_mul A
  have h1 : ∫ t in Set.Ioc 0 t₀, g t * F t ≤ ∫ t in Set.Ioc 0 t₀, K * t ^ (c - 1 - ε) := by
    apply setIntegral_mono_on (hgFint.mono_set Set.Ioc_subset_Ioi_self) hint1 measurableSet_Ioc
    intro t ht
    have htpos : 0 < t := ht.1
    have hg0 : 0 ≤ g t := Real.rpow_nonneg htpos.le _
    calc g t * F t ≤ g t * (K * t ^ c) := mul_le_mul_of_nonneg_left (hFK t htpos) hg0
      _ = K * t ^ (c - 1 - ε) := by
          simp only [g]
          rw [mul_left_comm, ← Real.rpow_add htpos]; ring_nf
  have h2 : ∫ t in Set.Ioi t₀, g t * F t ≤ ∫ t in Set.Ioi t₀, A * g t := by
    apply setIntegral_mono_on (hgFint.mono_set (Set.Ioi_subset_Ioi ht₀.le)) hint2
      measurableSet_Ioi
    intro t ht
    have hg0 : 0 ≤ g t := Real.rpow_nonneg (ht₀.trans ht).le _
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hFA t) hg0
  have hv1 : ∫ t in Set.Ioc 0 t₀, K * t ^ (c - 1 - ε) = K * t₀ ^ (c - ε) / (c - ε) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le ht₀.le,
      integral_rpow (Or.inl hr)]
    rw [show c - 1 - ε + 1 = c - ε by ring, Real.zero_rpow (by linarith)]
    ring
  have hv2 : ∫ t in Set.Ioi t₀, A * g t = A * t₀ ^ (-ε) / ε := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ht₀]
    rw [show -1 - ε + 1 = -ε by ring]
    field_simp
  have hKt : K * t₀ ^ (c - ε) = A * t₀ ^ (-ε) := by
    rw [sub_eq_add_neg, Real.rpow_add ht₀, ← mul_assoc, hKt₀]
  have hfinal : A * t₀ ^ (-ε) = A ^ (1 - ε / c) * B ^ (ε / c) * M ^ (2 * ε * (1 / c - 1)) := by
    have e1 : t₀ ^ (-ε) = K ^ (ε / c) / A ^ (ε / c) := by
      simp only [t₀]
      rw [← Real.rpow_mul (by positivity), show 1 / c * -ε = -(ε / c) by ring,
        Real.rpow_neg (by positivity), Real.div_rpow hApos.le hKpos.le, inv_div]
    have e2 : K ^ (ε / c) = B ^ (ε / c) * M ^ (2 * ε * (1 / c - 1)) := by
      rw [hK, Real.mul_rpow hBpos.le (by positivity), ← Real.rpow_mul hM.le]
      congr 2; field_simp
    have e3 : A ^ (1 - ε / c) = A / A ^ (ε / c) := by rw [Real.rpow_sub hApos, Real.rpow_one]
    have hApow : 0 < A ^ (ε / c) := by positivity
    rw [e1, e2, e3]; field_simp
  have hce : c - ε ≠ 0 := by linarith
  rw [hlayer, hsplit]
  calc ε * ((∫ t in Set.Ioc 0 t₀, g t * F t) + ∫ t in Set.Ioi t₀, g t * F t) ≤
      ε * (K * t₀ ^ (c - ε) / (c - ε) + A * t₀ ^ (-ε) / ε) := by
        rw [← hv1, ← hv2]; gcongr
    _ = c / (c - ε) * (A * t₀ ^ (-ε)) := by
        rw [hKt]; field_simp; ring
    _ = _ := by rw [hfinal]; ring


theorem sum_prod_rpow_le {κ ι : Type*} (I : Finset ι) (Gs : Finset κ) (m : ι → κ → ℝ)
    (β : ι → ℝ) (hm : ∀ i ∈ I, ∀ G ∈ Gs, 0 ≤ m i G) (hβ : ∀ i ∈ I, 0 < β i)
    (hb : 1 ≤ ∑ i ∈ I, β i) :
    ∑ G ∈ Gs, ∏ i ∈ I, m i G ^ β i ≤ ∏ i ∈ I, (∑ G ∈ Gs, m i G) ^ β i := by
  classical
  set S : ι → ℝ := fun i => ∑ G ∈ Gs, m i G
  have hS0 : ∀ i ∈ I, 0 ≤ S i := fun i hi => Finset.sum_nonneg fun G hG => hm i hi G hG
  -- a vanishing total makes every term vanish
  by_cases hz : ∃ i ∈ I, S i = 0
  · obtain ⟨i₀, hi₀, hS⟩ := hz
    have hzero : ∀ G ∈ Gs, m i₀ G = 0 := fun G hG =>
      le_antisymm ((Finset.single_le_sum (fun G' hG' => hm i₀ hi₀ G' hG') hG).trans hS.le)
        (hm i₀ hi₀ G hG)
    have hlhs : ∑ G ∈ Gs, ∏ i ∈ I, m i G ^ β i = 0 := by
      refine Finset.sum_eq_zero fun G hG => Finset.prod_eq_zero hi₀ ?_
      rw [hzero G hG, Real.zero_rpow (hβ i₀ hi₀).ne']
    rw [hlhs]
    exact Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hS0 i hi) _
  push Not at hz
  have hSpos : ∀ i ∈ I, 0 < S i := fun i hi => lt_of_le_of_ne (hS0 i hi) (hz i hi).symm
  set b := ∑ i ∈ I, β i
  have hb0 : 0 < b := by linarith
  set w : ι → ℝ := fun i => β i / b
  have hw0 : ∀ i ∈ I, 0 ≤ w i := fun i hi => (div_pos (hβ i hi) hb0).le
  have hw1 : ∑ i ∈ I, w i = 1 := by
    simp only [w]; rw [← Finset.sum_div]; exact div_self hb0.ne'
  set x : ι → κ → ℝ := fun i G => m i G / S i
  have hx0 : ∀ i ∈ I, ∀ G ∈ Gs, 0 ≤ x i G := fun i hi G hG =>
    div_nonneg (hm i hi G hG) (hS0 i hi)
  have hx1 : ∀ i ∈ I, ∀ G ∈ Gs, x i G ≤ 1 := fun i hi G hG => by
    rw [div_le_one (hSpos i hi)]
    exact Finset.single_le_sum (fun G' hG' => hm i hi G' hG') hG
  -- each normalized term is at most the weighted mean
  have hterm : ∀ G ∈ Gs, ∏ i ∈ I, x i G ^ β i ≤ ∑ i ∈ I, w i * x i G := by
    intro G hG
    calc ∏ i ∈ I, x i G ^ β i ≤ ∏ i ∈ I, x i G ^ w i := by
          refine Finset.prod_le_prod₀ (fun i hi => Real.rpow_nonneg (hx0 i hi G hG) _)
            fun i hi => Real.rpow_le_rpow_of_exponent_ge' (hx0 i hi G hG) (hx1 i hi G hG)
              (hw0 i hi) ?_
          simp only [w]
          rw [div_le_iff₀ hb0]
          exact le_mul_of_one_le_right (hβ i hi).le hb
      _ ≤ ∑ i ∈ I, w i * x i G :=
          Real.geom_mean_le_arith_mean_weighted I w (fun i => x i G) hw0 hw1
            fun i hi => hx0 i hi G hG
  have hsumx : ∑ G ∈ Gs, ∏ i ∈ I, x i G ^ β i ≤ 1 := by
    calc ∑ G ∈ Gs, ∏ i ∈ I, x i G ^ β i ≤ ∑ G ∈ Gs, ∑ i ∈ I, w i * x i G :=
          Finset.sum_le_sum hterm
      _ = ∑ i ∈ I, w i * ∑ G ∈ Gs, x i G := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ = ∑ i ∈ I, w i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          simp only [x]
          rw [← Finset.sum_div, div_self (hSpos i hi).ne', mul_one]
      _ = 1 := hw1
  -- undo the normalization
  have hfact : ∀ G ∈ Gs, ∏ i ∈ I, m i G ^ β i =
      (∏ i ∈ I, S i ^ β i) * ∏ i ∈ I, x i G ^ β i := by
    intro G hG
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp only [x]
    rw [Real.div_rpow (hm i hi G hG) (hS0 i hi), mul_div_cancel₀]
    exact (Real.rpow_pos_of_pos (hSpos i hi) _).ne'
  rw [Finset.sum_congr rfl hfact, ← Finset.mul_sum]
  have hP : 0 ≤ ∏ i ∈ I, S i ^ β i := Finset.prod_nonneg fun i hi => Real.rpow_nonneg (hS0 i hi) _
  calc (∏ i ∈ I, S i ^ β i) * ∑ G ∈ Gs, ∏ i ∈ I, x i G ^ β i ≤ (∏ i ∈ I, S i ^ β i) * 1 :=
        mul_le_mul_of_nonneg_left hsumx hP
    _ = ∏ i ∈ I, S i ^ β i := mul_one _


theorem rpow_finset_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) : (∑ i ∈ s, x i) ^ p ≤ ∑ i ∈ s, x i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hp0.ne']
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have hxs : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h2' : (x a + ∑ i ∈ s, x i) ^ p ≤ x a ^ p + (∑ i ∈ s, x i) ^ p :=
      Real.rpow_add_le_add_rpow hxa hxs hp0.le hp1
    exact h2'.trans (add_le_add le_rfl (ih fun i hi => hx i (Finset.mem_insert_of_mem hi)))


theorem min_sum_le_rpow {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {η p : ℝ} (hη : 0 ≤ η) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    min η (∑ i ∈ s, x i) ≤ η ^ (1 - p) * ∑ i ∈ s, x i ^ p :=
  (min_le_rpow_mul hη (Finset.sum_nonneg hx) hp0.le hp1).trans
    (mul_le_mul_of_nonneg_left (rpow_finset_sum_le s x hx hp0 hp1) (Real.rpow_nonneg hη _))


/-- Paper (36) -> (34), with p₀ = 1 - 1/4160. The exact sparse-mass
hypothesis is used at every δ. The constant is 2B. -/
theorem paper_powered_count {ι : Type*} (s : Finset ι) (N : ι → ℝ)
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
  have h := distribution_power s N hM hN0 hNM hA (by positivity : 0 < B * M ^ 2)
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

/-- Apply the minimum on the original cell before summing powers of the
principal terms. Numerical errors remain at power one. -/
theorem paper_min_with_error {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {η p a e : ℝ} (hη : 0 ≤ η) (hp : 0 < p) (hp1 : p ≤ 1)
    (hx : ∀ i ∈ s, 0 ≤ x i) (he : 0 ≤ e) (ha : a ≤ ∑ i ∈ s, x i + e) :
    min η a ≤ η ^ (1-p) * ∑ i ∈ s, x i ^ p + e := by
  have hmin : min η (∑ i ∈ s, x i + e) ≤ min η (∑ i ∈ s, x i) + e := by
    by_cases hh : η ≤ ∑ i ∈ s, x i
    · rw [min_eq_left hh, min_eq_left (by linarith)]
      linarith
    · rw [min_eq_right (le_of_not_ge hh)]
      exact min_le_right _ _
  exact (min_le_min_left η ha).trans (hmin.trans
    (add_le_add_right (min_sum_le_rpow s x hx hη hp hp1) e))

end OpenAI086.SourceV60
#print axioms OpenAI086.SourceV60.min_le_rpow_mul
#print axioms OpenAI086.SourceV60.rpow_one_sub_eq_integral
#print axioms OpenAI086.SourceV60.distribution_power
#print axioms OpenAI086.SourceV60.sum_prod_rpow_le
#print axioms OpenAI086.SourceV60.rpow_finset_sum_le
#print axioms OpenAI086.SourceV60.min_sum_le_rpow
#print axioms OpenAI086.SourceV60.paper_powered_count
#print axioms OpenAI086.SourceV60.paper_min_with_error
