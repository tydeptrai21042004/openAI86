import Mathlib
import OpenAI086.PaperWeylReturns

/-! Lemma 4.3, pages 16–17: actual measure integration of disjoint
Fourier balls, and the small-return contradiction. The shift-error,
Fourier Lipschitz, ball-volume and Plancherel bounds are explicit inputs;
this file does not establish the chart-specific analytic estimates. -/
namespace OpenAI086
open MeasureTheory

/-- A unimodular translation error transfers the lower bound at the
original Fourier sample to the shifted sample. -/
theorem v39_shift_sample (z w u : ℂ) (δ e : ℝ)
    (hu : ‖u‖ = 1) (hz : 3*δ/4 ≤ ‖z‖)
    (herr : ‖z-u*w‖ ≤ e) (he : e ≤ δ/4) : δ/2 ≤ ‖w‖ := by
  have h := norm_add_le (z-u*w) (u*w)
  rw [sub_add_cancel, norm_mul, hu, one_mul] at h
  linarith

/-- Norm Lipschitz control extends each Fourier sample to an entire ball. -/
theorem v39_ball_lower {E : Type*} [MetricSpace E] (F : E → ℂ)
    (c x : E) (D δ ρ : ℝ) (hD : 0 ≤ D)
    (hLip : ∀ a b, ‖F a-F b‖ ≤ D*dist a b)
    (hc : δ/2 ≤ ‖F c‖) (hx : dist c x ≤ ρ) (hr : D*ρ ≤ δ/6) :
    δ/3 ≤ ‖F x‖ := by
  have h := norm_add_le (F c-F x) (F x)
  rw [sub_add_cancel] at h
  have hm := mul_le_mul_of_nonneg_left hx hD
  linarith [hLip c x]

/-- A separated arithmetic progression has disjoint closed balls.
This does not require a finite-dimensional space. -/
theorem v39_progression_separated {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x ω : E) (i j : ℕ) (hij : i ≠ j)
    (hω : 1 ≤ ‖ω‖) :
    1 ≤ dist (x-(i:ℝ) • ω) (x-(j:ℝ) • ω) := by
  have he : (x-(i:ℝ) • ω)-(x-(j:ℝ) • ω) = ((j:ℝ)-(i:ℝ)) • ω := by
    rw [sub_smul]
    abel
  rw [dist_eq_norm, he, norm_smul, Real.norm_eq_abs]
  have ha : 1 ≤ |(j:ℝ)-(i:ℝ)| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hn : i+1 ≤ j := by omega
      have hr : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast hn
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hn : j+1 ≤ i := by omega
      have hr : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast hn
      rw [abs_of_nonpos (by linarith)]
      linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hω)]

/-- Integrated finite packing: the mass of a constant lower bound on
pairwise disjoint measurable sets is at most the total squared energy.
Using a real integral requires the stated integrability hypotheses. -/
theorem v39_disjoint_energy {X : Type*} [MeasurableSpace X]
    {I : Type*} (μ : Measure X) (s : Finset I) (B : I → Set X)
    (g : X → ℝ) (a : ℝ) (ha : 0 ≤ a) (hg : Integrable g μ)
    (hg0 : ∀ x, 0 ≤ g x) (hm : ∀ i ∈ s, MeasurableSet (B i))
    (hi : ∀ i ∈ s, Integrable ((B i).indicator (fun _ : X => a)) μ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (B i) (B j))
    (hl : ∀ i ∈ s, ∀ x ∈ B i, a ≤ g x) :
    (∑ i ∈ s, a*(μ (B i)).toReal) ≤ ∫ x, g x ∂μ := by
  classical
  let f : I → X → ℝ := fun i => (B i).indicator (fun _ : X => a)
  have hp (x : X) : (∑ i ∈ s, f i x) ≤ g x := by
    by_cases h : ∃ i ∈ s, x ∈ B i
    · obtain ⟨i, his, hxi⟩ := h
      have hs : (∑ j ∈ s, f j x) = f i x := by
        apply Finset.sum_eq_single i
        · intro j hjs hji
          have hn : x ∉ B j := fun hxj =>
            (Set.disjoint_left.mp (hd j hjs i his hji)) hxj hxi
          simp [f, Set.indicator_of_notMem hn]
        · intro hn
          exact (hn his).elim
      rw [hs]
      simpa [f, Set.indicator_of_mem hxi] using hl i his x hxi
    · have hs : (∑ j ∈ s, f j x) = 0 := by
        apply Finset.sum_eq_zero
        intro j hjs
        have hn : x ∉ B j := fun hxj => h ⟨j,hjs,hxj⟩
        simp [f, Set.indicator_of_notMem hn]
      rw [hs]
      exact hg0 x
  have hf : Integrable (fun x => ∑ i ∈ s, f i x) μ :=
    integrable_finset_sum _ (fun i hi' => hi i hi')
  have he := integral_mono hf hg hp
  rw [integral_finset_sum _ (fun i hi' => hi i hi')] at he
  calc
    _ = ∑ i ∈ s, ∫ x, f i x ∂μ := by
      apply Finset.sum_congr rfl
      intro i his
      dsimp [f]
      rw [integral_indicator (hm i his), integral_const]
      simp [Measure.real, smul_eq_mul, mul_comm]
    _ ≤ _ := he

/-- The return increment must have norm < 1 once the actual sample,
Lipschitz, ball measure and Plancherel energy bounds are supplied.
No pre-assumed scalar row energy budget is needed. -/
theorem v39_return_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) (F : E → ℂ) (x ω : E) (M : ℕ)
    (D δ ρ v energy : ℝ) (hδ : 0 < δ) (hD : 0 ≤ D)
    (hρ : 2*ρ < 1) (hsmall : D*ρ ≤ δ/6)
    (hLip : ∀ a b, ‖F a-F b‖ ≤ D*dist a b)
    (hsample : ∀ j < M, δ/2 ≤ ‖F (x-(j:ℝ) • ω)‖)
    (hvolume : ∀ j < M, v ≤ (μ (Metric.closedBall (x-(j:ℝ) • ω) ρ)).toReal)
    (hconst : ∀ j < M, Integrable ((Metric.closedBall (x-(j:ℝ) • ω) ρ).indicator
      (fun _ : E => (δ/3)^2)) μ)
    (hi : Integrable (fun z => ‖F z‖^2) μ)
    (he : (∫ z, ‖F z‖^2 ∂μ) ≤ energy)
    (hcontr : energy < (M:ℝ)*((δ/3)^2*v)) : ‖ω‖ < 1 := by
  by_contra hn
  have hω : 1 ≤ ‖ω‖ := le_of_not_gt hn
  let c : ℕ → E := fun j => x-(j:ℝ) • ω
  let B : ℕ → Set E := fun j => Metric.closedBall (c j) ρ
  have hd : ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M,
      i ≠ j → Disjoint (B i) (B j) := by
    intro i hi' j hj' hij
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hi'' : dist z (c i) ≤ ρ := hz
    have hj'' : dist z (c j) ≤ ρ := hz'
    have ht := dist_triangle (c i) z (c j)
    rw [dist_comm (c i) z] at ht
    have hs : 1 ≤ dist (c i) (c j) := v39_progression_separated x ω i j hij hω
    linarith
  have hl : ∀ i ∈ Finset.range M, ∀ z ∈ B i, (δ/3)^2 ≤ ‖F z‖^2 := by
    intro i his z hz
    have hdist : dist z (c i) ≤ ρ := hz
    have hdist' : dist (c i) z ≤ ρ := by simpa only [dist_comm] using hdist
    have hs := v39_ball_lower F (c i) z D δ ρ hD hLip
      (hsample i (Finset.mem_range.mp his)) hdist' hsmall
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ ‖F z‖+δ/3 by positivity)]
  have hp := v39_disjoint_energy μ (Finset.range M) B (fun z => ‖F z‖^2)
    ((δ/3)^2) (sq_nonneg _) hi (fun z => sq_nonneg _)
    (fun _ _ => by
      first | exact Metric.isClosed_closedBall.measurableSet | exact isClosed_closedBall.measurableSet)
    (fun j hj => hconst j (Finset.mem_range.mp hj)) hd hl
  have hsum : (M:ℝ)*((δ/3)^2*v) ≤ ∑ i ∈ Finset.range M, (δ/3)^2*(μ (B i)).toReal := by
    calc
      _ = ∑ _i ∈ Finset.range M, (δ/3)^2*v := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i his =>
        mul_le_mul_of_nonneg_left (hvolume i (Finset.mem_range.mp his)) (sq_nonneg _)
  exact (not_lt_of_ge ((hsum.trans hp).trans he)) hcontr

end OpenAI086
