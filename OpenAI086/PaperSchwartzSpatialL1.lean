import OpenAI086.PaperPVTrilinear

/-! V25: ordinary Schwartz L¹ existence via a separable integrable majorant.
This proof uses Schwartz seminorms of orders 0, 1, 2, 4. It deliberately
makes NO claim of a bound involving only L³ norms. The latter is the
substantive open proof obligation from the paper.
Source candidate, not yet kernel checked. -/
noncomputable section
namespace OpenAI086
open MeasureTheory

private def W (x : ℝ) : ℝ := 1+x^2
private theorem Wpos (x : ℝ) : 0 < W x := by unfold W; positivity
private theorem Wnonneg (x : ℝ) : 0 ≤ W x := (Wpos x).le

/-- Shifted arguments on the near strip have comparable spatial weights. -/
theorem v25_near_weight (x t d : ℝ) (ht : |t| ≤ 1) (hd : |d| ≤ 3) :
    W x * W t ≤ 40 * W (x+d) := by
  have ht2 : t^2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hd2 : d^2 ≤ 9 := by rw [← sq_abs]; nlinarith [abs_nonneg d]
  have hx : x^2 ≤ 2*(x+d)^2+2*d^2 := by nlinarith [sq_nonneg (x+2*d)]
  calc
    _ ≤ W x * 2 := by gcongr; unfold W; linarith
    _ ≤ 40 * W (x+d) := by unfold W; nlinarith [sq_nonneg (x+d)]

/-- Two distinct progression coordinates control both spatial variables. -/
theorem v25_far_weight (x t : ℝ) :
    W x * W t ≤ 16 * W (x-t)^2 * W (x-2*t)^2 := by
  let u := x-t
  let v := x-2*t
  have hx : x = 2*u-v := by dsimp [u,v]; ring
  have ht : t = u-v := by dsimp [u,v]; ring
  have hu : 1+x^2 ≤ 8*(1+u^2)*(1+v^2) := by
    have h : x^2 ≤ 8*u^2+2*v^2 := by rw [hx]; nlinarith [sq_nonneg (2*u+v)]
    nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  have hv : 1+t^2 ≤ 2*(1+u^2)*(1+v^2) := by
    have h : t^2 ≤ 2*u^2+2*v^2 := by rw [ht]; nlinarith [sq_nonneg (u+v)]
    nlinarith [sq_nonneg u, sq_nonneg v, mul_nonneg (sq_nonneg u) (sq_nonneg v)]
  change W x * W t ≤ 16 * W u^2 * W v^2
  calc
    _ ≤ (8*W u*W v)*(2*W u*W v) := by
      apply mul_le_mul hu hv (Wnonneg t)
      exact mul_nonneg (mul_nonneg (by norm_num) (Wnonneg u)) (Wnonneg v)
    _ = _ := by ring

/-- Common size budget for ordinary Schwartz seminorms. -/
private def v25Budget (f : Fin 3 → V25S) : ℝ :=
  ∑ i : Fin 3, ((SchwartzMap.seminorm ℝ 0 0) (f i) +
    (SchwartzMap.seminorm ℝ 0 1) (f i) +
    2*(SchwartzMap.seminorm ℝ 2 0) (f i) + (SchwartzMap.seminorm ℝ 4 0) (f i))

private theorem v25_budget_terms (f : Fin 3 → V25S) (i : Fin 3) :
    (SchwartzMap.seminorm ℝ 0 0) (f i) + (SchwartzMap.seminorm ℝ 0 1) (f i) +
      2*(SchwartzMap.seminorm ℝ 2 0) (f i) + (SchwartzMap.seminorm ℝ 4 0) (f i)
      ≤ v25Budget f := by
  unfold v25Budget
  apply Finset.single_le_sum (f := fun i => (SchwartzMap.seminorm ℝ 0 0) (f i) +
    (SchwartzMap.seminorm ℝ 0 1) (f i) + 2*(SchwartzMap.seminorm ℝ 2 0) (f i) +
      (SchwartzMap.seminorm ℝ 4 0) (f i)) (fun j _ => ?_) (Finset.mem_univ i)
  positivity

private theorem v25_decay4 (f : Fin 3 → V25S) (i : Fin 3) (y : ℝ) :
    W y ^ 2 * ‖f i y‖ ≤ v25Budget f := by
  have h0 := SchwartzMap.norm_le_seminorm ℝ (f i) y
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ (f i) 2 y
  have h4 := SchwartzMap.norm_pow_mul_le_seminorm ℝ (f i) 4 y
  have h1 : 0 ≤ (SchwartzMap.seminorm ℝ 0 1) (f i) := by positivity
  rw [Real.norm_eq_abs, sq_abs] at h2
  have hp4 : |y|^4 = y^4 := by
    calc
      _ = (|y|^2)^2 := by ring
      _ = _ := by rw [sq_abs] <;> ring
  rw [Real.norm_eq_abs, hp4] at h4
  unfold W
  calc
    _ = ‖f i y‖ + 2*(y^2*‖f i y‖) + y^4*‖f i y‖ := by ring
    _ ≤ _ := by linarith [v25_budget_terms f i]

private theorem v25_decay2 (f : Fin 3 → V25S) (i : Fin 3) (y : ℝ) :
    W y * ‖f i y‖ ≤ v25Budget f := by
  apply le_trans _ (v25_decay4 f i y)
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold W
  nlinarith [sq_nonneg y, sq_nonneg (y^2)]

private theorem v25_size (f : Fin 3 → V25S) (i : Fin 3) (y : ℝ) :
    ‖f i y‖ ≤ v25Budget f := by
  apply le_trans _ (v25_decay2 f i y)
  unfold W
  nlinarith [mul_nonneg (sq_nonneg y) (norm_nonneg (f i y))]

private theorem v25_Bnonneg (f : Fin 3 → V25S) : 0 ≤ v25Budget f :=
  (norm_nonneg (f 0 0)).trans (v25_size f 0 0)

private theorem v25_lip_budget (f : Fin 3 → V25S) (i : Fin 3) (y z : ℝ) :
    ‖f i y-f i z‖ ≤ v25Budget f * |y-z| := by
  apply (v25_schwartz_lipschitz (f i) y z).trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  have h0 : 0 ≤ (SchwartzMap.seminorm ℝ 0 0) (f i) := by positivity
  have h2 : 0 ≤ (SchwartzMap.seminorm ℝ 2 0) (f i) := by positivity
  have h4 : 0 ≤ (SchwartzMap.seminorm ℝ 4 0) (f i) := by positivity
  linarith [v25_budget_terms f i]

private theorem v25_weighted_factor (f : Fin 3 → V25S) (i : Fin 3)
    (x t d : ℝ) (ht : |t| ≤ 1) (hd : |d| ≤ 3) :
    (W x * W t) * ‖f i (x+d)‖ ≤ 40 * v25Budget f := by
  calc
    _ ≤ (40*W (x+d))*‖f i (x+d)‖ :=
      mul_le_mul_of_nonneg_right (v25_near_weight x t d ht hd) (norm_nonneg _)
    _ = 40*(W (x+d)*‖f i (x+d)‖) := by ring
    _ ≤ _ := by gcongr <;> exact v25_decay2 f i (x+d)

/-- Near the singularity, place the spatial weight on a non-differenced
factor in each of the three telescoping terms. -/
theorem v25_near_pair_majorant (f : Fin 3 → V25S) (x t : ℝ) (ht : |t| ≤ 1) :
    W x * W t * ‖pairedHilbertKernel (fun i => f i) x t‖ ≤ 480*v25Budget f^3 := by
  let M := v25Budget f
  let V := W x * W t
  have hM : 0 ≤ M := v25_Bnonneg f
  have hV : 0 ≤ V := mul_nonneg (Wnonneg _) (Wnonneg _)
  by_cases hz : t = 0
  · simp [hz, pairedHilbertKernel_zero] <;> positivity
  have htp : 0 < |t| := abs_pos.mpr hz
  have h1 : ‖f 0 (x-t)-f 0 (x+t)‖ ≤ 2*M*|t| := by
    apply (v25_lip_budget f 0 _ _).trans
    rw [show x-t-(x+t) = -(2*t) by ring, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  have h2 : ‖f 1 (x-2*t)-f 1 (x+2*t)‖ ≤ 4*M*|t| := by
    apply (v25_lip_budget f 1 _ _).trans
    rw [show x-2*t-(x+2*t) = -(4*t) by ring, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    ring_nf
  have h3 : ‖f 2 (x-3*t)-f 2 (x+3*t)‖ ≤ 6*M*|t| := by
    apply (v25_lip_budget f 2 _ _).trans
    rw [show x-3*t-(x+3*t) = -(6*t) by ring, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
    ring_nf
  have hw2 : V*‖f 2 (x-3*t)‖ ≤ 40*M := by
    simpa [V, sub_eq_add_neg] using v25_weighted_factor f 2 x t (-(3*t)) ht (by rw [abs_neg, abs_mul]; norm_num <;> linarith)
  have hw0 : V*‖f 0 (x+t)‖ ≤ 40*M :=
    v25_weighted_factor f 0 x t t ht (ht.trans (by norm_num))
  have hn := triple_difference_norm_bound
    (f 0 (x-t)) (f 1 (x-2*t)) (f 2 (x-3*t))
    (f 0 (x+t)) (f 1 (x+2*t)) (f 2 (x+3*t))
  have ha : V * ‖f 0 (x-t)-f 0 (x+t)‖ * ‖f 1 (x-2*t)‖ * ‖f 2 (x-3*t)‖ ≤ (2*M*|t|)*M*(40*M) := by
    calc
      _ = ‖f 0 (x-t)-f 0 (x+t)‖ * ‖f 1 (x-2*t)‖ * (V*‖f 2 (x-3*t)‖) := by ring
      _ ≤ _ := by gcongr <;> first | assumption | exact v25_size f 1 _
  have hb : V * ‖f 0 (x+t)‖ * ‖f 1 (x-2*t)-f 1 (x+2*t)‖ * ‖f 2 (x-3*t)‖ ≤ (40*M)*(4*M*|t|)*M := by
    gcongr <;> first | assumption | exact v25_size f 2 _
  have hc : V * ‖f 0 (x+t)‖ * ‖f 1 (x+2*t)‖ * ‖f 2 (x-3*t)-f 2 (x+3*t)‖ ≤ (40*M)*M*(6*M*|t|) := by
    gcongr <;> first | assumption | exact v25_size f 1 _
  have hnum : V * ‖symmetricTripleNumerator (fun i => f i) x t‖ ≤ 480*M^3*|t| := by
    unfold symmetricTripleNumerator
    have hh := mul_le_mul_of_nonneg_left hn hV
    linarith only [hh, ha, hb, hc, show (2*M*|t|)*M*(40*M) + (40*M)*(4*M*|t|)*M + (40*M)*M*(6*M*|t|) = 480*M^3*|t| by ring]
  change V * ‖pairedHilbertKernel (fun i => f i) x t‖ ≤ 480*M^3
  rw [pairedHilbertKernel, norm_div, Complex.norm_real, Real.norm_eq_abs, ← mul_div_assoc]
  exact (div_le_iff₀ htp).2 hnum

/-- Far from t=0, two rapid-decay factors give a joint integrable weight. -/
theorem v25_far_single_majorant (f : Fin 3 → V25S) (x t : ℝ) (ht : 1 ≤ |t|) :
    W x * W t * ‖kernelMinus (fun i => f i) x t‖ ≤ 16*v25Budget f^3 := by
  let M := v25Budget f
  have hM : 0 ≤ M := v25_Bnonneg f
  have hpos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  simp only [kernelMinus, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hd : (‖f 0 (x-t)‖*‖f 1 (x-2*t)‖*‖f 2 (x-3*t)‖)/|t| ≤
      ‖f 0 (x-t)‖*‖f 1 (x-2*t)‖*‖f 2 (x-3*t)‖ := by
    apply (div_le_iff₀ hpos).2
    exact le_mul_of_one_le_right (by positivity) ht
  calc
    _ ≤ W x * W t * (‖f 0 (x-t)‖*‖f 1 (x-2*t)‖*‖f 2 (x-3*t)‖) := by gcongr
    _ ≤ (16*W (x-t)^2*W (x-2*t)^2) * (‖f 0 (x-t)‖*‖f 1 (x-2*t)‖*‖f 2 (x-3*t)‖) := by
      gcongr <;> exact v25_far_weight x t
    _ = 16*(W (x-t)^2*‖f 0 (x-t)‖)*(W (x-2*t)^2*‖f 1 (x-2*t)‖)*‖f 2 (x-3*t)‖ := by ring
    _ ≤ 16*M*M*M := by gcongr <;> first | exact v25_decay4 f _ _ | exact v25_size f _ _
    _ = _ := by ring

/-- The single global majorant is independent of x and t except for the
separable integrable weights. -/
theorem v25_joint_majorant (f : Fin 3 → V25S) (x t : ℝ) :
    ‖pairedHilbertKernel (fun i => f i) x t‖ ≤ (480*v25Budget f^3) * ((W x)⁻¹*(W t)⁻¹) := by
  have hW : 0 < W x * W t := mul_pos (Wpos x) (Wpos t)
  have hM := v25_Bnonneg f
  have h : W x*W t*‖pairedHilbertKernel (fun i => f i) x t‖ ≤ 480*v25Budget f^3 := by
    by_cases ht : |t| ≤ 1
    · exact v25_near_pair_majorant f x t ht
    · have ha := v25_far_single_majorant f x t (le_of_lt (lt_of_not_ge ht))
      have hb := v25_far_single_majorant f x (-t) (by simpa using le_of_lt (lt_of_not_ge ht))
      have hw : W (-t) = W t := by unfold W; ring
      rw [hw] at hb
      rw [show pairedHilbertKernel (fun i => f i) x t = kernelMinus (fun i => f i) x t + kernelMinus (fun i => f i) x (-t) from (symmetric_kernel_pair (fun i => f i) x t).symm]
      have hsum := mul_le_mul_of_nonneg_left (norm_add_le (kernelMinus (fun i => f i) x t) (kernelMinus (fun i => f i) x (-t))) hW.le
      have hp : 0 ≤ v25Budget f^3 := pow_nonneg hM 3
      linarith only [ha, hb, hsum, hp]
  have hh : ‖pairedHilbertKernel (fun i => f i) x t‖ ≤ (480*v25Budget f^3)/(W x*W t) := by
    apply (le_div_iff₀ hW).2
    simpa [mul_comm] using h
  simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm] using hh

/-- Bochner integrability on the true product measure, not on a finite grid. -/
theorem v25_joint_integrable (f : Fin 3 → V25S) :
    Integrable (fun z : ℝ × ℝ => pairedHilbertKernel (fun i => f i) z.1 z.2)
      ((volume : Measure ℝ).prod volume) := by
  have hw : Integrable (fun x : ℝ => (W x)⁻¹) := by
    simpa [W] using integrable_inv_one_add_sq
  have h := (hw.mul_prod hw).const_mul (480*v25Budget f^3)
  apply h.mono' _ (Filter.Eventually.of_forall (fun z => v25_joint_majorant f z.1 z.2))
  apply Measurable.aestronglyMeasurable
  unfold pairedHilbertKernel symmetricTripleNumerator
  fun_prop

/-- Ordinary spatial L¹ membership follows by Fubini, independently of the
uniform norm bound from Theorem 1.1. -/
theorem v25_pv_spatial_integrable (f : Fin 3 → V25S) : Integrable (v25PV f) := by
  unfold v25PV
  exact (v25_joint_integrable f).integral_prod_left.const_mul _

theorem v25_T_memLp (a b c : V25S) : MemLp (v25T a b c) 1 volume := by
  apply memLp_one_iff_integrable.mpr
  exact v25_pv_spatial_integrable (![a,b,c])

end OpenAI086
