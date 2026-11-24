import OpenAI086.SchwartzSizeBridge
import OpenAI086.SymmetricKernel
import OpenAI086.PaperTruncationSign

/-! V25: concrete paired principal-value integral for Schwartz data.
The pointwise existence argument is separate from the uniform L3 estimate.
All proofs in this module are source candidates pending the pinned kernel. -/
noncomputable section
namespace OpenAI086
open MeasureTheory Filter Topology Set

abbrev V25S := SchwartzMap ℝ ℂ

theorem v25_schwartz_lipschitz (f : V25S) (y z : ℝ) :
    ‖f y - f z‖ ≤ (SchwartzMap.seminorm ℝ 0 1) f * |y-z| := by
  have h (x : ℝ) : ‖deriv (f : ℝ → ℂ) x‖ ≤ (SchwartzMap.seminorm ℝ 0 1) f := by
    simpa [iteratedDeriv_one] using SchwartzMap.le_seminorm' ℝ 0 1 f x
  simpa [Real.norm_eq_abs] using
    (Convex.norm_image_sub_le_of_norm_deriv_le (f := (f : ℝ → ℂ))
      (s := Set.univ) (fun x _ => f.differentiableAt) (fun x _ => h x)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (mem_univ z) (mem_univ y))

theorem v25_paired_uniform (f : Fin 3 → V25S) (x t : ℝ) :
    ‖pairedHilbertKernel (fun i => f i) x t‖ ≤
      (2*(SchwartzMap.seminorm ℝ 0 1) (f 0) +
       4*(SchwartzMap.seminorm ℝ 0 1) (f 1) +
       6*(SchwartzMap.seminorm ℝ 0 1) (f 2)) * (tripleSchwartzSize f)^2 := by
  apply paired_kernel_bound_for_schwartz_of_lipschitz f x t
    ((SchwartzMap.seminorm ℝ 0 1) (f 0))
    ((SchwartzMap.seminorm ℝ 0 1) (f 1))
    ((SchwartzMap.seminorm ℝ 0 1) (f 2))
  · exact (norm_nonneg _).trans (schwartz_first_iterated_derivative_bound _ 0)
  · exact (norm_nonneg _).trans (schwartz_first_iterated_derivative_bound _ 0)
  · exact (norm_nonneg _).trans (schwartz_first_iterated_derivative_bound _ 0)
  · exact v25_schwartz_lipschitz (f 0)
  · exact v25_schwartz_lipschitz (f 1)
  · exact v25_schwartz_lipschitz (f 2)

theorem v25_kernel_measurable (f : Fin 3 → V25S) (x : ℝ) :
    Measurable (kernelMinus (fun i => f i) x) := by
  unfold kernelMinus
  fun_prop

theorem v25_paired_measurable (f : Fin 3 → V25S) (x : ℝ) :
    Measurable (pairedHilbertKernel (fun i => f i) x) := by
  unfold pairedHilbertKernel symmetricTripleNumerator
  fun_prop

theorem v25_shift_integrable (f : V25S) (x : ℝ) :
    Integrable (fun t : ℝ => f (x+t)) := by
  exact f.integrable.comp_measurePreserving (measurePreserving_add_left volume x)

theorem v25_shift_minus_integrable (f : V25S) (x : ℝ) :
    Integrable (fun t : ℝ => f (x-t)) := by
  simpa [sub_eq_add_neg, Function.comp_def] using (v25_shift_integrable f x).comp_neg

/-- Away from zero only one integrable factor and two uniform bounds are needed. -/
theorem v25_kernel_cut_integrable (f : Fin 3 → V25S) (x ε : ℝ) (hε : 0 < ε) :
    Integrable ({t : ℝ | ε < |t|}.indicator (kernelMinus (fun i => f i) x)) := by
  let M := tripleSchwartzSize f
  have hM : 0 ≤ M := tripleSchwartzSize_nonneg f
  have hm : MeasurableSet {t : ℝ | ε < |t|} := measurableSet_Ioi.preimage measurable_id.abs
  have hi : Integrable (fun t : ℝ => (M^2 / ε) * ‖f 0 (x-t)‖) :=
    (v25_shift_minus_integrable (f 0) x).norm.const_mul _
  apply hi.mono' ((v25_kernel_measurable f x).indicator hm).aestronglyMeasurable
  filter_upwards [] with t
  by_cases ht : ε < |t|
  · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ε < |t|} from ht)]
    simp only [kernelMinus, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have htpos : 0 < |t| := hε.trans ht
    have h1 := tripleSchwartzSize_bound f 1 (x-2*t)
    have h2 := tripleSchwartzSize_bound f 2 (x-3*t)
    calc
      _ ≤ (‖f 0 (x-t)‖ * M * M) / |t| := by gcongr
      _ ≤ (‖f 0 (x-t)‖ * M * M) / ε := by gcongr
      _ = (M^2 / ε) * ‖f 0 (x-t)‖ := by ring
  · rw [Set.indicator_of_not_mem (show t ∉ {t : ℝ | ε < |t|} from ht), norm_zero]
    positivity

/-- On the whole real line the paired kernel has a bounded local part and
an integrable tail. The choice of value at t=0 is irrelevant to integration. -/
theorem v25_paired_integrable (f : Fin 3 → V25S) (x : ℝ) :
    Integrable (pairedHilbertKernel (fun i => f i) x) := by
  let K := kernelMinus (fun i => f i) x
  let s : Set ℝ := {t : ℝ | (1 : ℝ) < |t|}
  let Kc := s.indicator K
  have hk : Integrable Kc := v25_kernel_cut_integrable f x 1 (by norm_num)
  have htail : Integrable (s.indicator (pairedHilbertKernel (fun i => f i) x)) := by
    have heq : s.indicator (pairedHilbertKernel (fun i => f i) x) =
        fun t => Kc t + Kc (-t) := by
      funext t
      by_cases ht : t ∈ s
      · have hn : -t ∈ s := by simpa [s] using ht
        simp only [Kc, Set.indicator_of_mem ht, Set.indicator_of_mem hn]
        exact (symmetric_kernel_pair (fun i => f i) x t).symm
      · have hn : -t ∉ s := by simpa [s] using ht
        simp [Kc, Set.indicator_of_not_mem ht, Set.indicator_of_not_mem hn]
    rw [heq]
    exact hk.add hk.comp_neg
  have hs : MeasurableSet s := measurableSet_Ioi.preimage measurable_id.abs
  have hsmall : IntegrableOn (pairedHilbertKernel (fun i => f i) x) sᶜ := by
    have heq : sᶜ = Icc (-1 : ℝ) 1 := by
      ext t
      simp [s, abs_le]
    rw [heq]
    apply IntegrableOn.of_bound (by simp) (v25_paired_measurable f x).aestronglyMeasurable
    exact Filter.Eventually.of_forall (v25_paired_uniform f x)
  have hl := hsmall.integrable_indicator hs.compl
  have heq : (fun t => s.indicator (pairedHilbertKernel (fun i => f i) x) t +
       sᶜ.indicator (pairedHilbertKernel (fun i => f i) x) t) = pairedHilbertKernel (fun i => f i) x := by
    funext t
    by_cases ht : t ∈ s <;> simp [Set.indicator, ht]
  rw [← heq]
  exact htail.add hl

/-- The integral of the paired kernel on the whole line counts both halves,
so the exact PV has the factor 1/2. -/
def v25PV (f : Fin 3 → V25S) (x : ℝ) : ℂ :=
  (2 : ℂ)⁻¹ * ∫ t : ℝ, pairedHilbertKernel (fun i => f i) x t

theorem v25_cut_pair_identity (f : Fin 3 → V25S) (x ε : ℝ) (hε : 0 < ε) :
    truncHilbert (fun i => f i) x ε = (2 : ℂ)⁻¹ *
      ∫ t : ℝ, {t : ℝ | ε < |t|}.indicator (pairedHilbertKernel (fun i => f i) x) t := by
  let s : Set ℝ := {t : ℝ | ε < |t|}
  let K := s.indicator (kernelMinus (fun i => f i) x)
  have hi : Integrable K := v25_kernel_cut_integrable f x ε hε
  have hs : MeasurableSet s := measurableSet_Ioi.preimage measurable_id.abs
  have heq : s.indicator (pairedHilbertKernel (fun i => f i) x) = fun t => K t + K (-t) := by
    funext t
    by_cases ht : t ∈ s
    · have hn : -t ∈ s := by simpa [s] using ht
      simp only [K, Set.indicator_of_mem ht, Set.indicator_of_mem hn]
      exact (symmetric_kernel_pair (fun i => f i) x t).symm
    · have hn : -t ∉ s := by simpa [s] using ht
      simp [K, Set.indicator_of_not_mem ht, Set.indicator_of_not_mem hn]
  change (∫ t in s, kernelMinus (fun i => f i) x t) = (2 : ℂ)⁻¹ *
    ∫ t, s.indicator (pairedHilbertKernel (fun i => f i) x) t
  rw [← integral_indicator hs, heq, integral_add hi hi.comp_neg, integral_neg_eq_self K volume]
  change (∫ t, K t) = _
  ring

/-- Pointwise PV existence for every x, without the main uniform estimate. -/
theorem v25_pv_tendsto (f : Fin 3 → V25S) (x : ℝ) :
    Tendsto (fun ε : ℝ => truncHilbert (fun i => f i) x ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (v25PV f x)) := by
  let F := pairedHilbertKernel (fun i => f i) x
  have hF : Integrable F := v25_paired_integrable f x
  have hlim : Tendsto (fun ε : ℝ => ∫ t : ℝ, {t : ℝ | ε < |t|}.indicator F t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ t, F t)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖F t‖)
    · exact Filter.Eventually.of_forall (fun ε => (hF.indicator
        (measurableSet_Ioi.preimage measurable_id.abs)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun t => by
        by_cases ht : ε < |t| <;> simp [Set.indicator, ht]))
    · exact hF.norm
    · apply Filter.Eventually.of_forall
      intro t
      by_cases ht : t = 0
      · subst t
        simp [F, pairedHilbertKernel_zero, Set.indicator]
      · have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < |t| :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (abs_pos.mpr ht))
        apply tendsto_const_nhds.congr'
        filter_upwards [hev] with ε hε
        simp [Set.indicator, hε]
  apply ((tendsto_const_nhds (x := (2 : ℂ)⁻¹)).mul hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (v25_cut_pair_identity f x ε hε).symm

end OpenAI086
