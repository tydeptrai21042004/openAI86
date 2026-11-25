import OpenAI086.PaperCompressionRefit
import OpenAI086.FinitePrivateGramUpper
import OpenAI086.PaperComplexPredictorMoment

/-! Lemma 3.2: genuine complex finite private-coordinate synthesis on a
probability-normalized cell. The norm below is the Hilbert l2 norm, not
Mathlib's default sup norm on a function type. The projection estimate
uses the integrated orthogonality identity of an actual refit; construction
of the closed span in L2 and its orthogonal projection remains open. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped BigOperators

def v42L2Norm {I : Type*} [Fintype I] (z : I → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖z i‖^2)

theorem v42_l2_nonneg {I : Type*} [Fintype I] (z : I → ℂ) : 0 ≤ v42L2Norm z :=
  Real.sqrt_nonneg _

theorem v42_l2_sq {I : Type*} [Fintype I] (z : I → ℂ) :
    (v42L2Norm z)^2 = ∑ i, ‖z i‖^2 := by
  unfold v42L2Norm
  exact Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Physical coordinate followed by the distinct private coordinates. -/
def v42Synthesis {n : ℕ} (φ : Fin n → ℂ) (a : Fin n → ℝ) (c : Fin n → ℂ) :
    Fin (n+1) → ℂ :=
  Fin.cases (∑ i, c i * φ i) (fun i => (a i : ℂ) * c i)

theorem v42_synthesis_energy {n : ℕ} (φ : Fin n → ℂ) (a : Fin n → ℝ)
    (c : Fin n → ℂ) :
    (v42L2Norm (v42Synthesis φ a c))^2 =
      ‖∑ i, c i * φ i‖^2 + ∑ i, (a i)^2 * ‖c i‖^2 := by
  rw [v42_l2_sq, Fin.sum_univ_succ]
  simp only [v42Synthesis, Fin.cases_zero, Fin.cases_succ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Two-sided coefficient bounds, allowing arbitrary complex coefficients
and physical columns. The amplitude a is sqrt(epsilon) in the paper. -/
theorem v42_complex_column_bounds {n : ℕ} (φ : Fin n → ℂ)
    (a : Fin n → ℝ) (c : Fin n → ℂ) (D : ℝ)
    (hD : 0 < D) (hn : (n:ℝ) ≤ D) (ha : ∀ i, 1/D ≤ a i)
    (hcol : ∀ i, ‖φ i‖^2 + (a i)^2 ≤ D^2) :
    (v42L2Norm c)^2/D^2 ≤ (v42L2Norm (v42Synthesis φ a c))^2 ∧
    v42L2Norm (v42Synthesis φ a c) ≤ D*Real.sqrt D*v42L2Norm c := by
  have hc := v42_l2_sq c
  have he := v42_synthesis_energy φ a c
  have hp : ‖∑ i, c i * φ i‖^2 ≤ (∑ i, ‖c i‖^2)*(∑ i, ‖φ i‖^2) := by
    simpa only [smul_eq_mul] using v37_complex_vector_cs c φ
  have hpriv := private_energy_finite_upper a (fun i => ‖c i‖)
  simp only [mul_pow] at hpriv
  have hcolsum : (∑ i, (‖φ i‖^2 + (a i)^2)) ≤ D^3 := by
    calc
      _ ≤ ∑ _i : Fin n, D^2 := Finset.sum_le_sum (fun i _ => hcol i)
      _ = (n:ℝ)*D^2 := by simp
      _ ≤ D^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) (sq_nonneg D)]
  have hC : 0 ≤ ∑ i, ‖c i‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hupper : (v42L2Norm (v42Synthesis φ a c))^2 ≤ D^3*(v42L2Norm c)^2 := by
    rw [he, hc]
    calc
      _ ≤ (∑ i, ‖c i‖^2)*(∑ i, ‖φ i‖^2) +
          (∑ i, ‖c i‖^2)*(∑ i, (a i)^2) := add_le_add hp hpriv
      _ = (∑ i, ‖c i‖^2)*(∑ i, (‖φ i‖^2+(a i)^2)) := by
        rw [Finset.sum_add_distrib]; ring
      _ ≤ (∑ i, ‖c i‖^2)*D^3 := mul_le_mul_of_nonneg_left hcolsum hC
      _ = _ := by ring
  constructor
  · rw [hc, he]
    have hl := private_energy_lower_bound a (fun i => ‖c i‖) D hD ha
    simp only [mul_pow] at hl
    have hEq : (∑ i, (‖c i‖/D)^2) = (∑ i, ‖c i‖^2)/D^2 := by
      simp only [div_pow, Finset.sum_div]
    rw [hEq] at hl
    linarith [sq_nonneg ‖∑ i, c i * φ i‖]
  · apply (sq_le_sq₀ (v42_l2_nonneg _) (mul_nonneg (mul_nonneg hD.le (Real.sqrt_nonneg D)) (v42_l2_nonneg c))).mp
    calc
      _ ≤ D^3*(v42L2Norm c)^2 := hupper
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt hD.le]; ring

/-- Coefficient uniqueness without any assumptions on physical phases. -/
theorem v42_synthesis_injective {n : ℕ} (φ : Fin n → ℂ) (a : Fin n → ℝ)
    (ha : ∀ i, a i ≠ 0) : Function.Injective (v42Synthesis φ a) := by
  intro c d h
  funext i
  have hi := congrFun h i.succ
  simp only [v42Synthesis, Fin.cases_succ] at hi
  have hne : (a i : ℂ) ≠ 0 := by exact_mod_cast ha i
  exact mul_left_cancel₀ hne hi

/-- Real part of the complex Hilbert inner product, linear in the first
argument before taking real parts. -/
def v42Pairing {I : Type*} [Fintype I] (z w : I → ℂ) : ℝ :=
  ∑ i, (z i * star (w i)).re

theorem v42_pairing_bound {I : Type*} [Fintype I] (z w : I → ℂ) :
    v42Pairing z w ≤ v42L2Norm z * v42L2Norm w := by
  have hcs := finite_row_cauchy_schwarz (fun i => ‖z i‖) (fun i => ‖w i‖)
  have hs : 0 ≤ ∑ i, ‖z i‖*‖w i‖ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hprod : 0 ≤ v42L2Norm z * v42L2Norm w :=
    mul_nonneg (v42_l2_nonneg _) (v42_l2_nonneg _)
  have hbound : (∑ i, ‖z i‖*‖w i‖) ≤ v42L2Norm z * v42L2Norm w := by
    apply (sq_le_sq₀ hs hprod).mp
    rw [mul_pow, v42_l2_sq, v42_l2_sq]
    exact hcs
  apply le_trans _ hbound
  unfold v42Pairing
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ‖z i * star (w i)‖ := Complex.re_le_norm _
    _ = _ := by simp [norm_mul]

/-- D^5 bound from the *actual complex coordinate* moment identity.
No coefficient coercivity, synthesis bound, or pointwise Cauchy–Schwarz
is passed as a hypothesis. Integrability and the orthogonality identity
remain explicit; constructing the local L2 refit is the next step. -/
theorem v42_complex_refit_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (φ : Ω → Fin n → ℂ) (a : Fin n → ℝ) (c : Fin n → ℂ)
    (z : Ω → Fin (n+1) → ℂ) (D : ℝ)
    (hD : 0 < D) (hn : (n:ℝ) ≤ D) (ha : ∀ i, 1/D ≤ a i)
    (hcol : ∀ x i, ‖φ x i‖^2+(a i)^2 ≤ D^2)
    (hf : Integrable (fun x => v42L2Norm (z x)) μ)
    (hg : Integrable (fun x => (v42L2Norm (v42Synthesis (φ x) a c))^2) μ)
    (hfg : Integrable (fun x => v42L2Norm (z x)*v42L2Norm (v42Synthesis (φ x) a c)) μ)
    (hp : Integrable (fun x => v42Pairing (z x) (v42Synthesis (φ x) a c)) μ)
    (hmoment : (∫ x, (v42L2Norm (v42Synthesis (φ x) a c))^2 ∂μ) =
      ∫ x, v42Pairing (z x) (v42Synthesis (φ x) a c) ∂μ) :
    ∀ x, v42L2Norm (v42Synthesis (φ x) a c) ≤ D^5*(∫ y, v42L2Norm (z y) ∂μ) := by
  apply v38_refit_bound μ (fun x => v42L2Norm (z x))
    (fun x => v42L2Norm (v42Synthesis (φ x) a c)) D (v42L2Norm c) hD (v42_l2_nonneg c)
  · intro x; exact v42_l2_nonneg _
  · intro x; exact (v42_complex_column_bounds (φ x) a c D hD hn ha (hcol x)).1
  · intro x; exact (v42_complex_column_bounds (φ x) a c D hD hn ha (hcol x)).2
  · exact hf
  · exact hg
  · exact hfg
  · rw [hmoment]
    exact integral_mono hp hfg (fun x => v42_pairing_bound _ _)

end OpenAI086
