/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license (LICENSE-REFERENCE-APACHE2).
Original authors: Claude. Extracted and namespaced for OpenAI086 V58.
Source: TrilinearHT/Auto/Sec14_2aShortBlockSampling.lean and Sec14_2bShortBlockSummation.lean.
-/
import Mathlib

namespace OpenAI086.AdaptedV58
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal BigOperators

/-- Two integer pairs with the same sum and the same sum of squares agree as multisets. -/
theorem pair_eq_of_sum_sq {m₁ m₂ m₃ m₄ : ℤ} (hs : m₁ + m₂ = m₃ + m₄)
    (hq : m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2) :
    (m₃ = m₁ ∧ m₄ = m₂) ∨ (m₃ = m₂ ∧ m₄ = m₁) := by
  have h2 : 2 * ((m₁ - m₃) * (m₁ - m₄)) = 0 := by
    linear_combination hq - (m₂ + m₃ + m₄ - m₁) * hs
  have hprod : (m₁ - m₃) * (m₁ - m₄) = 0 := by omega
  rcases mul_eq_zero.mp hprod with h | h
  · left; constructor <;> omega
  · right; constructor <;> omega

/-- Blueprint `eq:fourth-moment` (lines 2311-2315), the pairing count: the sum of
`a(m₁) a(m₂) conj a(m₃) conj a(m₄)` over quadruples with equal sums and equal squared sums (what
survives integration in `w` and in `γ`) is at most `2 (Σ |a|²)²`. -/
theorem fourth_moment_pairing (s : Finset ℤ) (a : ℤ → ℂ) :
    ‖∑ m₁ ∈ s, ∑ m₂ ∈ s, ∑ m₃ ∈ s, ∑ m₄ ∈ s,
        (if m₁ + m₂ = m₃ + m₄ ∧ m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2 then
          a m₁ * a m₂ * conj (a m₃) * conj (a m₄) else 0)‖ ≤
      2 * (∑ m ∈ s, ‖a m‖ ^ 2) ^ 2 := by
  classical
  set X : ℤ → ℤ → ℤ → ℤ → ℝ := fun m₁ m₂ m₃ m₄ => ‖a m₁‖ * ‖a m₂‖ * ‖a m₃‖ * ‖a m₄‖
  have hterm : ∀ m₁ m₂ m₃ m₄, ‖(if m₁ + m₂ = m₃ + m₄ ∧ m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2 then
      a m₁ * a m₂ * conj (a m₃) * conj (a m₄) else 0)‖ ≤
      (if m₃ = m₁ ∧ m₄ = m₂ then X m₁ m₂ m₃ m₄ else 0) +
        (if m₃ = m₂ ∧ m₄ = m₁ then X m₁ m₂ m₃ m₄ else 0) := by
    intro m₁ m₂ m₃ m₄
    have hX : 0 ≤ X m₁ m₂ m₃ m₄ := by positivity
    have h1 : ‖(if m₁ + m₂ = m₃ + m₄ ∧ m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2 then
        a m₁ * a m₂ * conj (a m₃) * conj (a m₄) else 0)‖ ≤
        if m₁ + m₂ = m₃ + m₄ ∧ m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2 then X m₁ m₂ m₃ m₄ else 0 := by
      split_ifs
      · simp [X]
      · simp
    refine h1.trans ?_
    split_ifs with hc hA hB hB <;> try linarith
    rcases pair_eq_of_sum_sq hc.1 hc.2 with h | h
    · exact absurd h hA
    · exact absurd h hB
  have hsum : ∀ m₁ ∈ s, ∀ m₂ ∈ s, ∑ m₃ ∈ s, ∑ m₄ ∈ s,
      ((if m₃ = m₁ ∧ m₄ = m₂ then X m₁ m₂ m₃ m₄ else 0) +
        (if m₃ = m₂ ∧ m₄ = m₁ then X m₁ m₂ m₃ m₄ else 0)) = 2 * (‖a m₁‖ ^ 2 * ‖a m₂‖ ^ 2) := by
    intro m₁ h₁ m₂ h₂
    simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_eq', h₁, h₂, ite_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero, X]
    ring
  calc _ ≤ ∑ m₁ ∈ s, ∑ m₂ ∈ s, ∑ m₃ ∈ s, ∑ m₄ ∈ s,
        ((if m₃ = m₁ ∧ m₄ = m₂ then X m₁ m₂ m₃ m₄ else 0) +
          (if m₃ = m₂ ∧ m₄ = m₁ then X m₁ m₂ m₃ m₄ else 0)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₁ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₂ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₃ _ => ?_)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun m₄ _ => hterm _ _ _ _)
    _ = ∑ m₁ ∈ s, ∑ m₂ ∈ s, 2 * (‖a m₁‖ ^ 2 * ‖a m₂‖ ^ 2) :=
        Finset.sum_congr rfl fun m₁ h₁ => Finset.sum_congr rfl fun m₂ h₂ => hsum m₁ h₁ m₂ h₂
    _ = 2 * (∑ m ∈ s, ‖a m‖ ^ 2) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro m₁ _
        rw [Finset.mul_sum]

/-! ### The fast multipliers and the fourth moment (lem:shortblock, blueprint lines 2314-2326) -/

/-- The additive character `e(x) = exp(2πix)` of a real phase. -/
noncomputable def ePhase (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

theorem ePhase_add (x y : ℝ) : ePhase x * ePhase y = ePhase (x + y) := by
  unfold ePhase; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem ePhase_conj (x : ℝ) : (starRingEnd ℂ) (ePhase x) = ePhase (-x) := by
  unfold ePhase
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I,
    map_ofNat]
  push_cast; ring

theorem norm_ePhase (x : ℝ) : ‖ePhase x‖ = 1 := by
  unfold ePhase
  rw [Complex.norm_exp]
  simp

theorem continuous_ePhase : Continuous ePhase := by unfold ePhase; fun_prop

/-- `∫₀ᴸ e(k x / L) dx = L [k = 0]` for an integer frequency `k`. -/
theorem integral_ePhase_int (k : ℤ) {L : ℝ} (hL : 0 < L) :
    ∫ x in (0 : ℝ)..L, ePhase (k * x / L) = if k = 0 then (L : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp [ePhase]
  set c : ℂ := 2 * Real.pi * Complex.I * k / L
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hc : c ≠ 0 := by
    simp only [c]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hπ) Complex.I_ne_zero)
      hk') hL'
  have he : ∀ x : ℝ, ePhase (k * x / L) = Complex.exp (c * x) := by
    intro x; unfold ePhase; congr 1; simp only [c]; push_cast; field_simp
  simp_rw [he]
  rw [integral_exp_mul_complex hc]
  have h1 : c * (L : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [c]; field_simp
  rw [h1, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- The fast trigonometric polynomial `Σ_m a_m e(γ m²/c + m w/16)` on the circle of length `16`
after the multiplier `e(γ m²/c)` (blueprint line 2316). -/
noncomputable def fastMultiplied (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (γ w : ℝ) : ℂ :=
  ∑ m ∈ s, a m * ePhase (γ * (m : ℝ) ^ 2 / c + m * w / 16)

/-- The fourth power expanded into the quadruple sum. -/
theorem fastMultiplied_norm_pow_four (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (γ w : ℝ) :
    ((‖fastMultiplied s a c γ w‖ ^ 4 : ℝ) : ℂ) =
      ∑ m₁ ∈ s, ∑ m₂ ∈ s, ∑ m₃ ∈ s, ∑ m₄ ∈ s,
        a m₁ * a m₂ * (starRingEnd ℂ) (a m₃) * (starRingEnd ℂ) (a m₄) *
          (ePhase (γ * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2 - (m₃ : ℝ) ^ 2 - (m₄ : ℝ) ^ 2) / c) *
            ePhase (((m₁ + m₂ - m₃ - m₄ : ℤ) : ℝ) * w / 16)) := by
  set G := fastMultiplied s a c γ w
  have h4 : ((‖G‖ ^ 4 : ℝ) : ℂ) = (starRingEnd ℂ) G * (starRingEnd ℂ) G * G * G := by
    have : ((‖G‖ ^ 2 : ℝ) : ℂ) = G * (starRingEnd ℂ) G := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [show ‖G‖ ^ 4 = (‖G‖ ^ 2) ^ 2 by ring, Complex.ofReal_pow, this]; ring
  rw [h4]
  simp only [G, fastMultiplied, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
    Finset.sum_congr rfl fun m₃ _ => Finset.sum_congr rfl fun m₄ _ => ?_
  simp only [map_mul, ePhase_conj]
  have hR : ePhase (γ * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2 - (m₃ : ℝ) ^ 2 - (m₄ : ℝ) ^ 2) / c) *
      ePhase (((m₁ + m₂ - m₃ - m₄ : ℤ) : ℝ) * w / 16) =
        ePhase (γ * (m₁ : ℝ) ^ 2 / c + m₁ * w / 16) * ePhase (γ * (m₂ : ℝ) ^ 2 / c + m₂ * w / 16) *
          ePhase (-(γ * (m₃ : ℝ) ^ 2 / c + m₃ * w / 16)) *
          ePhase (-(γ * (m₄ : ℝ) ^ 2 / c + m₄ * w / 16)) := by
    rw [ePhase_add, ePhase_add, ePhase_add, ePhase_add]
    congr 1; push_cast; ring
  rw [hR]
  ring

/-- Interval integrals commute with quadruple finite sums of continuous functions. -/
theorem intervalIntegral_quad_sum {x₀ x₁ : ℝ} (s : Finset ℤ) (F : ℤ → ℤ → ℤ → ℤ → ℝ → ℂ)
    (hF : ∀ i j k l, Continuous (F i j k l)) :
    ∫ x in x₀..x₁, ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s, F i j k l x =
      ∑ i ∈ s, ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s, ∫ x in x₀..x₁, F i j k l x := by
  have c1 : ∀ i j k, Continuous fun x => ∑ l ∈ s, F i j k l x := fun i j k =>
    continuous_finsetSum _ fun l _ => hF i j k l
  have c2 : ∀ i j, Continuous fun x => ∑ k ∈ s, ∑ l ∈ s, F i j k l x := fun i j =>
    continuous_finsetSum _ fun k _ => c1 i j k
  have c3 : ∀ i, Continuous fun x => ∑ j ∈ s, ∑ k ∈ s, ∑ l ∈ s, F i j k l x := fun i =>
    continuous_finsetSum _ fun j _ => c2 i j
  rw [intervalIntegral.integral_finsetSum fun i _ => (c3 i).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j _ => (c2 i j).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun k _ => (c1 i j k).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact intervalIntegral.integral_finsetSum fun l _ => (hF i j k l).intervalIntegrable _ _

/-- Blueprint `eq:fourth-moment` (lines 2318-2322) for finite Fourier sums: when `c ∣ 3`,
the average over `γ ∈ ℝ/3ℤ` of the normalized `L⁴` norm on the circle of length `16` satisfies
`E_γ ∫ |U_γ F|⁴ ≤ 2 (Σ |a_m|²)² = 2 ‖F‖₂⁴`. -/
theorem fast_fourth_moment (s : Finset ℤ) (a : ℤ → ℂ) {c : ℤ} (hc0 : c ≠ 0) (hc : c ∣ 3) :
    (1 / 3) * ∫ γ in (0 : ℝ)..3, (1 / 16) * ∫ w in (0 : ℝ)..16, ‖fastMultiplied s a c γ w‖ ^ 4 ≤
      2 * (∑ m ∈ s, ‖a m‖ ^ 2) ^ 2 := by
  classical
  obtain ⟨b, hb⟩ := hc
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0
  -- integration in `w`
  have hw : ∀ γ : ℝ, ((∫ w in (0 : ℝ)..16, ‖fastMultiplied s a c γ w‖ ^ 4 : ℝ) : ℂ) =
      16 * ∑ m₁ ∈ s, ∑ m₂ ∈ s, ∑ m₃ ∈ s, ∑ m₄ ∈ s,
        if m₁ + m₂ - m₃ - m₄ = 0 then
          a m₁ * a m₂ * (starRingEnd ℂ) (a m₃) * (starRingEnd ℂ) (a m₄) *
            ePhase (γ * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2 - (m₃ : ℝ) ^ 2 - (m₄ : ℝ) ^ 2) / c)
        else 0 := by
    intro γ
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [fastMultiplied_norm_pow_four]
    rw [intervalIntegral_quad_sum s _ fun m₁ m₂ m₃ m₄ => by
      have := continuous_ePhase; fun_prop]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
      Finset.sum_congr rfl fun m₃ _ => Finset.sum_congr rfl fun m₄ _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_ePhase_int _ (by norm_num : (0 : ℝ) < 16)]
    split_ifs <;> push_cast <;> ring
  -- integration in `γ`
  have hγ : ∀ q : ℤ, ∫ γ in (0 : ℝ)..3, ePhase (γ * q / c) = if q = 0 then (3 : ℂ) else 0 := by
    intro q
    have h := integral_ePhase_int (q * b) (L := 3) (by norm_num)
    have hq : ∀ γ : ℝ, ePhase (γ * q / c) = ePhase (((q * b : ℤ) : ℝ) * γ / 3) := by
      intro γ; congr 1
      have : (3 : ℝ) = c * b := by exact_mod_cast hb
      have hbR : (b : ℝ) ≠ 0 := by
        rintro h; rw [h, mul_zero] at this; norm_num at this
      rw [this]; push_cast; field_simp
    simp_rw [hq]
    rw [h]
    have hb0 : b ≠ 0 := by rintro rfl; simp at hb
    simp [hb0]
  set P : ℂ := ∑ m₁ ∈ s, ∑ m₂ ∈ s, ∑ m₃ ∈ s, ∑ m₄ ∈ s,
    (if m₁ + m₂ = m₃ + m₄ ∧ m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2 then
      a m₁ * a m₂ * (starRingEnd ℂ) (a m₃) * (starRingEnd ℂ) (a m₄) else 0)
  have htotal : ((((1 / 3) * ∫ γ in (0 : ℝ)..3, (1 / 16) *
      ∫ w in (0 : ℝ)..16, ‖fastMultiplied s a c γ w‖ ^ 4) : ℝ) : ℂ) = P := by
    push_cast
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [Complex.ofReal_mul, hw]
    simp_rw [Finset.mul_sum]
    rw [intervalIntegral_quad_sum s _ fun m₁ m₂ m₃ m₄ => by
      have := continuous_ePhase; split_ifs <;> fun_prop, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₂ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₃ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₄ _ => ?_
    by_cases hd : m₁ + m₂ - m₃ - m₄ = 0
    · have hγq := hγ (m₁ ^ 2 + m₂ ^ 2 - m₃ ^ 2 - m₄ ^ 2)
      have hcast : ∀ γ : ℝ, γ * (((m₁ ^ 2 + m₂ ^ 2 - m₃ ^ 2 - m₄ ^ 2 : ℤ) : ℝ)) / c =
          γ * ((m₁ : ℝ) ^ 2 + (m₂ : ℝ) ^ 2 - (m₃ : ℝ) ^ 2 - (m₄ : ℝ) ^ 2) / c := by
        intro γ; push_cast; ring
      simp_rw [hcast] at hγq
      simp only [hd, ite_true]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hγq]
      have hd' : m₁ + m₂ = m₃ + m₄ := by omega
      by_cases hq : m₁ ^ 2 + m₂ ^ 2 - m₃ ^ 2 - m₄ ^ 2 = 0
      · have hq' : m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2 := by omega
        rw [ite_eq_left hq, ite_eq_left ⟨hd', hq'⟩]
        push_cast; ring
      · have hq' : ¬ m₁ ^ 2 + m₂ ^ 2 = m₃ ^ 2 + m₄ ^ 2 := by omega
        simp [hq, hq']
    · have hd' : ¬ m₁ + m₂ = m₃ + m₄ := by omega
      simp [hd, hd']
  have hreal := congrArg (‖·‖) htotal
  simp only [Complex.norm_real, Real.norm_eq_abs] at hreal
  refine (le_abs_self _).trans (hreal.le.trans ?_)
  exact fourth_moment_pairing s a

/-- The fast multiplier coefficients `c = (-1, 3, -3, 1)` (blueprint line 2314). -/
def fastSlotC : Fin 4 → ℤ := ![-1, 3, -3, 1]

theorem ePhase_prod_four (x : Fin 4 → ℝ) : ∏ j, ePhase (x j) = ePhase (∑ j, x j) := by
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, ePhase_add]

theorem ePhase_zero : ePhase 0 = 1 := by simp [ePhase]

/-- `fast_form_quadratic_invariance` over `ℝ`. -/
theorem fast_quadratic_invariance_real (m : Fin 4 → ℝ) (h0 : m 0 + m 1 + m 2 + m 3 = 0)
    (h1 : m 1 + 2 * m 2 + 3 * m 3 = 0) :
    ∑ j, m j ^ 2 / (fastSlotC j : ℝ) = 0 := by
  have hm1 : m 1 = -2 * m 2 - 3 * m 3 := by linarith
  have hm0 : m 0 = m 2 + 2 * m 3 := by linarith
  simp only [Fin.sum_univ_four, fastSlotC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [hm0, hm1]; push_cast; ring

/-- The product of the four multiplied slots on the progression `w_j = (1-j)u + jv`, expanded
over frequency tuples. -/
theorem fast_slots_product (s : Finset ℤ) (a : Fin 4 → ℤ → ℂ) (γ u v : ℝ) :
    ∏ j : Fin 4, fastMultiplied s (a j) (fastSlotC j) γ ((1 - (j : ℝ)) * u + j * v) =
      ∑ p ∈ Fintype.piFinset fun _ : Fin 4 => s, (∏ j, a j (p j)) *
        (ePhase (γ * ∑ j, ((p j : ℝ)) ^ 2 / (fastSlotC j : ℝ)) *
          ePhase ((((∑ j : Fin 4, (1 - (j : ℤ)) * p j : ℤ) : ℝ) * u +
            ((∑ j : Fin 4, (j : ℤ) * p j : ℤ) : ℝ) * v) / 16)) := by
  simp only [fastMultiplied]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.prod_mul_distrib, ePhase_prod_four, ePhase_add]
  congr 2
  simp only [Fin.sum_univ_four]
  push_cast
  ring

/-- `∫₀¹⁶ ∫₀¹⁶ e((A u + B v)/16) dv du = 16² [A = 0][B = 0]`. -/
theorem double_integral_ePhase (A B : ℤ) :
    ∫ u in (0 : ℝ)..16, ∫ v in (0 : ℝ)..16, ePhase (((A : ℝ) * u + (B : ℝ) * v) / 16) =
      if A = 0 ∧ B = 0 then (256 : ℂ) else 0 := by
  have hsplit : ∀ u v : ℝ, ePhase (((A : ℝ) * u + (B : ℝ) * v) / 16) =
      ePhase ((A : ℝ) * u / 16) * ePhase ((B : ℝ) * v / 16) := by
    intro u v; rw [ePhase_add]; congr 1; ring
  simp_rw [hsplit, intervalIntegral.integral_const_mul]
  rw [integral_ePhase_int B (by norm_num : (0 : ℝ) < 16), intervalIntegral.integral_mul_const,
    integral_ePhase_int A (by norm_num : (0 : ℝ) < 16)]
  by_cases hA : A = 0 <;> by_cases hB : B = 0 <;> simp [hA, hB]; norm_num

/-- Blueprint lines 2314-2317: the fast form of the multiplied slots does not depend on `γ`:
its Fourier support has `Σ m_j = Σ j m_j = 0`, hence `Σ m_j² / c_j = 0`. The form equals
`16² Σ_{Σ m_j = Σ j m_j = 0} Π_j a_j(m_j)`. -/
theorem fast_form_eval (s : Finset ℤ) (a : Fin 4 → ℤ → ℂ) (γ : ℝ) :
    ∫ u in (0 : ℝ)..16, ∫ v in (0 : ℝ)..16,
        ∏ j : Fin 4, fastMultiplied s (a j) (fastSlotC j) γ ((1 - (j : ℝ)) * u + j * v) =
      256 * ∑ p ∈ Fintype.piFinset fun _ : Fin 4 => s,
        if (∑ j : Fin 4, (1 - (j : ℤ)) * p j) = 0 ∧ (∑ j : Fin 4, (j : ℤ) * p j) = 0 then
          ∏ j, a j (p j) else 0 := by
  simp_rw [fast_slots_product]
  have hc : ∀ p : Fin 4 → ℤ, Continuous fun x : ℝ × ℝ => (∏ j, a j (p j)) *
      (ePhase (γ * ∑ j, ((p j : ℝ)) ^ 2 / (fastSlotC j : ℝ)) *
        ePhase ((((∑ j : Fin 4, (1 - (j : ℤ)) * p j : ℤ) : ℝ) * x.1 +
          ((∑ j : Fin 4, (j : ℤ) * p j : ℤ) : ℝ) * x.2) / 16)) := by
    intro p; have := continuous_ePhase; fun_prop
  have hin : ∀ u : ℝ, ∫ v in (0 : ℝ)..16, ∑ p ∈ Fintype.piFinset fun _ : Fin 4 => s,
      (∏ j, a j (p j)) * (ePhase (γ * ∑ j, ((p j : ℝ)) ^ 2 / (fastSlotC j : ℝ)) *
        ePhase ((((∑ j : Fin 4, (1 - (j : ℤ)) * p j : ℤ) : ℝ) * u +
          ((∑ j : Fin 4, (j : ℤ) * p j : ℤ) : ℝ) * v) / 16)) =
      ∑ p ∈ Fintype.piFinset fun _ : Fin 4 => s, ∫ v in (0 : ℝ)..16,
      (∏ j, a j (p j)) * (ePhase (γ * ∑ j, ((p j : ℝ)) ^ 2 / (fastSlotC j : ℝ)) *
        ePhase ((((∑ j : Fin 4, (1 - (j : ℤ)) * p j : ℤ) : ℝ) * u +
          ((∑ j : Fin 4, (j : ℤ) * p j : ℤ) : ℝ) * v) / 16)) := fun u =>
    intervalIntegral.integral_finsetSum fun p _ =>
      ((hc p).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  simp_rw [hin]
  rw [intervalIntegral.integral_finsetSum fun p _ => ?_]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp_rw [intervalIntegral.integral_const_mul]
    rw [double_integral_ePhase]
    split_ifs with h
    · have e0 : p 0 - p 2 - 2 * p 3 = 0 := by
        have := h.1; simp only [Fin.sum_univ_four] at this; norm_num at this; linarith
      have e1 : p 1 + 2 * p 2 + 3 * p 3 = 0 := by
        have := h.2; simp only [Fin.sum_univ_four] at this; norm_num at this; linarith
      have hq : ∑ j, ((p j : ℝ)) ^ 2 / (fastSlotC j : ℝ) = 0 := by
        apply fast_quadratic_invariance_real
        · have : p 0 + p 1 + p 2 + p 3 = 0 := by linarith
          exact_mod_cast this
        · exact_mod_cast e1
      rw [hq, mul_zero, ePhase_zero]; ring
    · ring
  · have : Continuous fun u : ℝ => ∫ v in (0 : ℝ)..16,
        (∏ j, a j (p j)) * (ePhase (γ * ∑ j, ((p j : ℝ)) ^ 2 / (fastSlotC j : ℝ)) *
          ePhase ((((∑ j : Fin 4, (1 - (j : ℤ)) * p j : ℤ) : ℝ) * u +
            ((∑ j : Fin 4, (j : ℤ) * p j : ℤ) : ℝ) * v) / 16)) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (hc p) 0 16
    exact this.intervalIntegrable _ _

/-- Blueprint lines 2314-2317: the multipliers `U_{j,γ}` leave the fast form unchanged. -/
theorem fast_form_invariance (s : Finset ℤ) (a : Fin 4 → ℤ → ℂ) (γ : ℝ) :
    ∫ u in (0 : ℝ)..16, ∫ v in (0 : ℝ)..16,
        ∏ j : Fin 4, fastMultiplied s (a j) (fastSlotC j) γ ((1 - (j : ℝ)) * u + j * v) =
      ∫ u in (0 : ℝ)..16, ∫ v in (0 : ℝ)..16,
        ∏ j : Fin 4, fastMultiplied s (a j) (fastSlotC j) 0 ((1 - (j : ℝ)) * u + j * v) := by
  rw [fast_form_eval, fast_form_eval]

/-- Parseval for fast trigonometric sums on the circle of length `16`:
`(1/16) ∫₀¹⁶ |Σ_m a_m e(m w / 16)|² dw = Σ_m |a_m|²`. -/
theorem fast_parseval (s : Finset ℤ) (a : ℤ → ℂ) :
    (1 / 16) * ∫ w in (0 : ℝ)..16, ‖∑ m ∈ s, a m * ePhase (m * w / 16)‖ ^ 2 =
      ∑ m ∈ s, ‖a m‖ ^ 2 := by
  classical
  have hsq : ∀ w : ℝ, ((‖∑ m ∈ s, a m * ePhase (m * w / 16)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₁ ∈ s, ∑ m₂ ∈ s, a m₁ * (starRingEnd ℂ) (a m₂) *
        ePhase (((m₁ - m₂ : ℤ) : ℝ) * w / 16) := by
    intro w
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
    rw [map_mul, ePhase_conj]
    have : ePhase (m₁ * w / 16) * ePhase (-(m₂ * w / 16)) =
        ePhase (((m₁ - m₂ : ℤ) : ℝ) * w / 16) := by
      rw [ePhase_add]; congr 1; push_cast; ring
    rw [← this]; ring
  have hc : ∀ m₁ m₂ : ℤ, Continuous fun w : ℝ =>
      a m₁ * (starRingEnd ℂ) (a m₂) * ePhase (((m₁ - m₂ : ℤ) : ℝ) * w / 16) := by
    intro m₁ m₂; have := continuous_ePhase; fun_prop
  have hint : ((∫ w in (0 : ℝ)..16, ‖∑ m ∈ s, a m * ePhase (m * w / 16)‖ ^ 2 : ℝ) : ℂ) =
      16 * ∑ m ∈ s, ((‖a m‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hsq]
    rw [intervalIntegral.integral_finsetSum fun m₁ _ =>
      (continuous_finsetSum _ fun m₂ _ => hc m₁ m₂).intervalIntegrable _ _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m₁ hm₁ => ?_
    rw [intervalIntegral.integral_finsetSum fun m₂ _ => (hc m₁ m₂).intervalIntegrable _ _]
    simp_rw [intervalIntegral.integral_const_mul,
      integral_ePhase_int _ (by norm_num : (0 : ℝ) < 16)]
    rw [Finset.sum_eq_single m₁]
    · simp only [sub_self, ↓reduceIte]
      rw [Complex.mul_conj', ← Complex.ofReal_pow]
      push_cast; ring
    · intro m₂ _ hne
      have : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      simp [this]
    · intro h; exact absurd hm₁ h
  have := congrArg Complex.re hint
  simp only [Complex.ofReal_re] at this
  rw [this]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  rw [Complex.re_sum]
  simp only [Complex.ofReal_re]
  ring

/-- The fast circle `T₀ = ℝ / 16ℤ` of blueprint line 2303. -/
abbrev FastCircle := AddCircle (16 : ℝ)

instance : Fact ((0 : ℝ) < 16) := ⟨by norm_num⟩

/-- Normalized Haar measure on the fast circle. -/
noncomputable abbrev fastHaar : Measure FastCircle := AddCircle.haarAddCircle

/-- The progression coordinate `w_j = (1 - j) u + j v` as a homomorphism `T₀² → T₀`. -/
def fastCoord (j : ℤ) : FastCircle × FastCircle →+ FastCircle where
  toFun x := (1 - j) • x.1 + j • x.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, smul_add]; abel

theorem continuous_fastCoord (j : ℤ) : Continuous (fastCoord j) := by
  change Continuous fun x : FastCircle × FastCircle => (1 - j) • x.1 + j • x.2
  fun_prop

theorem fastCoord_surjective (j : ℤ) : Function.Surjective (fastCoord j) := by
  intro x
  refine ⟨(x, x), ?_⟩
  change (1 - j) • x + j • x = x
  rw [← add_smul]; simp

/-- Two distinct progression coordinates `(w_i, w_j)` as a homomorphism `T₀² → T₀²`. -/
def fastPair (i j : ℤ) : FastCircle × FastCircle →+ FastCircle × FastCircle :=
  (fastCoord i).prod (fastCoord j)

theorem fastPair_surjective {i j : ℤ} (hij : i ≠ j) : Function.Surjective (fastPair i j) := by
  rintro ⟨x, y⟩
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hd : ((j : ℝ) - i) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hij.symm)
  set u : ℝ := (j * a - i * b) / (j - i)
  set v : ℝ := ((1 - i) * b - (1 - j) * a) / (j - i)
  refine ⟨((u : FastCircle), (v : FastCircle)), ?_⟩
  have h1 : (1 - (i : ℝ)) * u + i * v = a := by
    simp only [u, v]; field_simp; ring
  have h2 : (1 - (j : ℝ)) * u + j * v = b := by
    simp only [u, v]; field_simp; ring
  change ((1 - i) • (u : FastCircle) + i • (v : FastCircle),
    (1 - j) • (u : FastCircle) + j • (v : FastCircle)) = ((a : FastCircle), (b : FastCircle))
  simp only [← AddCircle.coe_zsmul, zsmul_eq_mul, ← AddCircle.coe_add]
  push_cast
  rw [h1, h2]

instance : IsProbabilityMeasure (fastHaar.prod fastHaar) := inferInstance

theorem map_fastCoord : Measure.map (fastCoord j) (fastHaar.prod fastHaar) = fastHaar := by
  have : Measure.IsAddHaarMeasure (Measure.map (fastCoord j) (fastHaar.prod fastHaar)) :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure _ (fastCoord j) (continuous_fastCoord j)
      (fastCoord_surjective j)
  have : IsProbabilityMeasure (Measure.map (fastCoord j) (fastHaar.prod fastHaar)) :=
    ⟨by rw [Measure.map_apply (continuous_fastCoord j).measurable MeasurableSet.univ]; simp⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

theorem map_fastPair {i j : ℤ} (hij : i ≠ j) :
    Measure.map (fastPair i j) (fastHaar.prod fastHaar) = fastHaar.prod fastHaar := by
  have hc : Continuous (fastPair i j) :=
    (continuous_fastCoord i).prodMk (continuous_fastCoord j)
  have : Measure.IsAddHaarMeasure (Measure.map (fastPair i j) (fastHaar.prod fastHaar)) :=
    Measure.isAddHaarMeasure_map_of_isFiniteMeasure _ (fastPair i j) hc (fastPair_surjective hij)
  have : IsProbabilityMeasure (Measure.map (fastPair i j) (fastHaar.prod fastHaar)) :=
    ⟨by rw [Measure.map_apply hc.measurable MeasurableSet.univ]; simp⟩
  exact Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The single progression coordinate pushes Haar measure on `T₀²` to Haar measure on `T₀`. -/
theorem lintegral_fastCoord (j : ℤ) {f : FastCircle → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f (fastCoord j x) ∂(fastHaar.prod fastHaar) = ∫⁻ t, f t ∂fastHaar := by
  rw [← lintegral_map hf (continuous_fastCoord j).measurable, map_fastCoord]

/-- Blueprint line 394 (torus pair endpoint): two distinct progression coordinates are
independent: `∫∫ f(w_i) g(w_j) = ∫ f ∫ g`. -/
theorem lintegral_fastPair {i j : ℤ} (hij : i ≠ j) {f g : FastCircle → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, f (fastCoord i x) * g (fastCoord j x) ∂(fastHaar.prod fastHaar) =
      (∫⁻ t, f t ∂fastHaar) * ∫⁻ t, g t ∂fastHaar := by
  have hc : Continuous (fastPair i j) :=
    (continuous_fastCoord i).prodMk (continuous_fastCoord j)
  have hm : Measurable fun y : FastCircle × FastCircle => f y.1 * g y.2 :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  have := lintegral_map hm hc.measurable (μ := fastHaar.prod fastHaar)
  rw [map_fastPair hij] at this
  rw [lintegral_prod_mul hf.aemeasurable hg.aemeasurable] at this
  exact this.symm


/-- The uniform probability on `γ ∈ [0, 3)` (blueprint line 2316, `γ ∈ ℝ/3ℤ`). -/
noncomputable def gammaMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / 3) • volume.restrict (Set.Ioc 0 3)

instance : IsProbabilityMeasure gammaMeasure := by
  constructor
  rw [gammaMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ioc,
    smul_eq_mul, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem fastSlotC_ne_zero (j : Fin 4) : fastSlotC j ≠ 0 := by
  fin_cases j <;> simp [fastSlotC]

theorem fastSlotC_dvd (j : Fin 4) : fastSlotC j ∣ 3 := by
  fin_cases j <;> simp [fastSlotC]

/-- Haar averages on the fast circle are interval averages over one period. -/
theorem integral_fastHaar_eq (f : FastCircle → ℝ) :
    ∫ t, f t ∂fastHaar = (1 / 16) * ∫ x in (0 : ℝ)..16, f x := by
  rw [AddCircle.integral_haarAddCircle, smul_eq_mul, one_div]
  congr 1
  have := AddCircle.intervalIntegral_preimage (16 : ℝ) 0 f
  rw [zero_add] at this
  exact this.symm

/-- The multiplied fast trigonometric polynomial as a function on the fast circle. -/
noncomputable def fastCircleMultiplied (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (γ : ℝ)
    (t : FastCircle) : ℂ :=
  ∑ m ∈ s, a m * ePhase (γ * (m : ℝ) ^ 2 / c) * fourier m t

theorem fastCircleMultiplied_coe (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (γ x : ℝ) :
    fastCircleMultiplied s a c γ (x : FastCircle) = fastMultiplied s a c γ x := by
  unfold fastCircleMultiplied fastMultiplied
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [fourier_coe_apply, show Complex.exp (2 * Real.pi * Complex.I * m * x / ((16 : ℝ) : ℂ)) =
    ePhase (m * x / 16) by unfold ePhase; congr 1; push_cast; ring, mul_assoc, ePhase_add]

theorem continuous_fastCircleMultiplied (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (γ : ℝ) :
    Continuous (fastCircleMultiplied s a c γ) := by
  unfold fastCircleMultiplied
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (fourier m).continuous

/-- Blueprint `eq:fourth-moment` (lines 2318-2322) on the fast circle with normalized Haar
measure, for finite Fourier sums: `E_γ ∫ |U_γ F|⁴ ≤ 2 ‖F‖₂⁴` with `‖F‖₂² = Σ |a_m|²`. -/
theorem fast_fourth_moment_circle (s : Finset ℤ) (a : ℤ → ℂ) {c : ℤ} (hc0 : c ≠ 0)
    (hc : c ∣ 3) :
    (1 / 3) * ∫ γ in (0 : ℝ)..3, ∫ t, ‖fastCircleMultiplied s a c γ t‖ ^ 4 ∂fastHaar ≤
      2 * (∑ m ∈ s, ‖a m‖ ^ 2) ^ 2 := by
  have h := fast_fourth_moment s a hc0 hc
  refine le_trans (le_of_eq ?_) h
  congr 1
  refine intervalIntegral.integral_congr fun γ _ => ?_
  rw [integral_fastHaar_eq]
  simp only [fastCircleMultiplied_coe]

/-- Unitarity of the fast multipliers (Parseval on the fast circle):
`∫ |U_γ F|² = Σ_m |a_m|²`. -/
theorem fast_circle_parseval (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (γ : ℝ) :
    ∫ t, ‖fastCircleMultiplied s a c γ t‖ ^ 2 ∂fastHaar = ∑ m ∈ s, ‖a m‖ ^ 2 := by
  rw [integral_fastHaar_eq]
  simp only [fastCircleMultiplied_coe]
  have h := fast_parseval s (fun m => a m * ePhase (γ * (m : ℝ) ^ 2 / c))
  have e : ∀ w : ℝ, fastMultiplied s a c γ w =
      ∑ m ∈ s, a m * ePhase (γ * (m : ℝ) ^ 2 / c) * ePhase (m * w / 16) := by
    intro w
    unfold fastMultiplied
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_assoc, ePhase_add]
  simp_rw [e]
  rw [h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [norm_mul, norm_ePhase, mul_one]

theorem continuous_fastCircleMultiplied_joint (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) :
    Continuous fun p : ℝ × FastCircle => fastCircleMultiplied s a c p.1 p.2 := by
  unfold fastCircleMultiplied
  refine continuous_finsetSum _ fun m _ => ?_
  have := continuous_ePhase
  exact (continuous_const.mul (this.comp (by fun_prop))).mul
    ((fourier m).continuous.comp continuous_snd)

/-- Unitarity in `ℝ≥0∞` form: `∫⁻ |U_γ F|² = Σ |a_m|²`. -/
theorem lintegral_fastCircle_sq (s : Finset ℤ) (a : ℤ → ℂ) (c : ℤ) (γ : ℝ) :
    ∫⁻ t, ‖fastCircleMultiplied s a c γ t‖ₑ ^ (2 : ℝ) ∂fastHaar =
      ENNReal.ofReal (∑ m ∈ s, ‖a m‖ ^ 2) := by
  have hc := continuous_fastCircleMultiplied s a c γ
  rw [← fast_circle_parseval s a c γ, ofReal_integral_eq_lintegral_ofReal]
  · refine lintegral_congr fun t => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      Real.rpow_two]
  · exact (hc.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact Filter.Eventually.of_forall fun t => by positivity

/-- `eq:fourth-moment` in `ℝ≥0∞` form with the uniform `γ`-average. -/
theorem lintegral_fastCircle_fourth (s : Finset ℤ) (a : ℤ → ℂ) {c : ℤ} (hc0 : c ≠ 0)
    (hc : c ∣ 3) :
    ∫⁻ γ, ∫⁻ t, ‖fastCircleMultiplied s a c γ t‖ₑ ^ (4 : ℝ) ∂fastHaar ∂gammaMeasure ≤
      ENNReal.ofReal (2 * (∑ m ∈ s, ‖a m‖ ^ 2) ^ 2) := by
  set F : ℝ → ℝ := fun γ => ∫ t, ‖fastCircleMultiplied s a c γ t‖ ^ 4 ∂fastHaar
  have hj := continuous_fastCircleMultiplied_joint s a c
  have hFc : Continuous F := by
    have := continuous_parametric_integral_of_continuous (μ := fastHaar)
      (f := fun γ t => ‖fastCircleMultiplied s a c γ t‖ ^ 4)
      ((hj.norm.pow 4).congr fun p => rfl) isCompact_univ
    simpa only [Measure.restrict_univ] using this
  have hin : ∀ γ, ∫⁻ t, ‖fastCircleMultiplied s a c γ t‖ₑ ^ (4 : ℝ) ∂fastHaar =
      ENNReal.ofReal (F γ) := by
    intro γ
    have hc := continuous_fastCircleMultiplied s a c γ
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun t => ?_
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    · exact (hc.norm.pow 4).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact Filter.Eventually.of_forall fun t => by positivity
  simp_rw [hin]
  have hF0 : ∀ γ, 0 ≤ F γ := fun γ => integral_nonneg fun t => by positivity
  rw [gammaMeasure, lintegral_smul_measure, ← ofReal_integral_eq_lintegral_ofReal
    (hFc.integrableOn_Ioc) (Filter.Eventually.of_forall hF0), smul_eq_mul, ← ENNReal.ofReal_mul
    (by norm_num), ← intervalIntegral.integral_of_le (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (fast_fourth_moment_circle s a hc0 hc)

/-! ### Fourier partial sums of the fast windows (limiting route of lem:shortblock) -/

/-- The symmetric Fourier partial sums of an `L²` function on the fast circle converge to it in
`L²` (Mathlib `hasSum_fourier_series_L2`). -/
theorem fast_partial_sums_tendsto (f : Lp ℂ 2 fastHaar) :
    Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
      fourierCoeff f m • fourierLp (T := 16) 2 m) Filter.atTop (nhds f) :=
  (hasSum_fourier_series_L2 f).comp Finset.tendsto_Icc_neg

/-- Bessel's inequality for finite sets of frequencies: `Σ_{m ∈ s} |f̂(m)|² ≤ ‖f‖₂²`. -/
theorem fast_bessel (f : Lp ℂ 2 fastHaar) (s : Finset ℤ) :
    ∑ m ∈ s, ‖fourierCoeff f m‖ ^ 2 ≤ ∫ t, ‖f t‖ ^ 2 ∂fastHaar :=
  sum_le_hasSum s (fun _ _ => by positivity) (hasSum_sq_fourierCoeff f)

/-- Paper p.55: for each actual slot, the truncated random Fourier
polynomial is bounded by twice the fourth power of the full input L² norm.
This does not assert joint almost-everywhere convergence of the random polynomials. -/
theorem v58_slot_partial_fourth (f : Lp ℂ 2 fastHaar) (s : Finset ℤ) (j : Fin 4) :
    (1 / 3) * ∫ γ in (0 : ℝ)..3, ∫ t,
      ‖fastCircleMultiplied s (fourierCoeff f) (fastSlotC j) γ t‖ ^ 4 ∂fastHaar ≤
    2 * (∫ t, ‖f t‖ ^ 2 ∂fastHaar)^2 := by
  have h := fast_fourth_moment_circle s (fourierCoeff f)
    (fastSlotC_ne_zero j) (fastSlotC_dvd j)
  refine h.trans ?_
  have hb := fast_bessel f s
  have hn : 0 ≤ ∑ m ∈ s, ‖fourierCoeff f m‖ ^ 2 := by positivity
  have hp : (∑ m ∈ s, ‖fourierCoeff f m‖ ^ 2)^2 ≤
      (∫ t, ‖f t‖ ^ 2 ∂fastHaar)^2 := by
    exact pow_le_pow_left₀ hn hb 2
  linarith

end OpenAI086.AdaptedV58
#print axioms OpenAI086.AdaptedV58.fast_fourth_moment
#print axioms OpenAI086.AdaptedV58.fast_form_invariance
#print axioms OpenAI086.AdaptedV58.fast_circle_parseval
#print axioms OpenAI086.AdaptedV58.fast_fourth_moment_circle
#print axioms OpenAI086.AdaptedV58.lintegral_fastCircle_fourth
#print axioms OpenAI086.AdaptedV58.fast_partial_sums_tendsto
#print axioms OpenAI086.AdaptedV58.fast_bessel
#print axioms OpenAI086.AdaptedV58.v58_slot_partial_fourth
#print axioms OpenAI086.AdaptedV58.lintegral_fastPair
