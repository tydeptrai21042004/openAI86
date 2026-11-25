import Mathlib
import OpenAI086.FiniteRowCauchySchwarz

/-!
V52 formalization of the nonfuture-pair estimate in Lemma 9.1, p.84.

For each counting block b and a fixed pair of roles, the block mass is
bounded both by alpha*M^2 and by L*m_i(b)*m_j(b).  The role budgets
sum_b m_i(b) <= M and sum_b m_j(b) <= M then give

  sum_b mass(b) <= sqrt(L*alpha) * M^2.

The final six-pair factor is also derived.  This is one component of
Lemma 9.1; it does not prove the geometric cover or the density-power
saving.
-/
namespace OpenAI086

/-- The fixed-pair nonfuture mass estimate from p.84. -/
theorem v52_nonfuture_pair_mass
    {Block : Type*} [Fintype Block]
    (mass x y : Block → ℝ) (α L M : ℝ)
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hx : ∀ b, 0 ≤ x b) (hy : ∀ b, 0 ≤ y b)
    (hmass : ∀ b, 0 ≤ mass b)
    (hX : (∑ b, x b) ≤ M) (hY : (∑ b, y b) ≤ M)
    (hcap : ∀ b, mass b ≤ α*M^2)
    (hpair : ∀ b, mass b ≤ L*x b*y b) :
    (∑ b, mass b) ≤ Real.sqrt (L*α)*M^2 := by
  classical
  let C : ℝ := Real.sqrt (L*α)*M
  have hLA : 0 ≤ L*α := mul_nonneg hL hα
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.sqrt_nonneg _) hM
  have hpoint (b : Block) :
      mass b ≤ C * Real.sqrt (x b) * Real.sqrt (y b) := by
    have hA : 0 ≤ α*M^2 := mul_nonneg hα (sq_nonneg M)
    have hprod : (mass b)^2 ≤ (α*M^2)*(L*x b*y b) := by
      calc
        (mass b)^2 ≤ (α*M^2)*mass b := by nlinarith [hcap b, hmass b]
        _ ≤ (α*M^2)*(L*x b*y b) :=
          mul_le_mul_of_nonneg_left (hpair b) hA
    have htarget :
        (C * Real.sqrt (x b) * Real.sqrt (y b))^2 =
          (α*M^2)*(L*x b*y b) := by
      dsimp [C]
      calc
        (Real.sqrt (L*α)*M*Real.sqrt (x b)*Real.sqrt (y b))^2 =
            (Real.sqrt (L*α))^2 * M^2 * (Real.sqrt (x b))^2 *
              (Real.sqrt (y b))^2 := by ring
        _ = (L*α)*M^2*x b*y b := by
          rw [Real.sq_sqrt hLA, Real.sq_sqrt (hx b), Real.sq_sqrt (hy b)]
        _ = (α*M^2)*(L*x b*y b) := by ring
    have hnonneg : 0 ≤ C * Real.sqrt (x b) * Real.sqrt (y b) := by
      dsimp [C]
      positivity
    nlinarith [sq_nonneg (mass b - C * Real.sqrt (x b) * Real.sqrt (y b))]
  have hsum :
      (∑ b, mass b) ≤ C * (∑ b, Real.sqrt (x b)*Real.sqrt (y b)) := by
    calc
      _ ≤ ∑ b, C * (Real.sqrt (x b)*Real.sqrt (y b)) :=
        Finset.sum_le_sum (fun b _ => by simpa [mul_assoc] using hpoint b)
      _ = _ := by rw [← Finset.mul_sum]
  let sx : ℝ := ∑ b, Real.sqrt (x b)*Real.sqrt (y b)
  have hcs := finite_row_cauchy_schwarz
    (fun b : Block => Real.sqrt (x b))
    (fun b : Block => Real.sqrt (y b))
  have hxs : (∑ b, (Real.sqrt (x b))^2) = ∑ b, x b := by
    apply Finset.sum_congr rfl
    intro b _
    exact Real.sq_sqrt (hx b)
  have hys : (∑ b, (Real.sqrt (y b))^2) = ∑ b, y b := by
    apply Finset.sum_congr rfl
    intro b _
    exact Real.sq_sqrt (hy b)
  have hcs' : sx^2 ≤ (∑ b, x b)*(∑ b, y b) := by
    dsimp [sx]
    rw [hxs, hys] at hcs
    exact hcs
  have hX0 : 0 ≤ ∑ b, x b := Finset.sum_nonneg (fun b _ => hx b)
  have hY0 : 0 ≤ ∑ b, y b := Finset.sum_nonneg (fun b _ => hy b)
  have hXY : (∑ b, x b)*(∑ b, y b) ≤ M^2 :=
    mul_le_mul hX hY hY0 hM
  have hsx0 : 0 ≤ sx := by
    dsimp [sx]
    exact Finset.sum_nonneg (fun b _ =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hsxM : sx ≤ M := by nlinarith [hcs', hXY]
  calc
    _ ≤ C*sx := by simpa [sx] using hsum
    _ ≤ C*M := mul_le_mul_of_nonneg_left hsxM hC
    _ = Real.sqrt (L*α)*M^2 := by dsimp [C]; ring

/-- Sum the fixed-pair estimate over the at most six choices of role
pair appearing in the proof of Lemma 9.1. -/
theorem v52_six_nonfuture_pair_mass
    {Pair Block : Type*} [Fintype Pair] [Fintype Block]
    (mass x y : Pair → Block → ℝ) (α L M : ℝ)
    (hcard : (Fintype.card Pair : ℝ) ≤ 6)
    (hα : 0 ≤ α) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hx : ∀ p b, 0 ≤ x p b) (hy : ∀ p b, 0 ≤ y p b)
    (hmass : ∀ p b, 0 ≤ mass p b)
    (hX : ∀ p, (∑ b, x p b) ≤ M)
    (hY : ∀ p, (∑ b, y p b) ≤ M)
    (hcap : ∀ p b, mass p b ≤ α*M^2)
    (hpair : ∀ p b, mass p b ≤ L*x p b*y p b) :
    (∑ p, ∑ b, mass p b) ≤ 6*Real.sqrt (L*α)*M^2 := by
  classical
  have hsingle (p : Pair) :
      (∑ b, mass p b) ≤ Real.sqrt (L*α)*M^2 :=
    v52_nonfuture_pair_mass (mass p) (x p) (y p) α L M hα hL hM
      (hx p) (hy p) (hmass p) (hX p) (hY p) (hcap p) (hpair p)
  calc
    _ ≤ ∑ _p : Pair, Real.sqrt (L*α)*M^2 :=
      Finset.sum_le_sum (fun p _ => hsingle p)
    _ = (Fintype.card Pair : ℝ)*(Real.sqrt (L*α)*M^2) := by simp
    _ ≤ 6*Real.sqrt (L*α)*M^2 := by
      apply mul_le_mul_of_nonneg_right hcard
      positivity

end OpenAI086
