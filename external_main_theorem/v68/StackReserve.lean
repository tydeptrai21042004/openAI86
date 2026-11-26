import TrilinearHT.Auto.Sec14_5CommonCutsHullMaximaSummation

/-! Lemma 7.4, equation (18): extract a single overhead from the actual
reference main-column stack energy, without paying a second power of P.
The five normalized input bounds have to come from the analytic construction. -/
namespace OpenAI086.ReferenceV68
open Auto MeasureTheory
open scoped Classical BigOperators

/-- If all variation, base-energy, depth and configuration bounds are
controlled by H, then the two stack budgets are controlled by a common
35 H^6, with the extra P+2 only for the banded side. -/
theorem fixed_stack_common_reserve {κ : LocalKernelClass} {c₀ : ℕ}
    {A : ActiveSetup κ c₀} {bf : A.BasicFamilies} (fp : bf.FamParams) {Ω : Type*}
    (Os : Finset Ω) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (D : Ω → List (Bool × ℕ × Option ℕ)) (N : ℕ)
    {BA BB EWa EWb H : ℝ} (hH : 1 ≤ H)
    (hBA : 0 ≤ BA) (hBB : 0 ≤ BB) (hWa : 0 ≤ EWa) (hWb : 0 ≤ EWb)
    (hN : (N : ℝ) ≤ H) (hOs : (Os.card : ℝ) ≤ H)
    (hJ : ∀ ω ∈ Os, fp.bandJumpM sA mbA (D ω).length ≤ H)
    (hBA' : BA ≤ H * dyadicGridLength A.G A.R.1)
    (hBB' : BB ≤ H * dyadicGridLength A.G A.R.1)
    (hWa' : EWa ≤ H * dyadicGridLength A.G A.R.1)
    (hWb' : EWb ≤ H * dyadicGridLength A.G A.R.1) :
    fp.stackEA Os sA mbA D N BA EWa ≤
      (fp.P + 2) * (35 * H ^ 6) * dyadicGridLength A.G A.R.1 ∧
    (Os.card : ℝ) * (N * BB + EWb) ≤ 35 * H ^ 6 * dyadicGridLength A.G A.R.1 := by
  let R := dyadicGridLength A.G A.R.1
  have hR : 0 ≤ R := (dyadicGridLength_pos A.G A.R.1).le
  have hH0 : 0 ≤ H := by linarith
  -- The restricted power monotonicity is sufficient for every term.
  have hp (n : ℕ) (hn : n ≤ 6) : H ^ n ≤ H ^ 6 := pow_le_pow_right₀ hH hn
  have hpoly : 2 * H ^ 3 + 16 * H ^ 4 + 16 * H ^ 6 + H ^ 2 ≤ 35 * H ^ 6 := by
    linarith [hp 3 (by decide), hp 4 (by decide), hp 2 (by decide)]
  have hpoly' : H ^ 3 + H ^ 2 ≤ 35 * H ^ 6 := by
    linarith [hp 3 (by decide), hp 2 (by decide), pow_nonneg hH0 6]
  have hstack := fp.stackEA_le Os sA mbA D N hBA hWa hJ
  have hsum : (Os.card : ℝ) * (N * (2 * BA + 16 * (H * EWa) +
      16 * (N * (H * (N * BA)))) + EWa) ≤ (2 * H ^ 3 + 16 * H ^ 4 + 16 * H ^ 6 + H ^ 2) * R := by
    calc
      _ ≤ H * (H * (2 * (H * R) + 16 * (H * (H * R)) +
          16 * (H * (H * (H * (H * R))))) + H * R) := by gcongr
      _ = _ := by ring
  constructor
  · calc
      _ ≤ (fp.P + 2) * ((Os.card : ℝ) * (N * (2 * BA + 16 * (H * EWa) +
            16 * (N * (H * (N * BA)))) + EWa)) := hstack
      _ ≤ (fp.P + 2) * ((2 * H ^ 3 + 16 * H ^ 4 + 16 * H ^ 6 + H ^ 2) * R) := by gcongr
      _ ≤ (fp.P + 2) * ((35 * H ^ 6) * R) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ H * (H * (H * R) + H * R) := by gcongr
      _ = (H ^ 3 + H ^ 2) * R := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hpoly' hR

end OpenAI086.ReferenceV68
#print axioms OpenAI086.ReferenceV68.fixed_stack_common_reserve
