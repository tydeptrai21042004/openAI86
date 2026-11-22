import Mathlib
import OpenAI086.FiniteRowCauchySchwarz

/-!
# V6: finite four-linear Cauchy--Schwarz (Section 7.1 / 7.5)

The manuscript applies more delicate mixed-norm maximal estimates over
spatial intervals. This finite model records the exact squared bound
obtained when the first two and last two input factors are grouped.
It is a local algebraic ingredient, not a replacement for Lemma 7.1.
-/

namespace OpenAI086

/-- Four scalar inputs can be bounded by the energies of their two
paired products. This is Cauchy--Schwarz on the actual four-factor
expression, not an assumed row estimate. -/
theorem finite_four_linear_cauchy_schwarz
    {ι : Type*} [Fintype ι]
    (a b c d : ι → ℝ) :
    (∑ i : ι, a i * b i * c i * d i) ^ 2 ≤
      (∑ i : ι, (a i * b i) ^ 2) *
      (∑ i : ι, (c i * d i) ^ 2) := by
  classical
  calc
    (∑ i : ι, a i * b i * c i * d i) ^ 2 =
        (∑ i : ι, (a i * b i) * (c i * d i)) ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ ≤ (∑ i : ι, (a i * b i) ^ 2) *
        (∑ i : ι, (c i * d i) ^ 2) :=
          finite_row_cauchy_schwarz (fun i => a i * b i)
            (fun i => c i * d i)

end OpenAI086
