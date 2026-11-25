import Mathlib
import OpenAI086.PaperSideChainColoring

/-!
V51 conditional event-energy assembly for Proposition 8.9 (pp. 72--73).
It combines event-row Bessel energy, the exact-subtotal error budget, and
within-colour almost-orthogonality.  The paper-specific PRE graph, chain
bound, projection leakage estimate, and offset averaging are not assumed
proved by this module.
-/
namespace OpenAI086

/-- Sum the exact event subtotals over their decision colours.  If the
projection rows have total energy A*|R| and the replacement errors have
energy B*|R|, then the coloured linear-side subtotal energy is bounded by
K(2A+2B)|R|, provided each colour class has the stated near-orthogonality
bound. -/
theorem v51_prop89_event_energy_assembly
    {E G X : Type*} [Fintype E] [Fintype G] [DecidableEq G]
    [NormedAddCommGroup X]
    (P T : E → X) (color : E → G)
    (K A B R : ℝ) (hK : 0 ≤ K)
    (hproj : (∑ e : E, ‖P e‖^2) ≤ A*R)
    (herr : (∑ e : E, ‖T e-P e‖^2) ≤ B*R)
    (horth : ∀ g : G,
      ‖∑ e : E, if color e = g then T e else 0‖^2 ≤
        K * (∑ e : E, if color e = g then ‖T e‖^2 else 0)) :
    (∑ g : G, ‖∑ e : E, if color e = g then T e else 0‖^2) ≤
      K*(2*(A+B)*R) := by
  have hT : (∑ e : E, ‖T e‖^2) ≤ 2*(A*R)+2*(B*R) :=
    v21_exact_subtotal_energy P T (A*R) (B*R) hproj herr
  have hpartition :
      (∑ g : G, ∑ e : E, if color e = g then ‖T e‖^2 else 0) =
        ∑ e : E, ‖T e‖^2 := by
    rw [Finset.sum_comm]
    simp
  calc
    _ ≤ ∑ g : G, K * (∑ e : E, if color e = g then ‖T e‖^2 else 0) :=
      Finset.sum_le_sum (fun g _ => horth g)
    _ = K * (∑ g : G, ∑ e : E,
        if color e = g then ‖T e‖^2 else 0) := by rw [Finset.mul_sum]
    _ = K * (∑ e : E, ‖T e‖^2) := by rw [hpartition]
    _ ≤ K * (2*(A*R)+2*(B*R)) := mul_le_mul_of_nonneg_left hT hK
    _ = K*(2*(A+B)*R) := by ring

end OpenAI086
