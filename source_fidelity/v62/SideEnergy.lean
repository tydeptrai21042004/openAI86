import SourceV62PathCore
import OpenAI086.PaperV51Prop89Assembly

/-! Proposition 8.9: the event leakage budget follows from a normalized
per-event error and the pathwise bound on event multiplicity. This joins
those estimates to the existing colour-energy assembly. The oscillatory
leakage and row Bessel estimates themselves remain inputs. -/
namespace OpenAI086.SourceV62
open scoped BigOperators

theorem side_energy_from_normalized_errors {E G L H : Type*}
    [Fintype E] [Fintype G] [DecidableEq G] [NormedAddCommGroup H]
    (leaves : Finset L) (w : L → ℝ) (onPath : E → L → Prop) [DecidableRel onPath]
    (P T : E → H) (color : E → G) (K A B ε : ℝ)
    (hK : 0 ≤ K) (hε : 0 ≤ ε) (hw : ∀ l ∈ leaves, 0 ≤ w l)
    (hcount : ∀ l ∈ leaves, (∑ e : E, if onPath e l then (1:ℝ) else 0) ≤ B)
    (hleak : ∀ e, ‖T e-P e‖ ≤ ε * Real.sqrt (∑ l ∈ leaves, if onPath e l then w l else 0))
    (hproj : (∑ e : E, ‖P e‖^2) ≤ A * ∑ l ∈ leaves, w l)
    (horth : ∀ g : G,
      ‖∑ e : E, if color e = g then T e else 0‖^2 ≤
        K * (∑ e : E, if color e = g then ‖T e‖^2 else 0)) :
    (∑ g : G, ‖∑ e : E, if color e = g then T e else 0‖^2) ≤
      K * (2*(A+ε^2*B)*(∑ l ∈ leaves, w l)) := by
  let len : E → ℝ := fun e => ∑ l ∈ leaves, if onPath e l then w l else 0
  have hlen : ∀ e, 0 ≤ len e := by
    intro e
    apply Finset.sum_nonneg
    intro l hl
    by_cases h : onPath e l <;> simp [h, hw l hl]
  have hpack : (∑ e : E, len e) ≤ B * ∑ l ∈ leaves, w l := by
    simpa only [len, mul_one] using
      (leaf_budget (Finset.univ : Finset E) leaves w onPath (fun _ => (1:ℝ)) B hw
        (fun l hl => hcount l hl))
  have hpoint : ∀ e, ‖T e-P e‖^2 ≤ ε^2 * len e := by
    intro e
    calc
      _ ≤ (ε * Real.sqrt (len e))^2 := pow_le_pow_left₀ (norm_nonneg _) (hleak e) 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt (hlen e)]
  have herr : (∑ e : E, ‖T e-P e‖^2) ≤ (ε^2*B) * ∑ l ∈ leaves, w l := by
    calc
      _ ≤ ∑ e : E, ε^2 * len e := Finset.sum_le_sum fun e _ => hpoint e
      _ = ε^2 * (∑ e : E, len e) := by rw [Finset.mul_sum]
      _ ≤ ε^2 * (B * ∑ l ∈ leaves, w l) := mul_le_mul_of_nonneg_left hpack (sq_nonneg _)
      _ = _ := by ring
  exact OpenAI086.v51_prop89_event_energy_assembly P T color K A (ε^2*B)
    (∑ l ∈ leaves, w l) hK hproj herr horth

end OpenAI086.SourceV62
#print axioms OpenAI086.SourceV62.side_energy_from_normalized_errors
