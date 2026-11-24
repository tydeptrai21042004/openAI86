import Mathlib

/-! Proposition 8.9: construct a rank coloring of linked events from a
bound on the length of directed chains. The graph must be the paper's
persistent PRE-link graph and the chain bound must come from Lemma 8.6. -/
namespace OpenAI086

/-- A directed chain of exactly n edges ending at v. -/
def v21Chain {E : Type*} (edge : E → E → Prop) : ℕ → E → Prop
  | 0, _ => True
  | n+1, v => ∃ u, edge u v ∧ v21Chain edge n u

theorem v21_chain_shorten {E : Type*} (edge : E → E → Prop) (n : ℕ) :
    ∀ v, v21Chain edge (n+1) v → v21Chain edge n v := by
  induction n with
  | zero => intro v h; trivial
  | succ n ih =>
    intro v h
    rcases h with ⟨u, huv, hu⟩
    exact ⟨u, huv, ih u hu⟩

theorem v21_chain_downward {E : Type*} (edge : E → E → Prop) (a b : ℕ)
    (hab : a ≤ b) (v : E) (h : v21Chain edge b v) : v21Chain edge a v := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst a
    trivial
  | succ b ih =>
    by_cases he : a = b+1
    · subst a; exact h
    · exact ih (by omega) (v21_chain_shorten edge b v h)

/-- First absent chain length is a positive integer rank bounded by C. -/
noncomputable def v21EventRank {E : Type*} (edge : E → E → Prop) (C : ℕ)
    (hC : ∀ v, ¬ v21Chain edge C v) (v : E) : ℕ := by
  classical
  exact Nat.find (show ∃ n, ¬ v21Chain edge n v from ⟨C,hC v⟩)

theorem v21_event_rank_bounds {E : Type*} (edge : E → E → Prop) (C : ℕ)
    (hC : ∀ v, ¬ v21Chain edge C v) (v : E) :
    0 < v21EventRank edge C hC v ∧ v21EventRank edge C hC v ≤ C := by
  classical
  unfold v21EventRank
  constructor
  · by_contra! h
    have he : Nat.find (show ∃ n, ¬ v21Chain edge n v from ⟨C,hC v⟩) = 0 := by omega
    have hh := Nat.find_spec (show ∃ n, ¬ v21Chain edge n v from ⟨C,hC v⟩)
    rw [he] at hh
    exact hh trivial
  · exact Nat.find_min' _ (hC v)

/-- Linked events have distinct ranks, in the directed order. -/
theorem v21_event_rank_strict {E : Type*} (edge : E → E → Prop) (C : ℕ)
    (hC : ∀ v, ¬ v21Chain edge C v) (u v : E) (h : edge u v) :
    v21EventRank edge C hC u < v21EventRank edge C hC v := by
  classical
  let r := v21EventRank edge C hC u
  have hr := (v21_event_rank_bounds edge C hC u).1
  have hu : v21Chain edge (r-1) u := by
    by_contra hn
    have hmin : r ≤ r-1 := by
      dsimp [r, v21EventRank]
      exact Nat.find_min' _ hn
    omega
  have hv : v21Chain edge r v := by
    have he : r = (r-1)+1 := by omega
    rw [he]
    exact ⟨u,h,hu⟩
  by_contra! hle
  have hv' := v21_chain_downward edge (v21EventRank edge C hC v) r hle v hv
  have hn : ¬ v21Chain edge (v21EventRank edge C hC v) v := by
    unfold v21EventRank
    exact Nat.find_spec _
  exact hn hv'

/-- Sum color-class energy bounds with no factor depending on the number
of events. Each event belongs to exactly one class. -/
theorem v21_color_energy_sum {E G : Type*} [Fintype E] [Fintype G]
    (color : E → G) (energy : E → ℝ) (B : ℝ)
    (h : ∀ g, (∑ e, if color e = g then energy e else 0) ≤ B) :
    (∑ e, energy e) ≤ (Fintype.card G : ℝ)*B := by
  classical
  calc
    (∑ e, energy e) = ∑ e, ∑ g, if color e = g then energy e else 0 := by simp
    _ = ∑ g, ∑ e, if color e = g then energy e else 0 := Finset.sum_comm
    _ ≤ ∑ _g : G, B := Finset.sum_le_sum (fun g _ => h g)
    _ = _ := by simp

/-- Pass from the event projection outputs to exact coefficient subtotals.
The error bound is summed separately, so this does not charge a factor
for the number of event rows. -/
theorem v21_exact_subtotal_energy {E X : Type*} [Fintype E]
    [NormedAddCommGroup X] (P T : E → X) (A B : ℝ)
    (hP : (∑ e, ‖P e‖^2) ≤ A)
    (hErr : (∑ e, ‖T e-P e‖^2) ≤ B) :
    (∑ e, ‖T e‖^2) ≤ 2*A+2*B := by
  have hpoint (e : E) : ‖T e‖^2 ≤ 2*‖P e‖^2+2*‖T e-P e‖^2 := by
    have ht : ‖T e‖ ≤ ‖P e‖+‖T e-P e‖ := by
      have he : T e = P e + (T e-P e) := by abel
      calc
        ‖T e‖ = ‖P e+(T e-P e)‖ := congrArg norm he
        _ ≤ _ := norm_add_le _ _
    have hsq : ‖T e‖^2 ≤ (‖P e‖+‖T e-P e‖)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht)
        (add_nonneg (norm_nonneg (T e)) (add_nonneg (norm_nonneg (P e)) (norm_nonneg (T e-P e))))]
    nlinarith [sq_nonneg (‖P e‖-‖T e-P e‖)]
  calc
    _ ≤ ∑ e, (2*‖P e‖^2+2*‖T e-P e‖^2) := Finset.sum_le_sum (fun e _ => hpoint e)
    _ = 2*(∑ e, ‖P e‖^2)+2*(∑ e, ‖T e-P e‖^2) := by simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by linarith

/-- Final aggregation of per-cell almost orthogonality and exact subtotal
energy. The near-orthogonality factor is furnished by the graph estimates. -/
theorem v21_linear_side_energy {J E X : Type*} [Fintype J] [Fintype E]
    [NormedAddCommGroup X] (T : J → E → X) (K A : ℝ)
    (hK : 0 ≤ K)
    (horth : ∀ j, ‖∑ e, T j e‖^2 ≤ K*(∑ e, ‖T j e‖^2))
    (hT : (∑ j, ∑ e, ‖T j e‖^2) ≤ A) :
    (∑ j, ‖∑ e, T j e‖^2) ≤ K*A := by
  calc
    _ ≤ ∑ j, K*(∑ e, ‖T j e‖^2) := Finset.sum_le_sum (fun j _ => horth j)
    _ = K*(∑ j, ∑ e, ‖T j e‖^2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hT hK

end OpenAI086
