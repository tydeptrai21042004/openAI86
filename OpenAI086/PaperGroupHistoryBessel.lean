import Mathlib
import OpenAI086.FiniteRowCauchySchwarz
import OpenAI086.PaperHilbertClog

/-! Lemma 8.8: group adjoint synthesis implies a joint row Bessel estimate.
The group separation estimate (Lemma 6.5) and the local history compression
(Lemma 3.4) must still be furnished for the paper's concrete operators. -/
namespace OpenAI086

/-- Convert a bound for the sum of group adjoints into a joint Bessel
bound. The groups may have different codomain Hilbert spaces. -/
theorem v21_group_adjoint_bessel {G X : Type*} [Fintype G]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {Y : G → Type*} [∀ g, NormedAddCommGroup (Y g)]
    [∀ g, InnerProductSpace ℝ (Y g)]
    (A : (g : G) → X → Y g) (Astar : (g : G) → Y g → X) (C : ℝ)
    (hC : 0 ≤ C)
    (hAdj : ∀ g x w, inner ℝ x (Astar g w) = inner ℝ (A g x) w)
    (hSyn : ∀ w : (g : G) → Y g,
      ‖∑ g, Astar g (w g)‖^2 ≤ C*(∑ g, ‖w g‖^2)) (x : X) :
    (∑ g, ‖A g x‖^2) ≤ C*‖x‖^2 := by
  classical
  let S : ℝ := ∑ g, ‖A g x‖^2
  let z : X := ∑ g, Astar g (A g x)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun g _ => sq_nonneg _)
  have hpair : inner ℝ x z = S := by
    simp only [z, S, inner_sum, hAdj, real_inner_self_eq_norm_sq]
  have hsynth : ‖z‖^2 ≤ C*S := hSyn (fun g => A g x)
  have hCS : S ≤ ‖x‖*‖z‖ := by
    rw [← hpair]
    exact real_inner_le_norm _ _
  have hprod : 0 ≤ ‖x‖*‖z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : S^2 ≤ (‖x‖*‖z‖)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hCS) (add_nonneg hS hprod)]
  have hsq' : S^2 ≤ ‖x‖^2*(C*S) := by
    calc
      _ ≤ (‖x‖*‖z‖)^2 := hsq
      _ = ‖x‖^2*‖z‖^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsynth (sq_nonneg _)
  change S ≤ C*‖x‖^2
  by_cases hz : S = 0
  · rw [hz]; positivity
  · have hp : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
    apply (mul_le_mul_right hp).mp
    calc
      S*S = S^2 := by ring
      _ ≤ ‖x‖^2*(C*S) := hsq'
      _ = C*‖x‖^2*S := by ring

/-- Combine separated group ranges with an individual adjoint energy
bound. This realizes the two-stage synthesis argument on p.72. -/
theorem v21_group_history_bessel {G X : Type*} [Fintype G]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {Y : G → Type*} [∀ g, NormedAddCommGroup (Y g)]
    [∀ g, InnerProductSpace ℝ (Y g)]
    (A : (g : G) → X → Y g) (Astar : (g : G) → Y g → X) (Csep Cind : ℝ)
    (hsep0 : 0 ≤ Csep) (hind0 : 0 ≤ Cind)
    (hAdj : ∀ g x w, inner ℝ x (Astar g w) = inner ℝ (A g x) w)
    (hsep : ∀ w : (g : G) → Y g,
      ‖∑ g, Astar g (w g)‖^2 ≤ Csep*(∑ g, ‖Astar g (w g)‖^2))
    (hind : ∀ g w, ‖Astar g w‖^2 ≤ Cind*‖w‖^2) (x : X) :
    (∑ g, ‖A g x‖^2) ≤ (Csep*Cind)*‖x‖^2 := by
  apply v21_group_adjoint_bessel A Astar (Csep*Cind) (mul_nonneg hsep0 hind0) hAdj _ x
  intro w
  calc
    _ ≤ Csep*(∑ g, ‖Astar g (w g)‖^2) := hsep w
    _ ≤ Csep*(∑ g, Cind*‖w g‖^2) := by
      apply mul_le_mul_of_nonneg_left _ hsep0
      exact Finset.sum_le_sum (fun g _ => hind g (w g))
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- A shared fixed history of norm at most K costs K² in the joint bound.
For the cell-dependent histories of the paper, K must be replaced by the
compression estimate, not by an assumed contraction of individual rows. -/
theorem v21_fixed_history_bessel {G X : Type*} [Fintype G]
    [NormedAddCommGroup X] {Y : G → Type*} [∀ g, NormedAddCommGroup (Y g)]
    (A : (g : G) → X → Y g) (H : X → X) (C K : ℝ)
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hA : ∀ x, (∑ g, ‖A g x‖^2) ≤ C*‖x‖^2)
    (hH : ∀ x, ‖H x‖ ≤ K*‖x‖) (x : X) :
    (∑ g, ‖A g (H x)‖^2) ≤ C*K^2*‖x‖^2 := by
  have hh : ‖H x‖^2 ≤ (K*‖x‖)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (hH x))
      (add_nonneg (mul_nonneg hK (norm_nonneg x)) (norm_nonneg (H x)))]
  calc
    _ ≤ C*‖H x‖^2 := hA (H x)
    _ ≤ C*(K*‖x‖)^2 := mul_le_mul_of_nonneg_left hh hC
    _ = _ := by ring

end OpenAI086
