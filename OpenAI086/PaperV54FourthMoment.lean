import OpenAI086.PaperShortBlockResonance
import OpenAI086.PaperCubeEnergy

/-! Lemma 7.2, p.55. Finite resonant Fourier coefficient sum: the two
pairings bound its mass by twice the squared L² coefficient energy.
The integration on the two tori and the L² limit remain separate. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

/-- Exact selection rule for the two Fourier averages. -/
def v54Resonant (a b c d : ℤ) : Prop :=
  a+b = c+d ∧ a^2+b^2 = c^2+d^2

instance (a b c d : ℤ) : Decidable (v54Resonant a b c d) := by
  unfold v54Resonant
  infer_instance

theorem v54_integer_resonance (a b c d : ℤ) (h : v54Resonant a b c d) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  obtain ⟨hs,hq⟩ := h
  have hs' : (a:ℝ)+(b:ℝ) = (c:ℝ)+(d:ℝ) := by exact_mod_cast hs
  have hq' : (a:ℝ)^2+(b:ℝ)^2 = (c:ℝ)^2+(d:ℝ)^2 := by exact_mod_cast hq
  rcases v25_fourth_moment_pairings _ _ _ _ hs' hq' with h | h
  · left
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · right
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- Bound the complete finite resonant sum, including repeated indices.
The diagonal is counted at most twice; no number-of-modes loss. -/
theorem v54_resonant_fourth_mass (s : Finset ℤ) (w : ℤ → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      if v54Resonant a b c d then w a*w b else 0) ≤
        2*(∑ a ∈ s, w a)^2 := by
  classical
  have hpoint (a b c d : ℤ) (ha : a ∈ s) (hb : b ∈ s) :
      (if v54Resonant a b c d then w a*w b else 0) ≤
      (if c=a ∧ d=b then w a*w b else 0) +
      (if c=b ∧ d=a then w a*w b else 0) := by
    have hn := mul_nonneg (hw a ha) (hw b hb)
    by_cases h : v54Resonant a b c d
    · rcases v54_integer_resonance a b c d h with ⟨hc,hd⟩ | ⟨hd,hc⟩
      · subst c; subst d
        simp only [if_pos h, eq_self, true_and, and_true, if_true]
        split_ifs <;> linarith
      · subst c; subst d
        simp only [if_pos h, eq_self, true_and, and_true, if_true]
        split_ifs <;> linarith
    · rw [if_neg h]
      split_ifs <;> linarith
  have hpair (a b : ℤ) (ha : a ∈ s) (hb : b ∈ s) :
      (∑ c ∈ s, ∑ d ∈ s,
        (if c=a ∧ d=b then w a*w b else 0) +
        (if c=b ∧ d=a then w a*w b else 0)) = 2*(w a*w b) := by
    have hsingle (u v : ℤ) (hu : u ∈ s) (hv : v ∈ s) :
        (∑ c ∈ s, ∑ d ∈ s, if c=u ∧ d=v then w a*w b else 0) = w a*w b := by
      rw [Finset.sum_eq_single u]
      · simp only [eq_self, true_and]
        rw [Finset.sum_eq_single v]
        · simp
        · intro j _ hj
          simp [hj]
        · intro h
          exact (h hv).elim
      · intro j _ hj
        simp [hj]
      · intro h
        exact (h hu).elim
    simp only [Finset.sum_add_distrib]
    rw [hsingle a b ha hb, hsingle b a hb ha]
    ring

  calc
    _ ≤ ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        (if c=a ∧ d=b then w a*w b else 0) +
        (if c=b ∧ d=a then w a*w b else 0) := by
      exact Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb =>
        Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun d _ => hpoint a b c d ha hb))))
    _ = ∑ a ∈ s, ∑ b ∈ s, 2*(w a*w b) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_congr rfl (fun b hb => hpair a b ha hb)
    _ = _ := by
      calc
        _ = ∑ a ∈ s, 2*(w a*(∑ b ∈ s, w b)) := by
          apply Finset.sum_congr rfl
          intro a _
          simp only [Finset.mul_sum]
        _ = 2*(∑ a ∈ s, w a*(∑ b ∈ s, w b)) := by
          simp only [Finset.mul_sum]
        _ = 2*((∑ a ∈ s, w a)*(∑ b ∈ s, w b)) := by
          rw [Finset.sum_mul]
        _ = _ := by ring

/-- On resonance the actual complex Fourier product equals the positive
coefficient weight used above. -/
theorem v54_resonant_complex_product (f : ℤ → ℂ) (a b c d : ℤ)
    (h : v54Resonant a b c d) :
    f a*f b*star (f c*f d) = ((‖f a‖^2*‖f b‖^2 : ℝ) : ℂ) := by
  rcases v54_integer_resonance a b c d h with ⟨hc,hd⟩ | ⟨hd,hc⟩
  · subst c; subst d
    rw [v28_star_self, norm_mul]
    push_cast <;> ring
  · subst c; subst d
    rw [mul_comm (f b) (f a), v28_star_self, norm_mul]
    push_cast <;> ring

/-- Fourier-polynomial fourth-moment coefficient bound after both
orthogonality selections have been applied. -/
theorem v54_complex_fourth_mass (s : Finset ℤ) (f : ℤ → ℂ) :
    (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      if v54Resonant a b c d then (f a*f b*star (f c*f d)).re else 0) ≤
        2*(∑ a ∈ s, ‖f a‖^2)^2 := by
  have he : (∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
      if v54Resonant a b c d then (f a*f b*star (f c*f d)).re else 0) =
      ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s,
        if v54Resonant a b c d then ‖f a‖^2*‖f b‖^2 else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    split_ifs with h
    · rw [v54_resonant_complex_product f a b c d h] <;> simp
    · rfl
  rw [he]
  exact v54_resonant_fourth_mass s (fun a => ‖f a‖^2) (by intro a ha; positivity)

end OpenAI086
