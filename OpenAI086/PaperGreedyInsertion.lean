import Mathlib

/-! Lemmas 5.4 and 5.6 (pp.33–36): charge an inserted atom to
projection-energy increments, and aggregate simultaneous child refits.
The local detection theorem and actual nested dyadic construction are
separate obligations. -/
namespace OpenAI086

/-- A residual moment at least ρ against a vector of norm ≤ K,
when the new residual annihilates that vector, forces a projection jump. -/
theorem v26_fresh_moment_jump {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (x old new φ : X) (ρ K : ℝ)
    (hρ : 0 ≤ ρ) (hK : 0 < K)
    (hm : ρ ≤ |inner ℝ (x-old) φ|) (hn : inner ℝ (x-new) φ = 0)
    (hφ : ‖φ‖ ≤ K) : ρ/K ≤ ‖new-old‖ := by
  have he : inner ℝ (x-old) φ = inner ℝ (new-old) φ := by
    rw [inner_sub_left] at hn ⊢
    linarith
  rw [he] at hm
  have hc : |inner ℝ (new-old) φ| ≤ ‖new-old‖*‖φ‖ := by
    rw [abs_le]
    constructor
    · have hh := real_inner_le_norm (-(new-old)) φ
      rw [inner_neg_left, norm_neg] at hh
      linarith
    · exact real_inner_le_norm _ _
  apply (div_le_iff₀ hK).2
  calc
    ρ ≤ |inner ℝ (new-old) φ| := hm
    _ ≤ ‖new-old‖*‖φ‖ := hc
    _ ≤ ‖new-old‖*K := mul_le_mul_of_nonneg_left hφ (norm_nonneg _)
    _ = K*‖new-old‖ := mul_comm _ _

/-- Total charge of all successful insertions is bounded by telescoping
energy, with no factor for the number of projection depths. -/
theorem v26_insertion_energy_charge (N : ℕ) (E w : ℕ → ℝ) (c : ℝ)
    (h : ∀ n < N, c*w n ≤ E (n+1)-E n) :
    c*(∑ n ∈ Finset.range N, w n) ≤ E N-E 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
    have ha := ih (fun j hj => h j (by omega))
    have hb := h n (by omega)
    rw [Finset.sum_range_succ, mul_add]
    linarith

/-- A coarse moment lower bound controls childwise energy by weighted
Cauchy–Schwarz; weights are child lengths, and need not be uniform. -/
theorem v26_child_moment_energy {I : Type*} (s : Finset I)
    (w a : I → ℝ) (W ρ : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hW : ∑ i ∈ s, w i = W) (hWpos : 0 < W) (hρ : 0 ≤ ρ)
    (hm : W*ρ ≤ ∑ i ∈ s, w i*a i) :
    W*ρ^2 ≤ ∑ i ∈ s, w i*a i^2 := by
  have hh : 0 ≤ ∑ i ∈ s, w i*(a i-ρ)^2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  have he : (∑ i ∈ s, w i*(a i-ρ)^2) =
      (∑ i ∈ s, w i*a i^2)-2*ρ*(∑ i ∈ s, w i*a i)+ρ^2*W := by
    rw [← hW, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hh
  have hmul := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2*ρ)
  nlinarith

end OpenAI086
