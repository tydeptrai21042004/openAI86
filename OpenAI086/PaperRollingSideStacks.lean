import Mathlib

/-! Lemma 7.4 (pp.60–61): rolling side increment identity and exact
position/band selection by independent sign covariance. The analytic
energy control of the selected certified endpoint functions is not proved. -/
namespace OpenAI086

theorem v26_rolling_stack_increment {X : Type*} [AddCommGroup X]
    (Tr Tt : X →+ X) (Zr Zt Zb : X) :
    Tt (Zt-Zb)-Tr (Zr-Zb) =
      Tt (Zt-Zr)+(Tt (Zr-Zb)-Tr (Zr-Zb)) := by
  simp only [map_sub]
  abel

/-- A finite telescoping identity, valid for arbitrary additive groups. -/
theorem v26_side_prefix_telescoping {X : Type*} [AddCommGroup X]
    (W : ℕ → X) (b n : ℕ) :
    W (b+n) = W b+∑ j ∈ Finset.range n, (W (b+j+1)-W (b+j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih]
    rw [Nat.add_succ]
    abel

/-- A selector for independent Rademacher position and band indices.
The Kronecker covariance is the result of sign integration; here its
finite contraction is carried out exactly, including both positions. -/
theorem v26_select_matched_band {I J P : Type*} [Fintype I] [Fintype J] [Fintype P]
    [DecidableEq I] [DecidableEq J] [DecidableEq P]
    (a : I) (b : J) (z : I → J → P → P → ℝ) :
    (∑ i, ∑ j, ∑ p, ∑ q,
      (if i=a then 1 else 0)*(if j=b then 1 else 0)*
      (if p=q then 1 else 0)*z i j p q) = ∑ p, z a b p p := by
  simp [ite_mul, mul_ite]

end OpenAI086
