import Mathlib

/-! The finite pigeonhole step in an alternative bounded-dependence proof.
For d+1 integer vectors in a d-dimensional box, encode the sums with
coefficients in [0,K]. This lemma proves an actual collision and converts
it into a nonzero bounded integer relation, without assuming independence
or a Cramer-minor selection. The next theorem constructs the concrete range encoding and proves the
cardinal comparison for an explicit coefficient budget. -/
namespace OpenAI086
open scoped BigOperators

/-- If the number of coefficient choices exceeds the number of encoded
sums, and the encoding distinguishes different vector sums, then a
bounded nonzero integer relation exists. The finite encoding hypotheses
are explicit; this is not yet the rational-height lemma. -/
theorem v32_integer_relation_from_box {I J F : Type*} [Fintype I] [Fintype F]
    (K : ℕ) (v : I → J → ℤ) (enc : (I → Fin (K+1)) → F)
    (hcard : Fintype.card F < Fintype.card (I → Fin (K+1)))
    (henc : ∀ a b, enc a = enc b → ∀ j,
      (∑ i, ((a i).val:ℤ) * v i j : ℤ) = ∑ i, ((b i).val:ℤ) * v i j) :
    ∃ c : I → ℤ, (∃ i, c i ≠ 0) ∧ (∀ i, |c i| ≤ (K:ℤ)) ∧
      ∀ j, (∑ i, c i * v i j) = 0 := by
  classical
  have hn : ¬ Function.Injective enc := by
    intro hi
    exact (not_le_of_gt hcard) (Fintype.card_le_of_injective enc hi)
  unfold Function.Injective at hn
  push_neg at hn
  obtain ⟨a, b, hab, hne⟩ := hn
  let c : I → ℤ := fun i => ((a i).val:ℤ) - ((b i).val:ℤ)
  refine ⟨c, ?_, ?_, ?_⟩
  · by_contra hh
    push_neg at hh
    apply hne
    funext i
    apply Fin.ext
    have hi := hh i
    dsimp [c] at hi
    omega
  · intro i
    have ha := (a i).isLt
    have hb := (b i).isLt
    dsimp [c]
    rw [abs_le]
    constructor <;> omega
  · intro j
    have h := henc a b hab j
    dsimp [c]
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h

/-- Bounded integer dependence for d+1 vectors in Z^d, with no rank
hypothesis. The coefficient bound is explicit and its logarithm is
polynomial in d and log M. -/
theorem v32_integer_box_dependence (d M : ℕ)
    (v : Fin (d+1) → Fin d → ℤ)
    (hv : ∀ i j, |v i j| ≤ (M:ℤ)) :
    ∃ c : Fin (d+1) → ℤ, (∃ i, c i ≠ 0) ∧
      (∀ i, |c i| ≤ (((2*(d+1)*M+1)^d : ℕ):ℤ)) ∧
      ∀ j, (∑ i, c i * v i j) = 0 := by
  classical
  let A : ℕ := 2*(d+1)*M+1
  let K : ℕ := A^d
  let B : ℕ := (d+1)*M*K
  let S (a : Fin (d+1) → Fin (K+1)) (j : Fin d) : ℤ :=
    ∑ i, ((a i).val:ℤ) * v i j
  have hb (a : Fin (d+1) → Fin (K+1)) (j : Fin d) : |S a j| ≤ (B:ℤ) := by
    calc
      |S a j| ≤ ∑ i : Fin (d+1), |((a i).val:ℤ) * v i j| := by
        dsimp [S]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (d+1), (K:ℤ)*(M:ℤ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ ((a i).val:ℤ))]
        have hki : ((a i).val:ℤ) ≤ (K:ℤ) := by
          have h := (a i).isLt
          omega
        exact mul_le_mul hki (hv i j) (abs_nonneg _) (by positivity)
      _ = (B:ℤ) := by simp [B, mul_assoc]
  have hnonneg (a : Fin (d+1) → Fin (K+1)) (j : Fin d) :
      0 ≤ S a j + (B:ℤ) := by
    have h := (abs_le.mp (hb a j)).1
    omega
  let enc (a : Fin (d+1) → Fin (K+1)) (j : Fin d) : Fin (2*B+1) :=
    ⟨(S a j + (B:ℤ)).toNat, by
      have h := (abs_le.mp (hb a j)).2
      have ht := Int.toNat_of_nonneg (hnonneg a j)
      omega⟩
  have henc : ∀ a b, enc a = enc b → ∀ j, S a j = S b j := by
    intro a b he j
    have he' := congrArg (fun f : Fin d → Fin (2*B+1) => (f j).val) he
    change (S a j + (B:ℤ)).toNat = (S b j + (B:ℤ)).toNat at he'
    have ha := Int.toNat_of_nonneg (hnonneg a j)
    have hb' := Int.toNat_of_nonneg (hnonneg b j)
    omega
  have hwidth : 2*B+1 ≤ A*(K+1) := by
    calc
      2*B+1 ≤ 2*B+1+(2*(d+1)*M+K) := by omega
      _ = A*(K+1) := by dsimp [A, B]; ring
  have hp : (2*B+1)^d ≤ (A*(K+1))^d := by gcongr
  have hstrict : (2*B+1)^d < (K+1)^(d+1) := by
    calc
      _ ≤ (A*(K+1))^d := hp
      _ = K*(K+1)^d := by rw [mul_pow]; rfl
      _ < (K+1)*(K+1)^d := by
        gcongr <;> omega
      _ = _ := by rw [pow_succ]; ac_rfl
  have hcard : Fintype.card (Fin d → Fin (2*B+1)) <
      Fintype.card (Fin (d+1) → Fin (K+1)) := by
    simpa [Fintype.card_fun] using hstrict
  have h := v32_integer_relation_from_box K v enc hcard henc
  simpa [K, A] using h

end OpenAI086
