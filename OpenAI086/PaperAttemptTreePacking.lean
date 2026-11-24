import OpenAI086.Packing

/-! Lemma 3.1, finite rooted attempt families. The local child condition
is the input of the paper's lemma. The generation contraction is derived
from the parent assignment, rather than taken as another hypothesis. -/
namespace OpenAI086
open scoped BigOperators

variable {R : Type*} [DecidableEq R]

theorem v29_generation_contraction (level : ℕ → Finset R)
    (parent : R → R) (len : R → ℝ) (ρ : ℝ)
    (hp : ∀ n r, r ∈ level (n+1) → parent r ∈ level n)
    (hc : ∀ n r, r ∈ level n →
      (∑ s ∈ (level (n+1)).filter (fun s => parent s = r), len s) ≤ ρ * len r)
    (n : ℕ) :
    (∑ s ∈ level (n+1), len s) ≤ ρ * ∑ r ∈ level n, len r := by
  classical
  calc
    _ = ∑ s ∈ level (n+1), ∑ r ∈ level n, (if parent s = r then len s else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      symm
      rw [Finset.sum_eq_single (parent s)]
      · simp
      · intro r hr hne
        simp [Ne.symm hne]
      · intro hn
        exact (hn (hp n s hs)).elim
    _ = ∑ r ∈ level n, ∑ s ∈ level (n+1), (if parent s = r then len s else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ level n, ∑ s ∈ (level (n+1)).filter (fun s => parent s = r), len s := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_filter]
    _ ≤ ∑ r ∈ level n, ρ * len r := Finset.sum_le_sum (hc n)
    _ = _ := by rw [Finset.mul_sum]

/-- Both conclusions of Lemma 3.1 for finite generation lists. The root
length and each local contribution are supplied as actual node data. -/
theorem v29_attempt_tree_packing (level : ℕ → Finset R) (parent : R → R)
    (root : R) (len cost : R → ℝ) (A ρ : ℝ)
    (hroot : level 0 = {root}) (hlen : ∀ r, 0 ≤ len r)
    (hA : 0 ≤ A) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hp : ∀ n r, r ∈ level (n+1) → parent r ∈ level n)
    (hc : ∀ n r, r ∈ level n →
      (∑ s ∈ (level (n+1)).filter (fun s => parent s = r), len s) ≤ ρ * len r)
    (hcost : ∀ r, cost r ≤ A * len r) (N : ℕ) :
    (∑ n ∈ Finset.range N, ∑ r ∈ level n, len r) ≤ len root / (1-ρ) ∧
    (∑ n ∈ Finset.range N, ∑ r ∈ level n, cost r) ≤ A * len root / (1-ρ) := by
  let M : ℕ → ℝ := fun n => ∑ r ∈ level n, len r
  let C : ℕ → ℝ := fun n => ∑ r ∈ level n, cost r
  have hM : M 0 = len root := by simp [M, hroot]
  have hm0 : 0 ≤ M 0 := hM.symm ▸ hlen root
  have hs : ∀ n, M (n+1) ≤ ρ * M n :=
    v29_generation_contraction level parent len ρ hp hc
  have hC : ∀ n, C n ≤ A * M n := by
    intro n
    dsimp [C, M]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun r _ => hcost r)
  constructor
  · have h := packing_of_contracted_generations M ρ hρ0 hρ1 hm0 hs N
    rw [hM] at h
    exact h
  · have h := cost_of_packed_generations M C A ρ hA hρ0 hρ1 hm0 hs hC N
    rw [hM] at h
    exact h

end OpenAI086
