import OpenAI086.PaperAttemptTreePacking

/-! Paper Lemma 3.1, finite actual interval roots, summed exactly once.
The input is the finite attempt tree described by the paper; no bound on
its depth or cardinality enters the result. The child-root contraction
is the hypothesis of Lemma 3.1, not a conclusion of the stopping rules. -/
noncomputable section
namespace OpenAI086
open scoped BigOperators

/-- Partition a finite set by its generation, and sum every root once. -/
theorem v43_sum_generations {R : Type*} [DecidableEq R]
    (S : Finset R) (depth : R → ℕ) (N : ℕ)
    (hN : ∀ r ∈ S, depth r < N) (f : R → ℝ) :
    (∑ n ∈ Finset.range N, ∑ r ∈ S.filter (fun r => depth r = n), f r) =
      ∑ r ∈ S, f r := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_eq_single (depth r)]
  · simp
  · intro n _ hn
    simp [Ne.symm hn]
  · intro hn
    exact (hn (Finset.mem_range.mpr (hN r hr))).elim

/-- Actual Lebesgue length of the half-open real interval. -/
def v43IntervalLength (r : ℝ × ℝ) : ℝ :=
  (MeasureTheory.volume (Set.Ico r.1 r.2)).toReal

/-- The paper-facing packing statement, for the finite set of all attempt
roots. Depth is generation in the attempt tree, not dyadic spatial depth.
The finite tree can be encoded by endpoint pairs because every attempt
root in the construction is distinct. The child-root hypothesis is
required only on actual roots. -/
def V43Lemma31Goal : Prop :=
  ∀ (S : Finset (ℝ × ℝ)) (root : ℝ × ℝ)
    (depth : ℝ × ℝ → ℕ) (parent : ℝ × ℝ → ℝ × ℝ)
    (cost : ℝ × ℝ → ℝ) (A ρ : ℝ) (N : ℕ),
    (∀ r, (r ∈ S ∧ depth r = 0) ↔ r = root) →
    (∀ r ∈ S, depth r < N) →
    (∀ r ∈ S, 0 < depth r → parent r ∈ S ∧ depth (parent r) + 1 = depth r) →
    0 ≤ A → 0 ≤ ρ → ρ < 1 →
    (∀ r ∈ S, (∑ s ∈ S.filter (fun s => depth s = depth r + 1 ∧ parent s = r),
      v43IntervalLength s) ≤ ρ * v43IntervalLength r) →
    (∀ r ∈ S, cost r ≤ A * v43IntervalLength r) →
    (∑ r ∈ S, v43IntervalLength r) ≤ v43IntervalLength root / (1-ρ) ∧
    (∑ r ∈ S, cost r) ≤ A * v43IntervalLength root / (1-ρ)

/-- Both length and assigned-cost conclusions of Lemma 3.1. No
pre-assumed generation contraction, packing estimate or numerical cutoff
bound is used. The cutoff N merely enumerates the given finite tree. -/
theorem v43_lemma31 : V43Lemma31Goal := by
  classical
  intro S root depth parent cost A ρ N hroot hN hp hA hρ0 hρ1 hc hcost
  let level : ℕ → Finset (ℝ × ℝ) := fun n => S.filter (fun r => depth r = n)
  have hlevel0 : level 0 = {root} := by
    ext r
    simpa [level, Finset.mem_filter] using hroot r
  have hparent : ∀ n r, r ∈ level (n+1) → parent r ∈ level n := by
    intro n r hr
    have h := Finset.mem_filter.mp hr
    have hd0 := h.2
    have hpos : 0 < depth r := by omega
    obtain ⟨hs, hd⟩ := hp r h.1 hpos
    exact Finset.mem_filter.mpr ⟨hs, by omega⟩
  have hchild : ∀ n r, r ∈ level n →
      (∑ s ∈ (level (n+1)).filter (fun s => parent s = r), v43IntervalLength s)
        ≤ ρ * v43IntervalLength r := by
    intro n r hr
    have h := Finset.mem_filter.mp hr
    have he : (level (n+1)).filter (fun s => parent s = r) =
        S.filter (fun s => depth s = depth r + 1 ∧ parent s = r) := by
      ext s
      simp [level, h.2, and_assoc]
    rw [he]
    exact hc r h.1
  have hlen : ∀ r, 0 ≤ v43IntervalLength r := fun _ => ENNReal.toReal_nonneg
  let cost' : ℝ × ℝ → ℝ := fun r => if r ∈ S then cost r else 0
  have hcost' : ∀ r, cost' r ≤ A * v43IntervalLength r := by
    intro r
    by_cases hr : r ∈ S
    · simpa [cost', hr] using hcost r hr
    · simpa [cost', hr] using mul_nonneg hA (hlen r)
  obtain ⟨hL,hC⟩ := v29_attempt_tree_packing level parent root v43IntervalLength cost'
    A ρ hlevel0 hlen hA hρ0 hρ1 hparent hchild hcost' N
  change (∑ n ∈ Finset.range N, ∑ r ∈ S.filter (fun r => depth r = n),
    v43IntervalLength r) ≤ _ at hL
  change (∑ n ∈ Finset.range N, ∑ r ∈ S.filter (fun r => depth r = n), cost' r) ≤ _ at hC
  rw [v43_sum_generations S depth N hN v43IntervalLength] at hL
  rw [v43_sum_generations S depth N hN cost'] at hC
  have he : (∑ r ∈ S, cost' r) = ∑ r ∈ S, cost r := by
    apply Finset.sum_congr rfl
    intro r hr
    simp [cost', hr]
  rw [he] at hC
  exact ⟨hL,hC⟩

end OpenAI086
