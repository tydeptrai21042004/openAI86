import Mathlib
import OpenAI086.FiniteDyadicBlockIndexBounds
import OpenAI086.FiniteDyadicWidthGrouping

/-! Generic additive dyadic blocks, independent of coordinates. -/
namespace OpenAI086

def v19Grouped {X : Type*} [AddCommGroup X]
    (blocks : List (ℕ × X)) (label : ℕ) : X :=
  (blocks.map (fun p => if p.1 = label then p.2 else 0)).sum

/-- Regrouping is an exact equality, not an estimate.  This general
statement is also useful outside the specific dyadic construction. -/
theorem v19_grouped_sum {X : Type*} [AddCommGroup X]
    (labels : Finset ℕ) (blocks : List (ℕ × X))
    (hsupport : ∀ p ∈ blocks, p.1 ∈ labels) :
    (∑ w ∈ labels, v19Grouped blocks w) =
      (blocks.map Prod.snd).sum := by
  classical
  induction blocks with
  | nil => simp [v19Grouped]
  | cons p rest ih =>
      obtain ⟨w, F⟩ := p
      have hw : w ∈ labels := hsupport (w, F) (by simp)
      have hrest : ∀ q ∈ rest, q.1 ∈ labels := by
        intro q hq
        exact hsupport q (by simp [hq])
      have ih' := ih hrest
      simp only [v19Grouped, List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib]
      have hsingle :
          (∑ t ∈ labels, if w = t then F else (0 : X)) = F := by
        simp [hw]
      rw [hsingle]
      exact congrArg (fun z : X => F + z) ih'

theorem v19_grouped_zero_of_absent {X : Type*} [AddCommGroup X]
    (pairs : List (ℕ × X)) (w : ℕ)
    (habsent : w ∉ pairs.map Prod.fst) :
    v19Grouped pairs w = 0 := by
  induction pairs with
  | nil => simp [v19Grouped]
  | cons p rest ih =>
      obtain ⟨v, F⟩ := p
      have hv : v ≠ w := by
        intro h
        apply habsent
        simp [h]
      have htail : w ∉ rest.map Prod.fst := by
        intro h
        apply habsent
        simp [h]
      simp [v19Grouped, hv, ih htail]

theorem v19_grouped_of_unique {X : Type*} [AddCommGroup X] :
    ∀ (pairs : List (ℕ × X)) (w : ℕ)
      (F : X),
      (w, F) ∈ pairs → (pairs.map Prod.fst).Nodup →
      v19Grouped pairs w = F := by
  intro pairs
  induction pairs with
  | nil =>
      intro w F hmem _
      simp at hmem
  | cons p ps ih =>
      intro w F hmem hnodup
      have hcons : (p.1 :: ps.map Prod.fst).Nodup := by
        simpa using hnodup
      obtain ⟨habsent, htailnodup⟩ := List.nodup_cons.mp hcons
      rcases List.mem_cons.mp hmem with hhead | htail
      · cases hhead
        have hz := v19_grouped_zero_of_absent ps w habsent
        change (if w = w then F else 0) + v19Grouped ps w = F
        simp [hz]
      · have hneq : p.1 ≠ w := by
          intro heq
          apply habsent
          have hw : w ∈ ps.map Prod.fst := by
            exact List.mem_map.mpr ⟨(w, F), htail, rfl⟩
          simpa [heq] using hw
        change (if p.1 = w then p.2 else 0) +
          v19Grouped ps w = F
        simp [hneq, ih w F htail htailnodup]


/-- Block contributions are differences of cumulative vectors. -/
def v19BlockPairs {X : Type*} [AddCommGroup X] (F : ℕ → X)
    (k start length : ℕ) : List (ℕ × X) :=
  (finiteDyadicPrefixBlocks k start length).map
    (fun b => (b.2, F (b.1 + b.2) - F b.1))

theorem v19_block_pairs_sum {X : Type*} [AddCommGroup X] (F : ℕ → X)
    (k : ℕ) : ∀ s n : ℕ, n ≤ 2^k →
      ((v19BlockPairs F k s n).map Prod.snd).sum = F (s+n) - F s := by
  induction k with
  | zero =>
    intro s n hn
    have h : n = 0 ∨ n = 1 := by simp at hn; omega
    rcases h with h | h <;> subst n <;> simp [v19BlockPairs, finiteDyadicPrefixBlocks]
  | succ k ih =>
    intro s n hn
    by_cases hf : n = 2^(k+1)
    · simp [v19BlockPairs, finiteDyadicPrefixBlocks, hf]
    · by_cases hl : n ≤ 2^k
      · simpa [v19BlockPairs, finiteDyadicPrefixBlocks, hf, hl] using ih s n hl
      · have hp : 2^(k+1) = 2^k + 2^k := by simp [pow_succ, mul_two]
        have ht : n - 2^k ≤ 2^k := by omega
        have he : s + 2^k + (n-2^k) = s+n := by omega
        have htail := ih (s+2^k) (n-2^k) ht
        change ((v19BlockPairs F (k+1) s n).map Prod.snd).sum = _
        simp only [v19BlockPairs, finiteDyadicPrefixBlocks, if_neg hf, if_neg hl,
          List.map_cons, List.sum_cons]
        change (F (s+2^k)-F s) + ((v19BlockPairs F k (s+2^k) (n-2^k)).map Prod.snd).sum = _
        rw [htail, he]
        abel

theorem v19_width_prefix {X : Type*} [AddCommGroup X] (F : ℕ → X)
    (k n : ℕ) (hn : n ≤ 2^k) :
    (∑ w ∈ finiteDyadicWidthSet k, v19Grouped (v19BlockPairs F k 0 n) w) = F n - F 0 := by
  have hs : ∀ p ∈ v19BlockPairs F k 0 n, p.1 ∈ finiteDyadicWidthSet k := by
    intro p hp
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hp
    exact finite_dyadic_width_mem_set k 0 n hn b hb
  rw [v19_grouped_sum _ _ hs]
  simpa using v19_block_pairs_sum F k 0 n hn

theorem v19_width_choice {X : Type*} [AddCommGroup X] (F : ℕ → X)
    (k n w : ℕ) (hn : n ≤ 2^k) :
    ∃ a : Bool, ∃ j : Fin (2^k),
      v19Grouped (v19BlockPairs F k 0 n) w =
        if a then F ((j.val+1)*w) - F (j.val*w) else 0 := by
  classical
  let bs := finiteDyadicPrefixBlocks k 0 n
  by_cases h : ∃ b : ℕ × ℕ, b ∈ bs ∧ b.2 = w
  · obtain ⟨b,hb,hw⟩ := h
    obtain ⟨j,hj⟩ := finite_dyadic_zero_base_blocks_aligned k n hn b hb
    have hj' : b.1 = j*b.2 := by simpa [Nat.mul_comm] using hj
    have hlt := finite_dyadic_aligned_block_index_lt k n hn b hb j hj'
    have hm : (b.2,F (b.1+b.2)-F b.1) ∈ v19BlockPairs F k 0 n :=
      List.mem_map.mpr ⟨b,hb,rfl⟩
    have hd : ((v19BlockPairs F k 0 n).map Prod.fst).Nodup := by
      simpa [v19BlockPairs, List.map_map, Function.comp_def] using
        finite_dyadic_prefix_widths_nodup k 0 n hn
    refine ⟨true,⟨j,hlt⟩,?_⟩
    rw [← hw, v19_grouped_of_unique _ _ _ hm hd]
    simp [hj', Nat.add_mul]
  · have hz : w ∉ (v19BlockPairs F k 0 n).map Prod.fst := by
      intro hm
      have hm' : w ∈ bs.map Prod.snd := by
        simpa [bs, v19BlockPairs, List.map_map, Function.comp_def] using hm
      obtain ⟨b,hb,he⟩ := List.mem_map.mp hm'
      exact h ⟨b,hb,he⟩
    refine ⟨false,⟨0,by positivity⟩,?_⟩
    simp [v19_grouped_zero_of_absent _ _ hz]

end OpenAI086
