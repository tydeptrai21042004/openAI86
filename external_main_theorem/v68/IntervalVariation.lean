import TrilinearHT.Auto.Sec14_5bExportedSideEstimate

/-! Lemma 7.3: construct the coloring of the actual depth-increment
intervals (r,t]. The overlap cap counts intervals with multiplicity.
Empty increments can have any color because they have zero variation. -/
namespace OpenAI086.ReferenceV68
open Auto MeasureTheory
open scoped Classical BigOperators

/-- A finite family of integer-depth intervals of overlap at most m can be
colored with m colors. The proof removes a latest-starting interval. All
its remaining intersecting neighbors contain the same depth r(j)+1. -/
theorem depth_interval_coloring {ι : Type*} [Fintype ι]
    (r t : ι → ℕ) {m : ℕ} (hm : 0 < m)
    (hcap : ∀ d : ℕ, (Finset.univ.filter fun i : ι => r i < d ∧ d ≤ t i).card ≤ m) :
    ∃ col : ι → Fin m, ∀ i j, i ≠ j → col i = col j →
      Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r j) (t j)) := by
  classical
  have aux : ∀ n (s : Finset ι), s.card = n →
      ∃ col : ι → Fin m, ∀ i ∈ s, ∀ j ∈ s, i ≠ j → col i = col j →
        Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r j) (t j)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      by_cases hne : s.Nonempty
      · obtain ⟨a, ha, hamax⟩ := Finset.exists_max_image s r hne
        have hlt : (s.erase a).card < n := by
          have h := Finset.card_erase_of_mem ha
          have hpos : 0 < s.card := Finset.card_pos.mpr hne
          omega
        obtain ⟨col, hc⟩ := ih (s.erase a).card hlt (s.erase a) rfl
        let N := (s.erase a).filter fun j =>
          ¬ Disjoint (Finset.Ioc (r a) (t a)) (Finset.Ioc (r j) (t j))
        have hN : N.card < m := by
          by_cases hat : r a < t a
          · have hsub : insert a N ⊆ Finset.univ.filter (fun j : ι => r j < r a + 1 ∧ r a + 1 ≤ t j) := by
              intro j hj
              rw [Finset.mem_filter]
              refine ⟨Finset.mem_univ _, ?_⟩
              rcases Finset.mem_insert.mp hj with rfl | hj
              · omega
              · have hj' := Finset.mem_filter.mp hj
                have hjS : j ∈ s := (Finset.mem_erase.mp hj'.1).2
                have hstart := hamax j hjS
                have hw : ∃ d, d ∈ Finset.Ioc (r a) (t a) ∧ d ∈ Finset.Ioc (r j) (t j) := by
                  by_contra hn
                  apply hj'.2
                  apply Finset.disjoint_left.mpr
                  intro d hd hd'
                  exact hn ⟨d, hd, hd'⟩
                obtain ⟨d, hd, hd'⟩ := hw
                have hda := Finset.mem_Ioc.mp hd
                have hdj := Finset.mem_Ioc.mp hd'
                omega
            have hana : a ∉ N := by simp [N]
            have hcard := (Finset.card_le_card hsub).trans (hcap (r a + 1))
            rw [Finset.card_insert_of_notMem hana] at hcard
            omega
          · have hN0 : N = ∅ := by
              apply Finset.eq_empty_iff_forall_notMem.mpr
              intro j hj
              apply (Finset.mem_filter.mp hj).2
              apply Finset.disjoint_left.mpr
              intro d hd _
              have hda := Finset.mem_Ioc.mp hd
              omega
            simpa [hN0] using hm
        let used := N.image col
        have hused : used.card < m := lt_of_le_of_lt Finset.card_image_le hN
        have hex : ∃ c : Fin m, c ∉ used := by
          by_contra! h
          have heq : used = Finset.univ := by ext c; simp [h c]
          rw [heq, Finset.card_univ, Fintype.card_fin] at hused
          omega
        obtain ⟨c, hfree⟩ := hex
        let newcol : ι → Fin m := fun j => if j = a then c else col j
        have hnew : ∀ j ∈ s, j ≠ a → newcol j = newcol a →
            Disjoint (Finset.Ioc (r a) (t a)) (Finset.Ioc (r j) (t j)) := by
          intro j hj hja heq
          have hcj : col j = c := by simpa [newcol, hja] using heq
          by_contra hnd
          have hjN : j ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hja, hj⟩, hnd⟩
          apply hfree
          exact Finset.mem_image.mpr ⟨j, hjN, hcj⟩
        refine ⟨newcol, ?_⟩
        intro i hi j hj hij heq
        by_cases hia : i = a
        · subst i
          exact hnew j hj (Ne.symm hij) heq.symm
        · by_cases hja : j = a
          · subst j
            exact (hnew i hi hia heq).symm
          · exact hc i (Finset.mem_erase.mpr ⟨hia, hi⟩) j
              (Finset.mem_erase.mpr ⟨hja, hj⟩) hij (by simpa [newcol, hia, hja] using heq)
      · refine ⟨fun _ => ⟨0, hm⟩, ?_⟩
        intro i hi
        exact (hne ⟨i, hi⟩).elim
  obtain ⟨col, hc⟩ := aux (Finset.univ : Finset ι).card Finset.univ rfl
  exact ⟨col, fun i j hij he => hc i (Finset.mem_univ _) j (Finset.mem_univ _) hij he⟩

/-- Apply the constructed coloring directly to the certified endpoint
variation capacity, without assuming a coloring as input. -/
theorem variation_of_overlap {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)
    {γ V : Type*} [Fintype V] (Gs : Finset γ) (Z : γ → ℤ → ColumnL2 V)
    (ok : γ → ℤ × ℤ → Prop) {B : ℝ} (hB : A.VarCap Gs Z ok B)
    {m : ℕ} (hm : 0 < m) {ι : Type} [Fintype ι] (r t : ι → ℕ)
    (hrt : ∀ i, r i ≤ t i) (htd : ∀ i, t i ≤ A.treeDepth)
    (hcap : ∀ d : ℕ, (Finset.univ.filter fun i : ι => r i < d ∧ d ≤ t i).card ≤ m)
    (Ec : γ → ι → Finset (ℤ × ℤ))
    (hEc : ∀ g i, ∀ J ∈ Ec g i, J ∈ A.cells ∧ J.1 = A.R.1 + t i ∧ ok g J) :
    ∑ g ∈ Gs, ∑ i, ‖columnL2Restriction
      (⋃ J ∈ Ec g i, dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (Z g (A.R.1 + t i) - Z g (A.R.1 + r i))‖ ^ 2 ≤ (m : ℝ) * B := by
  classical
  obtain ⟨col, hc⟩ := depth_interval_coloring r t hm hcap
  let f (g : γ) (i : ι) : ℝ := ‖columnL2Restriction
      (⋃ J ∈ Ec g i, dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (Z g (A.R.1 + t i) - Z g (A.R.1 + r i))‖ ^ 2
  have hclass (c : Fin m) : ∑ g ∈ Gs, ∑ i, (if col i = c then f g i else 0) ≤ B := by
    let rc : ι → ℕ := fun i => if col i = c then r i else 0
    let tc : ι → ℕ := fun i => if col i = c then t i else 0
    let Ecc : γ → ι → Finset (ℤ × ℤ) := fun g i => if col i = c then Ec g i else ∅
    have hrc : ∀ i, rc i ≤ tc i := by intro i; by_cases h : col i = c <;> simp [rc, tc, h, hrt]
    have htc : ∀ i, tc i ≤ A.treeDepth := by intro i; by_cases h : col i = c <;> simp [tc, h, htd]
    have hd : ∀ i j, i ≠ j → Disjoint (Finset.Ioc (rc i) (tc i)) (Finset.Ioc (rc j) (tc j)) := by
      intro i j hij
      by_cases hi : col i = c <;> by_cases hj : col j = c
      · simpa [rc, tc, hi, hj] using hc i j hij (hi.trans hj.symm)
      · simp [rc, tc, hi, hj]
      · simp [rc, tc, hi, hj]
      · simp [rc, tc, hi, hj]
    have hec : ∀ g i, ∀ J ∈ Ecc g i, J ∈ A.cells ∧ J.1 = A.R.1 + tc i ∧ ok g J := by
      intro g i J hJ
      by_cases h : col i = c
      · simpa [tc, h] using hEc g i J (by simpa [Ecc, h] using hJ)
      · simp [Ecc, h] at hJ
    have h := hB rc tc hrc hd htc Ecc hec
    convert h using 1
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : col i = c <;> simp [f, rc, tc, Ecc, hi]
  change (∑ g ∈ Gs, ∑ i, f g i) ≤ _
  calc
    _ = ∑ g ∈ Gs, ∑ i, ∑ c : Fin m, (if col i = c then f g i else 0) := by simp
    _ = ∑ g ∈ Gs, ∑ c : Fin m, ∑ i, (if col i = c then f g i else 0) := by
      apply Finset.sum_congr rfl
      intro g _
      exact Finset.sum_comm
    _ = ∑ c : Fin m, ∑ g ∈ Gs, ∑ i, (if col i = c then f g i else 0) := Finset.sum_comm
    _ ≤ ∑ _c : Fin m, B := Finset.sum_le_sum fun c _ => hclass c
    _ = _ := by simp

end OpenAI086.ReferenceV68
#print axioms OpenAI086.ReferenceV68.depth_interval_coloring
#print axioms OpenAI086.ReferenceV68.variation_of_overlap
