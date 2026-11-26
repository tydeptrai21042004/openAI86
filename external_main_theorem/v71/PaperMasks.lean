/-! Section 9.1: exact first-success mask expansion for finite tuples of
paper-core modes, using the actual component families from Section 8.
The mask identity is reused from the Apache-2.0 reference, with the stronger
paper-specific predicate and its own common-success bound. -/
import ReferenceV70PaperCounting
import TrilinearHT.Auto.Sec15_1ExactCommonHeightSelection

namespace OpenAI086.ReferenceV71
open Auto
open scoped BigOperators

/-- The finite product of retained core-mode lists admits an exact
first-success role-mask expansion. This includes all failed-word lengths,
with no truncation or extra normalizing factor. -/
open Classical in
theorem paper_mode_masks {m₀ : ℕ} {M P : Fin m₀ → Type*}
    [∀ j, DecidableEq (M j)] [∀ j, DecidableEq (P j)]
    (C : ∀ j, ModeComponents (M j) (P j)) (Δ : ℕ)
    (goodP : ∀ j, ℕ → P j → Prop) [∀ j h, DecidablePred (goodP j h)]
    (T : ∀ j, Finset (M j)) {J : ℕ} (hJ : 2 ≤ J) {δ : ℝ}
    (hδ : 0 < δ) (hδ16 : δ ≤ 1/16) (hsmall : 2*(m₀:ℝ)*δ < 1)
    (hcore : ∀ j x, x ∈ T j → (C j).PaperCore Δ (goodP j) J δ x)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : (∀ j, M j) → E) :
    let H := ModeComponents.upperHeights J δ
    let good := fun j h x => (C j).PaperGood Δ (goodP j) h x
    HasSum (fun n : ℕ => ∑ a : Fin n → Fin m₀,
      ∑ w ∈ Fintype.piFinset (fun _ : Fin n => H), ∑ h ∈ H,
      ((H.card : ℝ)^(n+1))⁻¹ • ∑ r ∈ (Fintype.piFinset T).filter
        (fun r => ∀ j, roleMask (good j) j a w h (r j)), F r)
      (∑ r ∈ Fintype.piFinset T, F r) := by
  classical
  dsimp only
  apply Auto.first_success_masked
  intro r hr
  have hr' : ∀ j, r j ∈ T j := by simpa only [Fintype.mem_piFinset] using hr
  have hc := OpenAI086.ReferenceV70.paper_common_height C Δ goodP r hJ hδ hδ16 hsmall
    (fun j => hcore j (r j) (hr' j))
  dsimp only at hc
  let H := ModeComponents.upperHeights J δ
  have hp : 0 < ((H.filter fun h => ∀ j, h ∉ (C j).paperBadHeights Δ (goodP j) J (r j)).card : ℝ) /
      H.card := lt_of_lt_of_le (by linarith) hc.1
  have hnum : 0 < (H.filter fun h => ∀ j, h ∉ (C j).paperBadHeights Δ (goodP j) J (r j)).card := by
    by_contra hn
    have hz : (H.filter fun h => ∀ j, h ∉ (C j).paperBadHeights Δ (goodP j) J (r j)).card = 0 := by omega
    rw [hz] at hp
    simp at hp
  obtain ⟨h,hh⟩ := Finset.card_pos.mp hnum
  obtain ⟨hhH,hhgood⟩ := Finset.mem_filter.mp hh
  have hrange : h ∈ Finset.range (J+1) := (Finset.mem_filter.mp hhH).1
  refine ⟨h, Finset.mem_filter.mpr ⟨hhH,?_⟩⟩
  intro j
  by_contra hng
  exact hhgood j (Finset.mem_filter.mpr ⟨hrange,hng⟩)

end OpenAI086.ReferenceV71
#print axioms OpenAI086.ReferenceV71.paper_mode_masks
