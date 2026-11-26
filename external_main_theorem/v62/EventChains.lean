import TrilinearHT.Auto.Sec13_3BesselRowsLinearSideEnergy
import SourceV56EntryRank

/-! Paper Lemma 8.6 on a sequence of actual ModeSystem pre-cells.
The temporal inclusion is proved using the reference transport theorem,
rather than being postulated as in V61. The caller must still supply the
actual geometric link witnesses, multiplicity budgets, and printed
floor-log bad-density hypothesis. -/
namespace OpenAI086.ReferenceV62
open Auto OpenAI086.AdaptedV56
open scoped BigOperators

/-- Failure of the reference's nine-tenths size test implies failure of
 the paper's equal-floor-log size test. The converse is not valid. -/
theorem floorlog_ne_of_ratio (n m : ℕ) (hn : 0 < n) (hratio : 10*n < 9*m) :
    v57FloorLog n ≠ v57FloorLog m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : 0 < m := by omega
  have hrat : (10 : ℝ) * n < 9 * m := by exact_mod_cast hratio
  have hnm : (11/10 : ℝ) * n ≤ m := by linarith
  have hb : 0 < Real.log (11/10 : ℝ) := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (mul_pos (by norm_num : (0:ℝ) < 11/10) hnR) hnm
  rw [Real.log_mul (by norm_num : (11/10:ℝ) ≠ 0) hnR.ne'] at hlog
  have hstep : Real.log (n : ℝ) / Real.log (11/10:ℝ) + 1 ≤
      Real.log (m : ℝ) / Real.log (11/10:ℝ) := by
    apply (le_div_iff₀ hb).mpr
    rw [add_mul, div_mul_cancel₀ _ hb.ne', one_mul]
    linarith
  intro heq
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hfloor : (v57FloorLog n : ℝ) ≤ Real.log (n:ℝ) / Real.log (11/10:ℝ) :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hn1) hb.le)
  have hceil : Real.log (m:ℝ) / Real.log (11/10:ℝ) < (v57FloorLog m : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [← heq] at hceil
  linarith

/-- For a reference failure caused by too few good primaries, the
paper's bad fraction exceeds 1/10 if its exceptional/bad set covers all
non-good primaries. This is the required one-sided comparison. -/
open Classical in
theorem bad_fraction_of_ratio {P : Type*} [DecidableEq P]
    (C X Y : Finset P) (good : P → Prop) [DecidablePred good]
    (hcover : ∀ p ∈ C, ¬ good p → p ∈ X ∪ Y)
    (hfail : 10*(C.filter good).card < 9*C.card) :
    (1/10 : ℝ) < (((X ∪ Y) ∩ C).card : ℝ)/C.card := by
  have hcard := Finset.card_filter_add_card_filter_not (s := C) good
  have hsub : C.filter (fun p => ¬ good p) ⊆ (X ∪ Y) ∩ C := by
    intro p hp
    obtain ⟨hpC,hpg⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_inter.mpr ⟨hcover p hpC hpg,hpC⟩
  have hbound := Finset.card_le_card hsub
  have hc : 0 < C.card := by omega
  have hcR : (0:ℝ) < C.card := by exact_mod_cast hc
  have h : C.card < 10*((X ∪ Y) ∩ C).card := by omega
  apply (lt_div_iff₀ hcR).mpr
  have hR : (C.card : ℝ) < 10 * (((X ∪ Y) ∩ C).card : ℝ) := by exact_mod_cast h
  linarith

open Classical in
theorem linked_event_floorlog {Gd : RealDyadicGrid} {Mc : ℕ}
    (Ms : ModeSystem Gd Mc) (S : ModeSchedule) (hA0 : 6 ≤ S.A0)
    (b : ℕ → ℤ) (Jc : ℕ → ℤ × ℤ)
    (x : ∀ i, Ms.alive (ancAt Gd (Jc i) (b i - 4 * S.K)))
    (N J Δ M A B : ℕ) (δ β : ℝ)
    (X : ℕ → Finset Ms.Key) (Y : ℕ → ℕ → Finset Ms.Key)
    (hδ : 0 < δ) (hβ : 0 < β)
    (hcell : ∀ i, (Jc i).1 = b i - 2 * S.K)
    (hstep : ∀ i < N, b i + 3 * S.K ≤ b (i+1))
    (hsub : ∀ i < N, dyadicGridCell Gd (Jc (i+1)).1 (Jc (i+1)).2 ⊆
      dyadicGridCell Gd (Jc i).1 (Jc i).2)
    (hgeom : ∀ i < N, ∃ m m' : Ms.Md,
      m ∈ ((Ms.blockComps S hA0 (b i) (Jc i)).E 0 (x i)).map
        ⟨Subtype.val, Subtype.val_injective⟩ ∧
      m' ∈ ((Ms.blockComps S hA0 (b (i+1)) (Jc (i+1))).E 0 (x (i+1))).map
        ⟨Subtype.val, Subtype.val_injective⟩ ∧
      (m = m' ∨ Ms.pre0Edge S (Jc (i+1)) m m'))
    (hM : ∀ i h, ((Ms.blockComps S hA0 (b i) (Jc i)).labels
      ((Ms.blockComps S hA0 (b i) (Jc i)).F h (x i))).card ≤ M)
    (hA : ∀ i p, ((Finset.range (J+1)).filter fun h => p ∈ Y i h).card ≤ A)
    (hB : ∀ p, ((Finset.range (N+1)).filter fun i => p ∈ X i).card ≤ B)
    (hbad : ∀ i ≤ N, δ*(J+1 : ℕ) < ∑ h ∈ Finset.range (J+1),
      if v57Bad v57FloorLog
        (fun i h => (Ms.blockComps S hA0 (b i) (Jc i)).labels
          ((Ms.blockComps S hA0 (b i) (Jc i)).E h (x i)))
        (fun i h => (Ms.blockComps S hA0 (b i) (Jc i)).labels
          ((Ms.blockComps S hA0 (b i) (Jc i)).F h (x i))) X Y Δ β i h then (1:ℝ) else 0)
    (hbudget : 2*((Δ:ℝ)*(v57FloorLog M+1) + (A:ℝ)*(harmonic M:ℝ)/β) ≤ δ*(J+1 : ℕ)) :
    ((N+1 : ℕ):ℝ) < 2*((v57FloorLog M:ℝ) + (B:ℝ)*(harmonic M:ℝ)/β)/δ := by
  apply v57_lemma86 N J Δ M A B δ β
    (fun i h => (Ms.blockComps S hA0 (b i) (Jc i)).labels
      ((Ms.blockComps S hA0 (b i) (Jc i)).E h (x i)))
    (fun i h => (Ms.blockComps S hA0 (b i) (Jc i)).labels
      ((Ms.blockComps S hA0 (b i) (Jc i)).F h (x i))) X Y hδ hβ
  · intro i h
    exact ⟨_, Finset.mem_image_of_mem _ ((Ms.blockComps S hA0 (b i) (Jc i)).E_self h (x i))⟩
  · intro i h
    exact Finset.image_subset_image ((Ms.blockComps S hA0 (b i) (Jc i)).E_le_F h (x i))
  · intro i hi h
    obtain ⟨m,m',hm,hm',hl⟩ := hgeom i hi
    exact Ms.link_labels S hA0 (hcell i) (hcell (i+1)) (hstep i hi) (hsub i hi)
      (x i) (x (i+1)) hm hm' hl h
  · intro i h h' hh
    exact Finset.image_subset_image ((Ms.blockComps S hA0 (b i) (Jc i)).E_mono h h' (x i) hh)
  · intro i h h' hh
    exact Finset.image_subset_image ((Ms.blockComps S hA0 (b i) (Jc i)).F_mono h h' (x i) hh)
  · exact hM
  · exact hA
  · exact hB
  · exact hbad
  · exact hbudget

end OpenAI086.ReferenceV62
#print axioms OpenAI086.ReferenceV62.linked_event_floorlog
#print axioms Auto.ModeSystem.link_labels
#print axioms OpenAI086.ReferenceV62.floorlog_ne_of_ratio
#print axioms OpenAI086.ReferenceV62.bad_fraction_of_ratio
