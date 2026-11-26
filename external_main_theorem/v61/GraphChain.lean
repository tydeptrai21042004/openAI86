import TrilinearHT.Auto.Sec13_3BesselRowsLinearSideEnergy
import SourceV56EntryRank

/-! V61. Compose the paper's corrected floor-log chain candidate with
actual reference PRE/CURRENT component data. Unlike the reference's
ratio test, the bad predicate here is the printed floor-log predicate.
The chronological links and multiplicity bounds remain explicit inputs. -/
namespace OpenAI086.ReferenceV61
open scoped BigOperators
open Auto
open OpenAI086.AdaptedV56

/-- The terminal PRE-to-CURRENT primary inclusion follows at EVERY
position, independently of the existence of a later event. -/
theorem primary_inclusion {P : Type*} [DecidableEq P] (Mode : ℕ → Type*)
    [∀ i, DecidableEq (Mode i)] (C : ∀ i, ModeComponents (Mode i) P)
    (x : ∀ i, Mode i) (i h : ℕ) :
    (C i).labels ((C i).E h (x i)) ⊆ (C i).labels ((C i).F h (x i)) :=
  Finset.image_subset_image ((C i).E_le_F h (x i))

/-- Corrected Lemma 8.6 specialized to the reference's component structure.
No terminal inclusion or monotonicity of the label sets is assumed separately. -/
open Classical in
theorem floorlog_component_chain {P : Type*} [DecidableEq P]
    (Mode : ℕ → Type*) [∀ i, DecidableEq (Mode i)]
    (C : ∀ i, ModeComponents (Mode i) P) (x : ∀ i, Mode i)
    (N J Δ M A B : ℕ) (δ β : ℝ) (X : ℕ → Finset P) (Y : ℕ → ℕ → Finset P)
    (hδ : 0 < δ) (hβ : 0 < β)
    (hlink : ∀ i < N, ∀ h, (C i).labels ((C i).F h (x i)) ⊆
      (C (i+1)).labels ((C (i+1)).E h (x (i+1))))
    (hM : ∀ i h, ((C i).labels ((C i).F h (x i))).card ≤ M)
    (hA : ∀ i p, ((Finset.range (J+1)).filter fun h => p ∈ Y i h).card ≤ A)
    (hB : ∀ p, ((Finset.range (N+1)).filter fun i => p ∈ X i).card ≤ B)
    (hbad : ∀ i ≤ N, δ*(J+1 : ℕ) < ∑ h ∈ Finset.range (J+1),
      if v57Bad v57FloorLog (fun i h => (C i).labels ((C i).E h (x i)))
        (fun i h => (C i).labels ((C i).F h (x i))) X Y Δ β i h then (1:ℝ) else 0)
    (hbudget : 2*((Δ:ℝ)*(v57FloorLog M+1) + (A:ℝ)*(harmonic M:ℝ)/β) ≤ δ*(J+1 : ℕ)) :
    ((N+1 : ℕ):ℝ) < 2*((v57FloorLog M:ℝ) + (B:ℝ)*(harmonic M:ℝ)/β)/δ := by
  apply v57_lemma86 N J Δ M A B δ β
    (fun i h => (C i).labels ((C i).E h (x i)))
    (fun i h => (C i).labels ((C i).F h (x i))) X Y hδ hβ
  · intro i h
    exact ⟨(C i).π (x i), Finset.mem_image_of_mem _ ((C i).E_self h (x i))⟩
  · exact primary_inclusion Mode C x
  · exact hlink
  · intro i h h' hh
    exact Finset.image_subset_image ((C i).E_mono h h' (x i) hh)
  · intro i h h' hh
    exact Finset.image_subset_image ((C i).F_mono h h' (x i) hh)
  · exact hM
  · exact hA
  · exact hB
  · exact hbad
  · exact hbudget

end OpenAI086.ReferenceV61
#print axioms OpenAI086.ReferenceV61.primary_inclusion
#print axioms OpenAI086.ReferenceV61.floorlog_component_chain
#print axioms Auto.chain_side_bound
#print axioms Auto.ModeComponents.ofEdges
