import Mathlib
import OpenAI086.FiniteRowCauchySchwarz
import OpenAI086.FiniteCommonNeighborEnergy

/-!
# Lemma 9.1: exact four-step walk counting and an energy lower bound

The paper's dense-graph subargument starts by manufacturing many
four-step alternating paths.  This module records the exact finite
weighted walk identity and a twofold Cauchy--Schwarz estimate.
For 0/1 adjacency these count walks including repeated vertices.

It does not yet establish the paper's *distinct ordered color tuples*
count, the removal of bad codegree pairs, or the sparse power saving.
-/

namespace OpenAI086

/-- Common-neighbor weight of an ordered pair of left vertices. -/
def finiteCodegree {U V : Type*} [Fintype V]
    (a : U → V → ℝ) (u w : U) : ℝ :=
  ∑ v : V, a u v * a w v

/-- Expanding a codegree square counts ordered four-edge walks, with
the two intermediate right vertices listed separately. -/
theorem finite_four_step_walk_identity
    {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) :
    (∑ u : U, ∑ w : U, (finiteCodegree a u w) ^ 2) =
      ∑ u : U, ∑ w : U, ∑ v : V, ∑ t : V,
        a u v * a w v * a u t * a w t := by
  classical
  have hpair (u w : U) :
      (finiteCodegree a u w) ^ 2 =
        ∑ v : V, ∑ t : V,
          a u v * a w v * a u t * a w t := by
    unfold finiteCodegree
    calc
      (∑ v : V, a u v * a w v) ^ 2 =
          (∑ v : V, a u v * a w v) *
            (∑ t : V, a u t * a w t) := by ring
      _ = ∑ v : V, ∑ t : V,
            (a u v * a w v) * (a u t * a w t) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro v _
              rw [Finset.mul_sum]
      _ = ∑ v : V, ∑ t : V,
            a u v * a w v * a u t * a w t := by
              apply Finset.sum_congr rfl
              intro v _
              apply Finset.sum_congr rfl
              intro t _
              ring
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro w _
  exact hpair u w

/-- Two Cauchy--Schwarz applications give a dimension-uniform
four-step walk-energy bound.  The constant `|U|²` is explicit. -/
theorem finite_four_step_walk_second_moment
    {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) :
    (∑ u : U, ∑ w : U, finiteCodegree a u w) ^ 2 ≤
      (Fintype.card U : ℝ) ^ 2 *
        (∑ u : U, ∑ w : U, (finiteCodegree a u w) ^ 2) := by
  classical
  have hcard : 0 ≤ (Fintype.card U : ℝ) := by positivity
  have hinner (u : U) :
      (∑ w : U, finiteCodegree a u w) ^ 2 ≤
        (Fintype.card U : ℝ) *
          (∑ w : U, (finiteCodegree a u w) ^ 2) := by
    have hcs := finite_row_cauchy_schwarz
      (fun w : U => finiteCodegree a u w) (fun _w : U => (1 : ℝ))
    simpa [mul_comm] using hcs
  have houter :
      (∑ u : U, ∑ w : U, finiteCodegree a u w) ^ 2 ≤
        (Fintype.card U : ℝ) *
          (∑ u : U, (∑ w : U, finiteCodegree a u w) ^ 2) := by
    have hcs := finite_row_cauchy_schwarz
      (fun u : U => ∑ w : U, finiteCodegree a u w)
      (fun _u : U => (1 : ℝ))
    simpa [mul_comm] using hcs
  calc
    (∑ u : U, ∑ w : U, finiteCodegree a u w) ^ 2 ≤
        (Fintype.card U : ℝ) *
          (∑ u : U, (∑ w : U, finiteCodegree a u w) ^ 2) := houter
    _ ≤ (Fintype.card U : ℝ) *
        (∑ u : U, (Fintype.card U : ℝ) *
          (∑ w : U, (finiteCodegree a u w) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hcard
            apply Finset.sum_le_sum
            intro u _
            exact hinner u
    _ = (Fintype.card U : ℝ) ^ 2 *
        (∑ u : U, ∑ w : U, (finiteCodegree a u w) ^ 2) := by
          rw [← Finset.mul_sum]
          ring


/-- A finite weighted `C₄` (four-edge walk) lower bound, without any
regularity, density, or distinctness assumptions.  For 0/1 adjacency,
this is the elementary fourth-moment lower bound behind the dense-graph
part of Lemma 9.1. The much stronger *separated* sparse-counting claim
of Lemma 9.1 is still open. -/
theorem finite_four_step_walk_density_lower_bound
    {U V : Type*} [Fintype U] [Fintype V]
    (a : U → V → ℝ) :
    (∑ v : V, ∑ u : U, a u v) ^ 4 ≤
      (Fintype.card U : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 2 *
        (∑ u : U, ∑ w : U, (finiteCodegree a u w) ^ 2) := by
  let edgeMass : ℝ := ∑ v : V, ∑ u : U, a u v
  let pairMass : ℝ := ∑ u : U, ∑ w : U,
    ∑ v : V, a u v * a w v
  let walkMass : ℝ := ∑ u : U, ∑ w : U, (finiteCodegree a u w) ^ 2
  have hv : 0 ≤ (Fintype.card V : ℝ) := by positivity
  have hpair : 0 ≤ pairMass := by
    dsimp [pairMass]
    rw [finite_common_neighbor_identity a]
    apply Finset.sum_nonneg
    intro v _
    exact sq_nonneg _
  have h2 : edgeMass ^ 2 ≤ (Fintype.card V : ℝ) * pairMass := by
    simpa only [edgeMass, pairMass] using finite_common_neighbor_second_moment a
  have h4 : pairMass ^ 2 ≤
      (Fintype.card U : ℝ) ^ 2 * walkMass := by
    simpa only [pairMass, walkMass, finiteCodegree] using
      finite_four_step_walk_second_moment a
  have hsquare : edgeMass ^ 4 ≤
      (Fintype.card V : ℝ) ^ 2 * pairMass ^ 2 := by
    have hdiff : 0 ≤ (Fintype.card V : ℝ) * pairMass - edgeMass ^ 2 :=
      sub_nonneg.mpr h2
    have hplus : 0 ≤ (Fintype.card V : ℝ) * pairMass + edgeMass ^ 2 :=
      add_nonneg (mul_nonneg hv hpair) (sq_nonneg edgeMass)
    nlinarith [mul_nonneg hdiff hplus]
  calc
    (∑ v : V, ∑ u : U, a u v) ^ 4 = edgeMass ^ 4 := rfl
    _ ≤ (Fintype.card V : ℝ) ^ 2 * pairMass ^ 2 := hsquare
    _ ≤ (Fintype.card V : ℝ) ^ 2 *
          ((Fintype.card U : ℝ) ^ 2 * walkMass) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
    _ = (Fintype.card U : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 2 *
          (∑ u : U, ∑ w : U, (finiteCodegree a u w) ^ 2) := by
            dsimp [walkMass]
            ring

end OpenAI086
