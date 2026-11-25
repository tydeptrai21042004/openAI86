import OpenAI086.LocalForms

/-! V41: analytic statement candidates for Section 2. The local integral
uses actual Lebesgue measure. These Prop definitions are not theorems.
The definitions of the lattice, rooted subtree, and optimal local constant
must be reviewed against the manuscript before certification. -/
noncomputable section
namespace OpenAI086
open MeasureTheory
open scoped ENNReal BigOperators

/-- A dyadic lattice at every integral depth, with nested grid boundaries. -/
structure V41Lattice where
  scale : ℤ → ℝ
  offset : ℤ → ℝ
  scale_pos : ∀ n, 0 < scale n
  half_scale : ∀ n, scale (n+1) = scale n / 2
  nested_boundary : ∀ n, ∃ k : ℤ, offset n = offset (n+1) + (k : ℝ) * scale (n+1)

abbrev V41Cell := ℤ × ℤ

def v41Left (L : V41Lattice) (I : V41Cell) : ℝ :=
  L.offset I.1 + (I.2 : ℝ) * L.scale I.1

def v41Interval (L : V41Lattice) (I : V41Cell) : Set ℝ :=
  Set.Ico (v41Left L I) (v41Left L I + L.scale I.1)

def v41LocalNorm (L : V41Lattice) (I : V41Cell) (p : ℝ≥0∞) (f : ℝ → ℂ) : ℝ≥0∞ :=
  eLpNorm f p ((ENNReal.ofReal (L.scale I.1))⁻¹ • volume.restrict (v41Interval L I))

/-- Mixed partial derivative: x differentiated a times, then t b times. -/
def v41Partial (a b : ℕ) (w : ℝ → ℝ → ℂ) (x t : ℝ) : ℂ :=
  iteratedDeriv b (fun s => iteratedDeriv a (fun u => w u s) x) t

/-- All three admissibility conditions; smoothness is explicitly retained. -/
def V41Admissible (L : V41Lattice) (I : V41Cell) (c0 C0 : ℝ)
    (w : ℝ → ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ (fun z : ℝ × ℝ => w z.1 z.2) ∧
  (∀ x t, w x t ≠ 0 → ∀ j : Fin 4,
    v41Left L I + c0 * L.scale I.1 ≤ progressionCoordinate x t j ∧
    progressionCoordinate x t j ≤ v41Left L I + L.scale I.1 - c0 * L.scale I.1) ∧
  HasZeroProgressionMarginals w ∧
  (∀ (a b : ℕ) (x t : ℝ), ‖v41Partial a b w x t‖ ≤
    (L.scale I.1)⁻¹ ^ (a+b) * Real.rpow (C0 * ((a : ℝ) + (b : ℝ) + 2))
      (C0 * ((a : ℝ) + (b : ℝ) + 2)))

/-- Local absolute integral (using a nonnegative integral avoids totalized
Bochner integrals for inputs not yet known to be integrable). -/
def v41AbsoluteLocalForm (r : ℝ) (w : ℝ → ℝ → ℂ)
    (f : Fin 4 → ℝ → ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal r)⁻¹ ^ 2 * ∫⁻ z : ℝ × ℝ,
    ENNReal.ofReal (‖w z.1 z.2‖ * ∏ j : Fin 4, ‖f j (progressionCoordinate z.1 z.2 j)‖)

/-- Lemma 2.1, scalar-valued analytic target. The vector-valued version
requires a separate generalization of this statement. -/
def V41Lemma21Scalar (c0 C0 : ℝ) : Prop :=
  ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (L : V41Lattice) (I : V41Cell) (w : ℝ → ℝ → ℂ)
    (f : Fin 4 → ℝ → ℂ) (p : Fin 4 → ℝ≥0∞),
    V41Admissible L I c0 C0 w → (∀ j, 1 ≤ p j) → (∑ j, (p j)⁻¹) ≤ 2 →
    (∀ j, AEStronglyMeasurable (f j) volume) →
    v41AbsoluteLocalForm (L.scale I.1) w f ≤ C * ∏ j, v41LocalNorm L I (p j) (f j)

/-- Uncentered maximal operator of the absolute q-power, followed by
its q-th root. The supremum ranges over every bounded interval of
positive length containing x, not only a finite dyadic grid. -/
def v41Mq (q : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  sSup {v : ℝ≥0∞ | ∃ a b : ℝ, a < b ∧ a ≤ x ∧ x ≤ b ∧
    v = ENNReal.rpow ((ENNReal.ofReal (b-a))⁻¹ *
      ∫⁻ y in Set.Icc a b, ENNReal.ofReal (Real.rpow ‖f y‖ q)) (q⁻¹)}

def V41DepthRange (S : Finset V41Cell) (N : ℕ) : Prop :=
  ∃ n : ℤ, ∀ I ∈ S, n ≤ I.1 ∧ I.1 < n + (N : ℤ)

def V41CompactInputs (q : ℝ) (f : Fin 4 → ℝ → ℂ) : Prop :=
  ∀ j, HasCompactSupport (f j) ∧ MemLp (f j) (ENNReal.ofReal q) volume

def v41LocalSum (L : V41Lattice) (S : Finset V41Cell)
    (w : V41Cell → ℝ → ℝ → ℂ) (f : Fin 4 → ℝ → ℂ) : ℝ≥0∞ :=
  ∑ I ∈ S, ENNReal.ofReal (L.scale I.1) *
    ENNReal.ofReal ‖fourLinearLocalForm (L.scale I.1) (w I) f‖

def v41MaximalIntegral (q : ℝ) (f : Fin 4 → ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ∏ j : Fin 4, v41Mq q (f j) x

/-- Candidate definition of C_N as the infimum of the admissible constants.
The required nonempty finite bound and least-bound property are still to
be established (as are measurability and Fubini for the local forms). -/
def v41CN (c0 C0 q : ℝ) (N : ℕ) : ℝ≥0∞ :=
  sInf {C : ℝ≥0∞ | ∀ (L : V41Lattice) (S : Finset V41Cell)
    (w : V41Cell → ℝ → ℝ → ℂ) (f : Fin 4 → ℝ → ℂ),
    V41DepthRange S N → (∀ I ∈ S, V41Admissible L I c0 C0 (w I)) →
    V41CompactInputs q f → v41LocalSum L S w f ≤ C * v41MaximalIntegral q f}

/-- Theorem 2.2 target: no bound may depend on N. -/
def V41UniformLocalGoal (c0 C0 : ℝ) : Prop :=
  ∃ q : ℝ, 2 < q ∧ q < 3 ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ N : ℕ, v41CN c0 C0 q N ≤ C

/-- Root and ancestor closure on a finite dyadic subtree. -/
def V41RootedTree (L : V41Lattice) (T : Finset V41Cell) (R : V41Cell) : Prop :=
  R ∈ T ∧ (∀ I ∈ T, v41Interval L I ⊆ v41Interval L R) ∧
  (∀ I ∈ T, ∀ J : V41Cell, v41Interval L I ⊆ v41Interval L J →
    v41Interval L J ⊆ v41Interval L R → J ∈ T)

/-- Proposition 2.3 target. This is an obligation, not an assumed estimate.
The input class uses local measurable representatives; its relationship to
compact truncations and the original normalized Lq inputs needs review. -/
def V41NormalizedAbsorptionGoal (c0 C0 : ℝ) : Prop :=
  ∃ q : ℝ, 2 < q ∧ q < 3 ∧ ∃ cmax : ℝ, 0 < cmax ∧
    ∀ c : ℝ, 0 < c → c < cmax → ∃ A : ℝ≥0∞, A < ⊤ ∧
    ∀ (N : ℕ) (L : V41Lattice) (T S : Finset V41Cell) (R : V41Cell)
      (w : V41Cell → ℝ → ℝ → ℂ) (f : Fin 4 → ℝ → ℂ),
      V41RootedTree L T R → S ⊆ T → V41DepthRange S N →
      (∀ I ∈ S, V41Admissible L I c0 C0 (w I)) →
      (∀ j, AEStronglyMeasurable (f j) volume) →
      (∀ I ∈ T, ∀ j, v41LocalNorm L I (ENNReal.ofReal q) (f j) ≤ 1) →
      v41LocalSum L S w f ≤ (A + ENNReal.ofReal c * v41CN c0 C0 q N) *
        ENNReal.ofReal (L.scale R.1)

end OpenAI086
