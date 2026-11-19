import Mathlib

/-!
# OpenAI #086, §2 — definition of the four-linear local form

This is the ACTUAL analytic integral appearing in the paper on p. 4,
not a replacement by finite sums or a scalar placeholder.

The radius `r` is the interval length and is required to be positive in
applications. The kernel's full support and Gevrey derivative conditions
are not yet formalized. For admissible kernels, each progression marginal
must be integrable and vanish; the latter is recorded as a separate Prop.
-/

noncomputable section
namespace OpenAI086
open MeasureTheory

/-- Four equally spaced progression coordinates, indexed 0,1,2,3. -/
def progressionCoordinate (x t : ℝ) (j : Fin 4) : ℝ :=
  x + (j.val : ℝ) * t

/-- The unnormalized 4-linear local form `H_I(z_0,z_1,z_2,z_3)`,
with `r=|I|` and kernel `w_I` as on page 4 of the paper. The integral
is defined in Mathlib even when an integrability hypothesis is not yet
proved, so applications MUST establish its integrability separately. -/
def fourLinearLocalForm
    (r : ℝ) (w : ℝ → ℝ → ℂ) (z : Fin 4 → ℝ → ℂ) : ℂ :=
  (r : ℂ)⁻¹ ^ 2 *
    ∫ x : ℝ, ∫ t : ℝ,
      w x t * ∏ j : Fin 4, z j (progressionCoordinate x t j)

/-- Paper §2 admissibility condition (2): every one-point marginal
vanishes. This explicitly includes integrability to avoid vacuous use
of a totalized integral on nonintegrable functions. -/
def HasZeroProgressionMarginals (w : ℝ → ℝ → ℂ) : Prop :=
  ∀ (u : ℝ) (j : Fin 4),
    Integrable (fun t : ℝ => w (u - (j.val : ℝ) * t) t) ∧
      (∫ t : ℝ, w (u - (j.val : ℝ) * t) t) = 0

/-- Positive scale and cancellation; this is a STRICTLY WEAKER predicate
than complete kernel admissibility in the manuscript (support, derivative
and Gevrey constants remain to be supplied). -/
def HasBasicLocalKernelConditions (r : ℝ) (w : ℝ → ℝ → ℂ) : Prop :=
  0 < r ∧ HasZeroProgressionMarginals w

end OpenAI086
