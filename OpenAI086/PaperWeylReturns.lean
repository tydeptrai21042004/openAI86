import Mathlib

/-! Lemma 4.3, p.17: exact antisymmetrization and the integer obstruction.
The bounds on actual Fourier returns and geometry of numbers remain inputs. -/
namespace OpenAI086

theorem v27_return_antisymmetry {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (m m' d d' : E) (q : ℝ) :
    let A := fun u v => C u v - C v u
    (q + C (m'+d') (m+d) - A (m'+d') m) -
      (q + C (m+d) (m'+d') - A (m+d) m') = A d' d - A m' m := by
  dsimp
  simp only [map_add, LinearMap.add_apply]
  ring

/-- Once the two return pairings and the small-return skew pairing are
small enough, the integral lattice skew pairing vanishes exactly. -/
theorem v27_integral_skew_zero (p q e : ℝ) (z : ℤ)
    (hid : p-q = e-(z : ℝ))
    (hp : |p| ≤ 1/4) (hq : |q| ≤ 1/4) (he : |e| ≤ 1/4) : z = 0 := by
  have hz : |(z : ℝ)| ≤ 3/4 := by
    rw [abs_le] at hp hq he ⊢
    constructor <;> linarith
  by_contra hn
  have h1 : (1 : ℤ) ≤ |z| := by
    have hpos : 0 < |z| := abs_pos.mpr hn
    omega
  have h2 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast h1
  linarith

/-- Finite Plancherel packing obstruction. The analytic construction of
actual disjoint Fourier balls is separate from this summation step. -/
theorem v27_return_energy_obstruction (n : ℕ) (E c : ℝ)
    (energy : ℕ → ℝ) (hlower : ∀ j < n, c ≤ energy j)
    (hupper : (∑ j ∈ Finset.range n, energy j) ≤ E) : (n : ℝ)*c ≤ E := by
  calc
    (n : ℝ)*c = ∑ j ∈ Finset.range n, c := by simp [mul_comm]
    _ ≤ ∑ j ∈ Finset.range n, energy j := Finset.sum_le_sum
      (fun j hj => hlower j (Finset.mem_range.mp hj))
    _ ≤ E := hupper

end OpenAI086
