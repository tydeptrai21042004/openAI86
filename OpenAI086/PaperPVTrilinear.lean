import OpenAI086.PaperSchwartzPV
import OpenAI086.PaperMainExtensionBridge

/-! Concrete pointwise trilinearity and the L¹ realization bridge.
The remaining spatial integrability is an explicit hypothesis of the L¹
construction; the pointwise integral is not defined by choosing a limit.
Source candidates, pending pinned kernel verification. -/
noncomputable section
namespace OpenAI086
open MeasureTheory Filter Topology

def v25Pair (a b c : V25S) (x t : ℝ) : ℂ :=
  pairedHilbertKernel (fun i => (![a,b,c] : Fin 3 → V25S) i) x t

def v25T (a b c : V25S) (x : ℝ) : ℂ :=
  (2 : ℂ)⁻¹ * ∫ t : ℝ, v25Pair a b c x t

theorem v25_pair_integrable (a b c : V25S) (x : ℝ) :
    Integrable (v25Pair a b c x) := by
  exact v25_paired_integrable (![a,b,c]) x

theorem v25_T_pv (f : Fin 3 → V25S) (x : ℝ) :
    Tendsto (fun ε : ℝ => truncHilbert (fun i => f i) x ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (v25T (f 0) (f 1) (f 2) x)) := by
  have heq : (![f 0, f 1, f 2] : Fin 3 → V25S) = f := by
    funext i
    fin_cases i <;> simp
  simpa [v25T, v25Pair, v25PV, heq] using v25_pv_tendsto f x

theorem v25_pair_add_1 (a b c d : V25S) (x t : ℝ) :
    v25Pair (a+d) b c x t = v25Pair a b c x t + v25Pair d b c x t := by
  simp [v25Pair, pairedHilbertKernel, symmetricTripleNumerator, smul_eq_mul] <;> ring

theorem v25_T_add_1 (a b c d : V25S) (x : ℝ) :
    v25T (a+d) b c x = v25T a b c x + v25T d b c x := by
  unfold v25T
  simp_rw [v25_pair_add_1]
  rw [integral_add (v25_pair_integrable a b c x) (v25_pair_integrable d b c x)]
  ring

theorem v25_pair_smul_1 (a b c : V25S) (r : ℂ) (x t : ℝ) :
    v25Pair (r • a) b c x t = r • v25Pair a b c x t := by
  simp [v25Pair, pairedHilbertKernel, symmetricTripleNumerator, smul_eq_mul] <;> ring

theorem v25_T_smul_1 (a b c : V25S) (r : ℂ) (x : ℝ) :
    v25T (r • a) b c x = r • v25T a b c x := by
  unfold v25T
  simp_rw [v25_pair_smul_1]
  rw [integral_smul]
  simp [smul_eq_mul] <;> ring

theorem v25_pair_add_2 (a b c d : V25S) (x t : ℝ) :
    v25Pair a (b+d) c x t = v25Pair a b c x t + v25Pair a d c x t := by
  simp [v25Pair, pairedHilbertKernel, symmetricTripleNumerator, smul_eq_mul] <;> ring

theorem v25_T_add_2 (a b c d : V25S) (x : ℝ) :
    v25T a (b+d) c x = v25T a b c x + v25T a d c x := by
  unfold v25T
  simp_rw [v25_pair_add_2]
  rw [integral_add (v25_pair_integrable a b c x) (v25_pair_integrable a d c x)]
  ring

theorem v25_pair_smul_2 (a b c : V25S) (r : ℂ) (x t : ℝ) :
    v25Pair a (r • b) c x t = r • v25Pair a b c x t := by
  simp [v25Pair, pairedHilbertKernel, symmetricTripleNumerator, smul_eq_mul] <;> ring

theorem v25_T_smul_2 (a b c : V25S) (r : ℂ) (x : ℝ) :
    v25T a (r • b) c x = r • v25T a b c x := by
  unfold v25T
  simp_rw [v25_pair_smul_2]
  rw [integral_smul]
  simp [smul_eq_mul] <;> ring

theorem v25_pair_add_3 (a b c d : V25S) (x t : ℝ) :
    v25Pair a b (c+d) x t = v25Pair a b c x t + v25Pair a b d x t := by
  simp [v25Pair, pairedHilbertKernel, symmetricTripleNumerator, smul_eq_mul] <;> ring

theorem v25_T_add_3 (a b c d : V25S) (x : ℝ) :
    v25T a b (c+d) x = v25T a b c x + v25T a b d x := by
  unfold v25T
  simp_rw [v25_pair_add_3]
  rw [integral_add (v25_pair_integrable a b c x) (v25_pair_integrable a b d x)]
  ring

theorem v25_pair_smul_3 (a b c : V25S) (r : ℂ) (x t : ℝ) :
    v25Pair a b (r • c) x t = r • v25Pair a b c x t := by
  simp [v25Pair, pairedHilbertKernel, symmetricTripleNumerator, smul_eq_mul] <;> ring

theorem v25_T_smul_3 (a b c : V25S) (r : ℂ) (x : ℝ) :
    v25T a b (r • c) x = r • v25T a b c x := by
  unfold v25T
  simp_rw [v25_pair_smul_3]
  rw [integral_smul]
  simp [smul_eq_mul] <;> ring

/-- Actual pointwise function-valued curried trilinear map. -/
def v25PointwiseOperator : V25S →ₗ[ℂ] V25S →ₗ[ℂ] V25S →ₗ[ℂ] (ℝ → ℂ) where
  toFun a := {
    toFun b := {
      toFun c := v25T a b c
      map_add' c d := by funext x; exact v25_T_add_3 a b c d x
      map_smul' r c := by funext x; exact v25_T_smul_3 a b c r x }
    map_add' b d := by ext c x; exact v25_T_add_2 a b c d x
    map_smul' r b := by ext c x; exact v25_T_smul_2 a b c r x }
  map_add' a d := by ext b c x; exact v25_T_add_1 a b c d x
  map_smul' r a := by ext b c x; exact v25_T_smul_1 a b c r x

/-- A concrete L¹ element, once spatial integrability of the actual PV is known. -/
def v25ToL1 (a b c : V25S) (h : MemLp (v25T a b c) 1 volume) : V24L1 :=
  h.toLp (v25T a b c)

theorem v25_L1_ae (a b c : V25S) (h : MemLp (v25T a b c) 1 volume) :
    (fun x => v25ToL1 a b c h x) =ᵐ[volume] v25T a b c := by
  exact MemLp.coeFn_toLp _

/-- The uniform analytic bound now only needs to be proved for the concrete
paired integral. Its proof is not supplied by pointwise cancellation. -/
theorem v25_main_from_concrete_bound (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f : Fin 3 → V25S,
      eLpNorm (v25PV f) 1 ≤ ENNReal.ofReal C * ∏ i : Fin 3, eLpNorm (f i) 3) :
    Theorem1_1_Goal := by
  exact ⟨C, hC, fun f => ⟨v25PV f, v25_pv_tendsto f, h f⟩⟩

end OpenAI086
