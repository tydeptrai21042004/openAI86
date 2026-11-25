import Mathlib

/-! The coefficient-motion stopping rule of Lemma 3.4, p.11.
Construct anchors on each spatial path using the last selected coefficient
vector. Unlike size stops, this rule uses a norm difference, not doubling.
The path count is reset only by starting a new attempt. The spatial
partition and L² variation connection remain separate proof obligations. -/
noncomputable section
namespace OpenAI086

variable {X : Type*} [NormedAddCommGroup X]

def v47AnchorDepth (c : ℕ → X) (b : ℝ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if b < ‖c (n+1)-c (v47AnchorDepth c b n)‖ then n+1 else v47AnchorDepth c b n

def v47AnchorList (c : ℕ → X) (b : ℝ) : ℕ → List ℕ
  | 0 => [0]
  | n+1 => if b < ‖c (n+1)-c (v47AnchorDepth c b n)‖ then
      (n+1)::v47AnchorList c b n else v47AnchorList c b n

/-- Every pair of successive anchors is separated by the required
coefficient-motion threshold. Read the list newest to oldest. -/
inductive V47AnchorChain (c : ℕ → X) (b : ℝ) : List ℕ → Prop
  | single (n : ℕ) : V47AnchorChain c b [n]
  | cons (n m : ℕ) (l : List ℕ) : m < n → b < ‖c n-c m‖ →
      V47AnchorChain c b (m::l) → V47AnchorChain c b (n::m::l)

theorem v47_anchor_depth_le (c : ℕ → X) (b : ℝ) (n : ℕ) : v47AnchorDepth c b n ≤ n := by
  induction n with
  | zero => simp [v47AnchorDepth]
  | succ n ih => rw [v47AnchorDepth]; split_ifs <;> omega

theorem v47_anchor_nonempty (c : ℕ → X) (b : ℝ) (n : ℕ) : v47AnchorList c b n ≠ [] := by
  induction n with
  | zero => simp [v47AnchorList]
  | succ n ih => rw [v47AnchorList]; split_ifs <;> simp_all

theorem v47_anchor_head (c : ℕ → X) (b : ℝ) (n : ℕ) :
    (v47AnchorList c b n).headD 0 = v47AnchorDepth c b n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [v47AnchorList,v47AnchorDepth]; split_ifs <;> simp_all

theorem v47_anchor_chain (c : ℕ → X) (b : ℝ) (n : ℕ) : V47AnchorChain c b (v47AnchorList c b n) := by
  induction n with
  | zero => exact .single 0
  | succ n ih =>
    rw [v47AnchorList]
    split_ifs with h
    · have hn := v47_anchor_nonempty c b n
      have hh := v47_anchor_head c b n
      have hd := v47_anchor_depth_le c b n
      cases he : v47AnchorList c b n with
      | nil => exact (hn he).elim
      | cons k l =>
        simp only [he,List.headD_cons] at hh
        rw [← hh] at h hd
        exact .cons _ _ _ (by omega) h (by simpa only [he] using ih)
    · exact ih

/-- The coefficient error at every retained depth is at most b. At an
anchor the error vanishes. This is the error bound used on p.12. -/
theorem v47_retained_coefficient_error (c : ℕ → X) (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    ‖c n-c (v47AnchorDepth c b n)‖ ≤ b := by
  cases n with
  | zero => simpa [v47AnchorDepth] using hb
  | succ n =>
    rw [v47AnchorDepth]
    split_ifs with h
    · simpa using hb
    · exact le_of_not_gt h

/-- The first-match construction depends only on the coefficients through
that depth. In particular it agrees across a refining cell. -/
theorem v47_anchor_prefix_congr (c d : ℕ → X) (b : ℝ) (n : ℕ)
    (h : ∀ j ≤ n, c j = d j) :
    v47AnchorDepth c b n = v47AnchorDepth d b n ∧ v47AnchorList c b n = v47AnchorList d b n := by
  induction n with
  | zero => simp [v47AnchorDepth,v47AnchorList]
  | succ n ih =>
    obtain ⟨hd,hl⟩ := ih (fun j hj => h j (by omega))
    have hk := h (v47AnchorDepth c b n) (by have := v47_anchor_depth_le c b n; omega)
    have hs := h (n+1) (by omega)
    constructor
    · simp only [v47AnchorDepth, ← hd,hk,hs]
    · simp only [v47AnchorList, ← hd,hk,hs,hl]

end OpenAI086
