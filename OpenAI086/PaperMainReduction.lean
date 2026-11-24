import OpenAI086.ConditionalMainTransfer
import OpenAI086.PaperTruncationSign

/-! Main theorem transfer: sign and norm invariance are no longer assumed
as separate inputs. The actual plus-shift bound is still open. -/
namespace OpenAI086
open MeasureTheory

theorem v24_main_from_plus_bound (hplus : PlusShiftPointwiseBound) : Theorem1_1_Goal := by
  apply Theorem1_1_from_plus_shift hplus
  · intro f x ε
    exact truncationSignBridge (fun i => f i) x ε
  · intro g
    change eLpNorm (-g) 1 = eLpNorm g 1
    exact eLpNorm_neg g 1

end OpenAI086
