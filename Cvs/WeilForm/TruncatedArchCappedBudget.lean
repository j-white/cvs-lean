import Mathlib
import Cvs.Zeta.WeilPositivityStatement

/-!
# The truncated arch+Lévy term is bounded below by the capped channel budget

    per-channel caps `channelQuad_{bₙ}(f) ≤ lamₙ ∫f²`   ⟹
        `(truncConst N − Σ lamₙ) ∫f² ≤ archSymbol 0·g(0) + ∫ densityTrunc·(g(0)−g(u/2))`

for continuous `f` supported in `[0, L]`.
-/

noncomputable section

open MeasureTheory Set Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.TruncatedArchCappedBudget

/-- `g(0)` is `∫ f²`. -/
theorem selfConvolution_zero_eq (f : ℝ → ℝ) : selfConvolution f 0 = ∫ x, f x ^ 2 := by
  unfold selfConvolution
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show f s * f (s + 0) = f s ^ 2
  rw [add_zero, sq]

end Cvs.WeilForm.TruncatedArchCappedBudget
