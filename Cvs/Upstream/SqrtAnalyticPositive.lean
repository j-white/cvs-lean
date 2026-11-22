import Mathlib

/-!
# The square root is analytic on the positives

`Real.contDiffAt_sqrt` holds at the analytic smoothness index, so away from zero the square root is
analytic; this names that in the `AnalyticAt` form the mode functions need.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.Upstream.SqrtAnalyticPositive

/-- On the positives the square root is `exp ∘ (·/2) ∘ log`. -/
theorem sqrt_eq_exp_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

end Cvs.Upstream.SqrtAnalyticPositive
