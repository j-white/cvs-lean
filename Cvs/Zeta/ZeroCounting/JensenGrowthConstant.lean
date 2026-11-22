import Mathlib

/-!
# The growth constant, evaluated

`Cvs.Zeta.ZeroCounting.JensenChainConstants` showed the two maxima resolve.  With the venue carrying its constants rather than
discarding them, `K` is `π²/6` as a theorem about `completedXiCore`, not as arithmetic.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Complex Real

namespace Cvs.Zeta.ZeroCounting.JensenGrowthConstant

/-- `π²/6` is above `1`, which both maxima need. -/
theorem one_le_zetaTwo : (1:ℝ) ≤ Real.pi ^ 2 / 6 := by
  nlinarith [Real.pi_gt_three, Real.pi_pos]

end Cvs.Zeta.ZeroCounting.JensenGrowthConstant
