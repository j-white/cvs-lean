import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.PhiThetaDifferentialOperator
import Cvs.Xi.ThetaSumsTwiceDifferentiable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The second derivative sum is continuous

Continuity is local, and on a bounded interval the second derivative terms are dominated uniformly
by a summable sequence, so the sum is continuous there and hence at the interval's every interior
point. The other two sums are continuous because they are differentiable.
-/

noncomputable section

open Real Set Filter Topology

namespace Cvs.Xi.ThetaSecondDerivContinuous

open Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable

theorem continuous_thetaTerm2 (n : ℕ) : Continuous (thetaTerm2 n) := by
  unfold thetaTerm2 thetaTerm; fun_prop

/-- **The second derivative sum is continuous on any bounded interval.** -/
theorem continuousOn_thetaSum2 (y : ℝ) : ContinuousOn thetaSum2 (Ioo (y - 1) (y + 1)) := by
  unfold thetaSum2
  refine continuousOn_tsum (fun n => (continuous_thetaTerm2 (n + 1)).continuousOn)
    ((summable_nat_add_iff 1).mpr (summable_bnd2 (y - 1) (y + 1))) (fun n x hx => ?_)
  rw [Real.norm_eq_abs]
  exact abs_thetaTerm2_le_bnd hx.1.le hx.2.le (n + 1)

/-- **The second derivative sum is continuous.** -/
theorem continuous_thetaSum2 : Continuous thetaSum2 := by
  rw [continuous_iff_continuousAt]
  intro y
  exact (continuousOn_thetaSum2 y).continuousAt
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)

theorem continuous_thetaSum : Continuous thetaSum :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_thetaSum y).continuousAt

theorem continuous_thetaSum1 : Continuous thetaSum1 :=
  continuous_iff_continuousAt.mpr fun y => (hasDerivAt_thetaSum1 y).continuousAt

end Cvs.Xi.ThetaSecondDerivContinuous
