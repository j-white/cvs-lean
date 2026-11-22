import Mathlib
import Cvs.Finite.RecentredTransform

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The moving-window comparison for the recentred family

`Cvs.Finite.RecentredTransform.cgtransform` is the placed-window transform times `Cvs.Finite.RecentredTransform.phase`, and that factor has
modulus `exp(z.im · L / 2)`: one on the real axis, and growing off it, which is where
`Cvs.Limit.OffAxesLimit.offAxes` lives. So comparing two recentred families costs that factor on top of the strip
constant of `an earlier result`, and the `L²` distance has to beat the product.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Complex

namespace Cvs.Limit.MovingWindowComparison
open Cvs.ZeroCounting

/-- **The recentring factor has modulus `exp(z.im · L / 2)`**, which is one exactly on the
real axis. -/
theorem norm_phase (L : ℝ) (z : ℂ) :
    ‖Cvs.Finite.RecentredTransform.phase L z‖ = Real.exp (z.im * L / 2) := by
  unfold Cvs.Finite.RecentredTransform.phase
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

end Cvs.Limit.MovingWindowComparison
