import Mathlib
import Cvs.Finite.SecularSumRealSquare

/-!
# Zero-freeness off the axes passes to the L² limit

    approximants nowhere zero off both axes, converging in `L²`  ⟹  the limit is too

the zero-free form of the Hurwitz step, which needs no sign condition on the approximants.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Complex

namespace Cvs.Limit.OffAxesLimit

/-- The plane off both coordinate axes. -/
def offAxes : Set ℂ := {z : ℂ | z.re ≠ 0 ∧ z.im ≠ 0}

theorem isOpen_offAxes : IsOpen offAxes := by
  have h1 : IsOpen {z : ℂ | z.re ≠ 0} :=
    isOpen_compl_singleton.preimage Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.im ≠ 0} :=
    isOpen_compl_singleton.preimage Complex.continuous_im
  exact h1.inter h2

/-- **A zero with `z²` real lies on an axis.** -/
theorem notMem_offAxes_of_sq_im {z : ℂ} (h : (z ^ 2).im = 0) : z ∉ offAxes := by
  intro hz
  have := Cvs.Finite.SecularSumRealSquare.re_eq_zero_of_sq_im z h hz.2
  exact hz.1 this

end Cvs.Limit.OffAxesLimit
