import Mathlib

/-!
# The pole term as an operator

The rank-two pole `f ↦ A·e^{−s/2} + B·e^{s/2}` has quadratic form `2AB`, the first term of
`Cvs.WeilForm.SelfConvolutionFunctional`'s window form, and its moments are the `n = 0` channel's.
-/

set_option maxHeartbeats 1600000

noncomputable section

namespace Cvs.WeilForm.PoleTermOperator

variable {L : ℝ} {f : ℝ → ℝ}

/-- The forward pole moment. -/
def poleA (L : ℝ) (f : ℝ → ℝ) : ℝ := ∫ s in (0:ℝ)..L, Real.exp (s / 2) * f s

/-- The backward pole moment. -/
def poleB (L : ℝ) (f : ℝ → ℝ) : ℝ := ∫ s in (0:ℝ)..L, Real.exp (-(s / 2)) * f s

/-- The pole acting as an operator. -/
def poleOp (L : ℝ) (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  poleA L f * Real.exp (-(s / 2)) + poleB L f * Real.exp (s / 2)

end Cvs.WeilForm.PoleTermOperator
