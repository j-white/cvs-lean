import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The Hann window is three shifts

Measurement (`tools/aligned_test_admissibility.py`) shows the aligned test fails
`Cvs.Zeta.guinand_weil_classical`'s decay hypothesis: that theorem asks for `‖ofCritical h z‖ ≤
A/(1+|Im z|)³` on `-1 ≤ Re z ≤ 2`, and the aligned test's transform decays only quadratically,
because `g` has jumps at both endpoints of `[0, L]`.
-/

namespace Cvs.Detection

open Complex intervalIntegral MeasureTheory
open scoped Real

/-- The transform of `f` over `[0, L]`, with `fourierReal`'s character convention. -/
noncomputable def windowTransform (L : ℝ) (f : ℝ → ℂ) (ξ : ℂ) : ℂ :=
  ∫ s in (0 : ℝ)..L, Complex.exp (-((s : ℂ) * ξ) * I) * f s

end Cvs.Detection
