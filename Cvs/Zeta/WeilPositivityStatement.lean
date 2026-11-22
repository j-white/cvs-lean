import Mathlib

open scoped ContDiff

/-!
# Weil positivity as a formal statement — and the honesty line

`RH` below is Mathlib's formal Riemann hypothesis.
-/

namespace Cvs.Zeta.Explicit.Weil

/-- The self-convolution `(h⋆ ∗ h)(t) = ∫ h(x) h(x+t) dx` of a real test
function on log-scale — the positive-type test shape of Weil's criterion. -/
noncomputable def selfConvolution (h : ℝ → ℝ) : ℝ → ℝ :=
  fun t => ∫ x : ℝ, h x * h (x + t)

end Cvs.Zeta.Explicit.Weil
