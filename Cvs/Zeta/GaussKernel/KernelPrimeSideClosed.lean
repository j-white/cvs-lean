import Mathlib

/-!
# The prime side, in closed form

`B110C.re_gaussAmp_sq` puts the *zero* side of the explicit formula in closed form: three
terms, one per bump of `gaussAmp²`.
-/

namespace Cvs.GaussKernel

open Complex MeasureTheory
open scoped Real

/-- The general Gaussian integral, in the shape this block uses. -/
theorem integral_quad {lam : ℝ} (hlam : 0 < lam) (c d : ℂ) :
    (∫ r : ℝ, Complex.exp (-(lam : ℂ) * (r : ℂ) ^ 2 + c * (r : ℂ) + d))
      = ((π : ℂ) / (lam : ℂ)) ^ (1 / 2 : ℂ)
        * Complex.exp (d - c ^ 2 / (4 * (-(lam : ℂ)))) := by
  have hb : ((-(lam : ℂ))).re < 0 := by simpa using hlam
  rw [integral_cexp_quadratic hb, neg_neg]

theorem integrable_quad {lam : ℝ} (hlam : 0 < lam) (c d : ℂ) :
    Integrable (fun r : ℝ =>
      Complex.exp (-(lam : ℂ) * (r : ℂ) ^ 2 + c * (r : ℂ) + d)) :=
  integrable_cexp_quadratic (by simpa using hlam) c d

end Cvs.GaussKernel
