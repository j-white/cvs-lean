import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosh moment of the recentred window sum, in closed form

Against a lattice frequency the hyperbolic cosine integrates over the centred window to a single
sine-hyperbolic times a rational factor, so the exponential moment of the recentred sum is a finite
algebraic expression in the coefficients, and the scalar bound it carries has no integral left in
it.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Set Polynomial

namespace Cvs.Finite.CoshMomentRecentred


/-- The antiderivative of `cosh (y u) cos (ω u)`. -/
def coshCosAntideriv (y ω : ℝ) : ℝ → ℝ := fun u =>
  (y * Real.sinh (y * u) * Real.cos (ω * u) + ω * Real.cosh (y * u) * Real.sin (ω * u))
    / (y ^ 2 + ω ^ 2)

/-- **It is one**, wherever the two frequencies are not both zero. -/
theorem hasDerivAt_coshCosAntideriv {y ω : ℝ} (h : y ^ 2 + ω ^ 2 ≠ 0) (u : ℝ) :
    HasDerivAt (coshCosAntideriv y ω) (Real.cosh (y * u) * Real.cos (ω * u)) u := by
  have hu : HasDerivAt (fun t : ℝ => y * t) y u := by
    simpa using (hasDerivAt_id u).const_mul y
  have hv : HasDerivAt (fun t : ℝ => ω * t) ω u := by
    simpa using (hasDerivAt_id u).const_mul ω
  have hnum : HasDerivAt
      (fun t : ℝ => y * Real.sinh (y * t) * Real.cos (ω * t)
        + ω * Real.cosh (y * t) * Real.sin (ω * t))
      (y * (Real.cosh (y * u) * y) * Real.cos (ω * u)
          + y * Real.sinh (y * u) * (-Real.sin (ω * u) * ω)
        + (ω * (Real.sinh (y * u) * y) * Real.sin (ω * u)
          + ω * Real.cosh (y * u) * (Real.cos (ω * u) * ω))) u :=
    ((hu.sinh.const_mul y).mul hv.cos).add ((hu.cosh.const_mul ω).mul hv.sin)
  have hd : (y * (Real.cosh (y * u) * y) * Real.cos (ω * u)
          + y * Real.sinh (y * u) * (-Real.sin (ω * u) * ω)
        + (ω * (Real.sinh (y * u) * y) * Real.sin (ω * u)
          + ω * Real.cosh (y * u) * (Real.cos (ω * u) * ω))) / (y ^ 2 + ω ^ 2)
      = Real.cosh (y * u) * Real.cos (ω * u) := by
    rw [div_eq_iff h]; ring
  rw [← hd]
  exact hnum.div_const _

/-- **The hyperbolic cosine against a cosine, over the centred window.** -/
theorem integral_cosh_mul_cos {y ω a : ℝ} (h : y ^ 2 + ω ^ 2 ≠ 0) :
    (∫ u in (-a)..a, Real.cosh (y * u) * Real.cos (ω * u))
      = 2 * (y * Real.sinh (y * a) * Real.cos (ω * a)
          + ω * Real.cosh (y * a) * Real.sin (ω * a)) / (y ^ 2 + ω ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_coshCosAntideriv h u)
    ((by fun_prop : Continuous fun u : ℝ =>
      Real.cosh (y * u) * Real.cos (ω * u)).intervalIntegrable _ _)]
  unfold coshCosAntideriv
  rw [mul_neg, mul_neg, Real.sinh_neg, Real.cosh_neg, Real.cos_neg, Real.sin_neg]
  field_simp
  ring

end Cvs.Finite.CoshMomentRecentred
