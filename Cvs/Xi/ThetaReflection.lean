import Mathlib
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.ThetaSumEvenKernel

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Reflecting the variable

Inverting the kernel's argument multiplies it by a square root, and in the logarithmic variable that
inversion is a reflection. The theta sum therefore differs from its reflection by a hyperbolic sine,
which is the transformation the half line's two halves are exchanged by.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaReflection

open Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumEvenKernel

/-- **Inverting the argument multiplies the kernel by a square root.** -/
theorem evenKernel_zero_inv {x : ℝ} (hx : 0 < x) :
    HurwitzZeta.evenKernel 0 (1 / x) = Real.sqrt x * HurwitzZeta.evenKernel 0 x := by
  have hfe := HurwitzZeta.evenKernel_functional_equation 0 x
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at hfe
  have hne : x ^ (1 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx _)
  rw [Real.sqrt_eq_rpow, hfe]
  field_simp

/-- The square root of `e^{2u}` is `e^u`. -/
theorem sqrt_exp_two_mul (u : ℝ) : Real.sqrt (Real.exp (2 * u)) = Real.exp u := by
  have hsq : Real.exp (2 * u) = Real.exp u ^ 2 := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hsq, Real.sqrt_sq (Real.exp_pos u).le]

/-- **The kernel at the reflected point.** -/
theorem evenKernel_exp_neg (u : ℝ) :
    HurwitzZeta.evenKernel 0 (Real.exp (2 * -u))
      = Real.exp u * HurwitzZeta.evenKernel 0 (Real.exp (2 * u)) := by
  have hy : (0 : ℝ) < Real.exp (2 * u) := Real.exp_pos _
  have hinv : Real.exp (2 * -u) = 1 / Real.exp (2 * u) := by
    rw [show 2 * -u = -(2 * u) by ring, Real.exp_neg, one_div]
  rw [hinv, evenKernel_zero_inv hy, sqrt_exp_two_mul]

/-- **The theta sum differs from its reflection by a hyperbolic sine.** -/
theorem two_mul_thetaSum_neg (u : ℝ) :
    2 * thetaSum (-u) = 2 * thetaSum u + Real.exp (u / 2) - Real.exp (-u / 2) := by
  have h1 := two_mul_thetaSum_eq u
  have h2 := two_mul_thetaSum_eq (-u)
  rw [evenKernel_exp_neg u] at h2
  have hhalf : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2' : 2 * thetaSum (-u)
      = Real.exp (u / 2) * HurwitzZeta.evenKernel 0 (Real.exp (2 * u))
        - Real.exp (-u / 2) := by
    rw [h2, mul_sub, mul_one, ← mul_assoc, hhalf]
  linarith [h1, h2']

end Cvs.Xi.ThetaReflection
