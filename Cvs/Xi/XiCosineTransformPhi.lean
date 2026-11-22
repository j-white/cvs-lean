import Mathlib
import Cvs.Limit.ZeroFreeApproximantsRH
import Cvs.Xi.CompletedZetaCriticalReal
import Cvs.Xi.PhiCosineTransform
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.ThetaSumSlopeOrigin
import Cvs.Xi.ThetaTransformCompletedShape
import Cvs.Zeta.RiemannXi

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Riemann's `Ξ` is four times the cosine transform of `Φ`

The completed zeta carries a quadratic factor and a constant half; the transform of `Φ` carries the
same quadratic factor and the boundary value the fundamental theorem left behind. The slope of the
theta sum at the origin makes the two constants cancel.
-/

noncomputable section

open Set MeasureTheory Complex

namespace Cvs.Xi.XiCosineTransformPhi

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiKernelIdentitySums

/-- The quadratic factor on the critical line. -/
theorem quad_factor (τ : ℝ) :
    ((1 : ℂ) / 2 + (τ : ℂ) * I) * (((1 : ℂ) / 2 + (τ : ℂ) * I) - 1)
      = -((τ : ℂ) ^ 2 + 1 / 4) := by
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination ((τ : ℂ) ^ 2) * hI

/-- The argument, in the shape the completed zeta uses. -/
theorem arg_eq (τ : ℝ) :
    (1 : ℂ) / 2 + I * (τ : ℂ) = (1 : ℂ) / 2 + (τ : ℂ) * I := by
  ring

/-- **Riemann's `Ξ` is four times the cosine transform of `Φ`.** -/
theorem Xi_eq_four_mul_integral_riemannPhi (τ : ℝ) :
    Cvs.Limit.ZeroFreeApproximantsRH.Xi (τ : ℂ)
      = ((4 * ∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cos (τ * u) : ℝ) : ℂ) := by
  have h61 := Cvs.Xi.PhiCosineTransform.four_mul_integral_riemannPhi τ
  rw [Cvs.Xi.ThetaSumSlopeOrigin.thetaSum1_zero] at h61
  have h75 := Cvs.Xi.ThetaTransformCompletedShape.integral_thetaSum_cos_rpow τ
  have h73 := Cvs.Xi.CompletedZetaCriticalReal.completedRiemannZeta₀_critical τ
  have hXi : Cvs.Limit.ZeroFreeApproximantsRH.Xi (τ : ℂ)
      = -((τ : ℂ) ^ 2 + 1 / 4)
          * completedRiemannZeta₀ ((1 : ℂ) / 2 + (τ : ℂ) * I) / 2 + 1 / 2 := by
    rw [Cvs.Limit.ZeroFreeApproximantsRH.Xi, arg_eq τ, Cvs.Zeta.riemannXi, quad_factor τ]
  rw [h75] at h61
  have hreal : -((τ : ℝ) ^ 2 + 1 / 4)
        * (∫ x in Ioi (1 : ℝ), x ^ (-3 / 4 : ℝ) * Real.cos (τ / 2 * Real.log x)
            * (HurwitzZeta.evenKernel 0 x - 1)) / 2 + 1 / 2
      = 4 * ∫ u in Ioi (0 : ℝ), riemannPhi u * Real.cos (τ * u) := by
    linarith [h61]
  rw [hXi, h73, ← hreal]
  push_cast
  ring

end Cvs.Xi.XiCosineTransformPhi
