import Mathlib
import Cvs.Xi.PhiEvenExtension
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.ThetaSecondDerivContinuous

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `Φ` and its even extension are continuous

Eight times `Φ` is four times the second derivative sum less the theta sum, and both of those are
continuous, so `Φ` is continuous on the line. The even extension is `Φ` composed with the absolute
value, so it inherits that continuity across the origin, where the reflection meets.
-/

noncomputable section

open Real Set

namespace Cvs.Xi.RiemannPhiContinuous

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSecondDerivContinuous Cvs.Xi.PhiEvenExtension

/-- `Φ` in terms of the theta sum and its second derivative sum. -/
theorem riemannPhi_eq_theta (u : ℝ) : riemannPhi u = (4 * thetaSum2 u - thetaSum u) / 8 := by
  have h := eight_mul_riemannPhi_eq u
  linarith

/-- **`Φ` is continuous on the line.** -/
theorem continuous_riemannPhi : Continuous riemannPhi := by
  have h : riemannPhi = fun u : ℝ => (4 * thetaSum2 u - thetaSum u) / 8 :=
    funext riemannPhi_eq_theta
  rw [h]
  exact ((continuous_const.mul continuous_thetaSum2).sub continuous_thetaSum).div_const 8

/-- **The even extension is continuous on the line.** -/
theorem continuous_phiEven : Continuous phiEven :=
  Complex.continuous_ofReal.comp (continuous_riemannPhi.comp continuous_abs)

end Cvs.Xi.RiemannPhiContinuous
