import Mathlib
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.RiemannPhiContinuous
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.ThetaSecondSumDeriv
import Cvs.Xi.ThetaSumsTwiceDifferentiable
import Cvs.Xi.ThetaTermFourthDominated
import Cvs.Xi.ThetaTermThirdDominated
import Cvs.Xi.ThetaThirdSumDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `Φ` is twice differentiable

`Φ` is a fixed combination of the theta sum and its second derivative sum, and each of those now
has a derivative at every point, so the same combination one level up is `Φ`'s derivative, and the
combination two levels up is the derivative of that.
-/

noncomputable section

open Real

namespace Cvs.Xi.PhiTwiceDifferentiable

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable Cvs.Xi.RiemannPhiContinuous Cvs.Xi.ThetaTermThirdDominated Cvs.Xi.ThetaSecondSumDeriv Cvs.Xi.ThetaTermFourthDominated Cvs.Xi.ThetaThirdSumDeriv

/-- The first derivative of `Φ`. -/
noncomputable def riemannPhi1 (u : ℝ) : ℝ := (4 * thetaSum3 u - thetaSum1 u) / 8

/-- The second derivative of `Φ`. -/
noncomputable def riemannPhi2 (u : ℝ) : ℝ := (4 * thetaSum4 u - thetaSum2 u) / 8

/-- **`Φ` has a derivative at every point.** -/
theorem hasDerivAt_riemannPhi (u : ℝ) : HasDerivAt riemannPhi (riemannPhi1 u) u := by
  have h : riemannPhi = fun v : ℝ => (4 * thetaSum2 v - thetaSum v) / 8 :=
    funext riemannPhi_eq_theta
  rw [h]
  exact ((HasDerivAt.const_mul 4 (hasDerivAt_thetaSum2 u)).sub
    (hasDerivAt_thetaSum u)).div_const 8

/-- **The first derivative of `Φ` has a derivative at every point.** -/
theorem hasDerivAt_riemannPhi1 (u : ℝ) : HasDerivAt riemannPhi1 (riemannPhi2 u) u :=
  ((HasDerivAt.const_mul 4 (hasDerivAt_thetaSum3 u)).sub
    (hasDerivAt_thetaSum1 u)).div_const 8

theorem differentiable_riemannPhi1 : Differentiable ℝ riemannPhi1 :=
  fun u => (hasDerivAt_riemannPhi1 u).differentiableAt

end Cvs.Xi.PhiTwiceDifferentiable
