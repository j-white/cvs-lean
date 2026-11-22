import Mathlib
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.ThetaReflection
import Cvs.Xi.ThetaSumsTwiceDifferentiable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The theta sum's slope at the origin

Reflecting the variable sends the theta sum to itself plus a hyperbolic sine, and differentiating
that identity at the origin determines the slope: the reflection contributes its negative, the sine
contributes one, and the two together fix the value.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaSumSlopeOrigin

open Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable Cvs.Xi.ThetaReflection

theorem hasDerivAt_thetaSum_neg_gen (u : ℝ) :
    HasDerivAt (fun v : ℝ => thetaSum (-v)) (-thetaSum1 (-u)) u := by
  have h : HasDerivAt (fun v : ℝ => thetaSum (-v)) (thetaSum1 (-u) * -1) u :=
    (hasDerivAt_thetaSum (-u)).comp u ((hasDerivAt_id u).neg)
  simpa using h

theorem hasDerivAt_thetaSum_neg :
    HasDerivAt (fun u : ℝ => thetaSum (-u)) (-thetaSum1 0) 0 := by
  simpa using hasDerivAt_thetaSum_neg_gen 0

theorem hasDerivAt_exp_half :
    HasDerivAt (fun u : ℝ => Real.exp (u / 2)) (1 / 2) 0 := by
  have h : HasDerivAt (fun u : ℝ => u / 2) (1 / 2) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).div_const 2
  simpa using h.exp

theorem hasDerivAt_exp_neg_half :
    HasDerivAt (fun u : ℝ => Real.exp (-u / 2)) (-1 / 2) 0 := by
  have h : HasDerivAt (fun u : ℝ => -u / 2) (-1 / 2) 0 :=
    ((hasDerivAt_id (0 : ℝ)).neg).div_const 2
  simpa using h.exp

/-- **The theta sum's slope at the origin.** -/
theorem thetaSum1_zero : thetaSum1 0 = -(1 / 4) := by
  have hfun : (fun u : ℝ => 2 * thetaSum (-u))
      = fun u : ℝ => 2 * thetaSum u + Real.exp (u / 2) - Real.exp (-u / 2) :=
    funext two_mul_thetaSum_neg
  have d1 : HasDerivAt (fun u : ℝ => 2 * thetaSum (-u)) (2 * -thetaSum1 0) 0 :=
    HasDerivAt.const_mul 2 hasDerivAt_thetaSum_neg
  have d2 : HasDerivAt (fun u : ℝ => 2 * thetaSum u + Real.exp (u / 2) - Real.exp (-u / 2))
      (2 * thetaSum1 0 + 1 / 2 - -1 / 2) 0 :=
    ((HasDerivAt.const_mul 2 (hasDerivAt_thetaSum (0 : ℝ))).add hasDerivAt_exp_half).sub
      hasDerivAt_exp_neg_half
  rw [hfun] at d1
  have := d1.unique d2
  linarith

end Cvs.Xi.ThetaSumSlopeOrigin
