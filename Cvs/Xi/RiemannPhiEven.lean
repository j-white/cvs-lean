import Mathlib
import Cvs.Xi.PhiEvenExtension
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.RiemannPhiContinuous
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.ThetaReflection
import Cvs.Xi.ThetaSumSlopeOrigin
import Cvs.Xi.ThetaSumsTwiceDifferentiable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# `Φ` is even

The theta sum at a reflected point exceeds its value there by a hyperbolic sine, and
differentiating twice carries the excess to a quarter of that sine. Four times the second
derivative sum less the theta sum weights the two excesses oppositely, so they cancel and `Φ`
agrees at a point and its reflection; the even extension is then `Φ` itself.
-/

noncomputable section

open Real

namespace Cvs.Xi.RiemannPhiEven

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable Cvs.Xi.ThetaReflection Cvs.Xi.ThetaSumSlopeOrigin Cvs.Xi.PhiEvenExtension Cvs.Xi.RiemannPhiContinuous

theorem hasDerivAt_exp_half_gen (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (v / 2)) (Real.exp (u / 2) / 2) u := by
  have h : HasDerivAt (fun v : ℝ => v / 2) (1 / 2) u := by
    simpa using (hasDerivAt_id u).div_const 2
  have h2 := h.exp
  convert h2 using 1
  ring

theorem hasDerivAt_exp_neg_half_gen (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (-v / 2)) (-(Real.exp (-u / 2) / 2)) u := by
  have h : HasDerivAt (fun v : ℝ => -v / 2) (-1 / 2) u := by
    simpa using ((hasDerivAt_id u).neg).div_const 2
  have h2 := h.exp
  convert h2 using 1
  ring

theorem hasDerivAt_thetaSum1_neg_gen (u : ℝ) :
    HasDerivAt (fun v : ℝ => thetaSum1 (-v)) (-thetaSum2 (-u)) u := by
  have h : HasDerivAt (fun v : ℝ => thetaSum1 (-v)) (thetaSum2 (-u) * -1) u :=
    (hasDerivAt_thetaSum1 (-u)).comp u ((hasDerivAt_id u).neg)
  simpa using h

/-- **The first derivative sums at reflected points differ by half a hyperbolic cosine.** -/
theorem two_mul_thetaSum1_neg (u : ℝ) :
    -(2 * thetaSum1 (-u))
      = 2 * thetaSum1 u + Real.exp (u / 2) / 2 + Real.exp (-u / 2) / 2 := by
  have hfun : (fun v : ℝ => 2 * thetaSum (-v))
      = fun v : ℝ => 2 * thetaSum v + Real.exp (v / 2) - Real.exp (-v / 2) :=
    funext two_mul_thetaSum_neg
  have d1 : HasDerivAt (fun v : ℝ => 2 * thetaSum (-v)) (2 * -thetaSum1 (-u)) u :=
    HasDerivAt.const_mul 2 (hasDerivAt_thetaSum_neg_gen u)
  have d2 : HasDerivAt (fun v : ℝ => 2 * thetaSum v + Real.exp (v / 2) - Real.exp (-v / 2))
      (2 * thetaSum1 u + Real.exp (u / 2) / 2 - -(Real.exp (-u / 2) / 2)) u :=
    ((HasDerivAt.const_mul 2 (hasDerivAt_thetaSum u)).add (hasDerivAt_exp_half_gen u)).sub
      (hasDerivAt_exp_neg_half_gen u)
  rw [hfun] at d1
  have h := d1.unique d2
  linarith

/-- **The second derivative sums at reflected points differ by a quarter of the sine.** -/
theorem two_mul_thetaSum2_neg (u : ℝ) :
    2 * thetaSum2 (-u)
      = 2 * thetaSum2 u + (Real.exp (u / 2) - Real.exp (-u / 2)) / 4 := by
  have hfun : (fun v : ℝ => -(2 * thetaSum1 (-v)))
      = fun v : ℝ => 2 * thetaSum1 v + Real.exp (v / 2) / 2 + Real.exp (-v / 2) / 2 :=
    funext two_mul_thetaSum1_neg
  have d1 : HasDerivAt (fun v : ℝ => -(2 * thetaSum1 (-v))) (-(2 * -thetaSum2 (-u))) u :=
    (HasDerivAt.const_mul 2 (hasDerivAt_thetaSum1_neg_gen u)).neg
  have d2 : HasDerivAt
      (fun v : ℝ => 2 * thetaSum1 v + Real.exp (v / 2) / 2 + Real.exp (-v / 2) / 2)
      (2 * thetaSum2 u + Real.exp (u / 2) / 2 / 2 + -(Real.exp (-u / 2) / 2) / 2) u :=
    ((HasDerivAt.const_mul 2 (hasDerivAt_thetaSum1 u)).add
      ((hasDerivAt_exp_half_gen u).div_const 2)).add
      ((hasDerivAt_exp_neg_half_gen u).div_const 2)
  rw [hfun] at d1
  have h := d1.unique d2
  linarith

/-- **`Φ` is even.** -/
theorem riemannPhi_neg (u : ℝ) : riemannPhi (-u) = riemannPhi u := by
  have h2 := two_mul_thetaSum2_neg u
  have h0 := two_mul_thetaSum_neg u
  rw [riemannPhi_eq_theta, riemannPhi_eq_theta]
  linarith

/-- **`Φ` at the absolute value is `Φ`.** -/
theorem riemannPhi_abs (u : ℝ) : riemannPhi |u| = riemannPhi u := by
  rcases abs_choice u with h | h
  · rw [h]
  · rw [h, riemannPhi_neg]

/-- **The even extension is `Φ` itself.** -/
theorem phiEven_eq (u : ℝ) : phiEven u = ((riemannPhi u : ℝ) : ℂ) := by
  simp only [phiEven, riemannPhi_abs]

end Cvs.Xi.RiemannPhiEven
