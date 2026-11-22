import Mathlib
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.PhiThetaDifferentialOperator
import Cvs.Xi.PhiTwiceDifferentiable
import Cvs.Xi.RiemannPhiEven
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.ThetaDerivativeInheritDecay
import Cvs.Xi.ThetaHigherSumsDecay
import Cvs.Xi.ThetaOcticDominatingSeries
import Cvs.Xi.ThetaSecondDerivContinuous
import Cvs.Xi.ThetaSumExponentialDecay
import Cvs.Xi.ThetaTermFourthDeriv
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
# The derivatives of `Φ` are continuous, signed, and small

Reflection sends `Φ` to itself, so its first derivative changes sign and its second does not.
Past the origin the inner factor outgrows its own tangent line fast enough that a quarter of it
pays the half power in front and leaves a plain decaying exponential, which bounds both
derivatives there.
-/

noncomputable section

open Real Set

namespace Cvs.Xi.PhiDerivativesSignedSmall

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable Cvs.Xi.ThetaSumExponentialDecay Cvs.Xi.ThetaDerivativeInheritDecay Cvs.Xi.ThetaSecondDerivContinuous Cvs.Xi.RiemannPhiEven Cvs.Xi.ThetaTermThirdDeriv Cvs.Xi.ThetaTermThirdDominated Cvs.Xi.ThetaTermFourthDeriv Cvs.Xi.ThetaTermFourthDominated Cvs.Xi.ThetaThirdSumDeriv Cvs.Xi.PhiTwiceDifferentiable Cvs.Xi.ThetaOcticDominatingSeries Cvs.Xi.ThetaHigherSumsDecay

/-- **A quarter of the inner factor pays the half power and leaves a decaying exponential.** -/
theorem exp_half_sub_le {u : ℝ} (hu : 0 ≤ u) :
    exp (u / 2) * exp (-(π / 4 * exp (2 * u))) ≤ exp (-(π / 4)) * exp (-u) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h := Real.add_one_le_exp (2 * u)
  have hpi := Real.pi_gt_three
  nlinarith [hu, h, hpi]

theorem continuous_thetaTerm4 (n : ℕ) : Continuous (thetaTerm4 n) := by
  unfold thetaTerm4 thetaTerm; fun_prop

/-- The fourth derivative sum is continuous on any bounded interval. -/
theorem continuousOn_thetaSum4 (y : ℝ) :
    ContinuousOn thetaSum4 (Ioo (y - 1) (y + 1)) := by
  unfold thetaSum4
  refine continuousOn_tsum (fun n => (continuous_thetaTerm4 (n + 1)).continuousOn)
    ((summable_nat_add_iff 1).mpr (summable_bnd4 (y - 1) (y + 1))) (fun n x hx => ?_)
  rw [Real.norm_eq_abs]
  exact abs_thetaTerm4_le_bnd hx.1.le hx.2.le (n + 1)

theorem continuous_thetaSum4 : Continuous thetaSum4 := by
  rw [continuous_iff_continuousAt]
  intro y
  exact (continuousOn_thetaSum4 y).continuousAt
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)

theorem continuous_riemannPhi1 : Continuous riemannPhi1 :=
  differentiable_riemannPhi1.continuous

theorem continuous_riemannPhi2 : Continuous riemannPhi2 := by
  unfold riemannPhi2
  exact ((continuous_const.mul continuous_thetaSum4).sub continuous_thetaSum2).div_const 8

/-- **The first derivative of `Φ` is odd.** -/
theorem riemannPhi1_neg (u : ℝ) : riemannPhi1 (-u) = -riemannPhi1 u := by
  have hfun : (fun v : ℝ => riemannPhi (-v)) = riemannPhi := funext riemannPhi_neg
  have d0 : HasDerivAt (fun v : ℝ => riemannPhi (-v)) (riemannPhi1 (-u) * -1) u :=
    (hasDerivAt_riemannPhi (-u)).comp u ((hasDerivAt_id u).neg)
  have d1 : HasDerivAt (fun v : ℝ => riemannPhi (-v)) (-riemannPhi1 (-u)) u := by
    simpa using d0
  rw [hfun] at d1
  have h := d1.unique (hasDerivAt_riemannPhi u)
  linarith

/-- **The second derivative of `Φ` is even.** -/
theorem riemannPhi2_neg (u : ℝ) : riemannPhi2 (-u) = riemannPhi2 u := by
  have hfun : (fun v : ℝ => riemannPhi1 (-v)) = fun v : ℝ => -riemannPhi1 v :=
    funext riemannPhi1_neg
  have d0 : HasDerivAt (fun v : ℝ => riemannPhi1 (-v)) (riemannPhi2 (-u) * -1) u :=
    (hasDerivAt_riemannPhi1 (-u)).comp u ((hasDerivAt_id u).neg)
  have d1 : HasDerivAt (fun v : ℝ => riemannPhi1 (-v)) (-riemannPhi2 (-u)) u := by
    simpa using d0
  rw [hfun] at d1
  have h := d1.unique (hasDerivAt_riemannPhi1 u).neg
  linarith

/-- The constant in the first derivative's bound. -/
def phi1Const : ℝ :=
  (4 * (216 / π ^ 3 + 26784 / π ^ 2 + 51840 / π + 13824) * domConst8
    + (2 / π + 8) * domConst) / 8

/-- The constant in the second derivative's bound. -/
def phi2Const : ℝ :=
  (4 * (4096 / π ^ 4 + 2555904 / π ^ 3 + 10878976 / π ^ 2 + 7340032 / π + 1048576) * domConst8
    + (16 / π ^ 2 + 384 / π + 256) * domConst) / 8

theorem phi1Const_nonneg : 0 ≤ phi1Const := by
  have hA : (0 : ℝ) ≤ 4 * (216 / π ^ 3 + 26784 / π ^ 2 + 51840 / π + 13824) * domConst8 :=
    mul_nonneg (by positivity) domConst8_nonneg
  have hB : (0 : ℝ) ≤ (2 / π + 8) * domConst := mul_nonneg (by positivity) domConst_nonneg
  unfold phi1Const
  linarith

theorem phi2Const_nonneg : 0 ≤ phi2Const := by
  have hA : (0 : ℝ) ≤ 4 * (4096 / π ^ 4 + 2555904 / π ^ 3 + 10878976 / π ^ 2
      + 7340032 / π + 1048576) * domConst8 := mul_nonneg (by positivity) domConst8_nonneg
  have hB : (0 : ℝ) ≤ (16 / π ^ 2 + 384 / π + 256) * domConst :=
    mul_nonneg (by positivity) domConst_nonneg
  unfold phi2Const
  linarith

/-- **The first derivative of `Φ` decays on the half line.** -/
theorem abs_riemannPhi1_le {u : ℝ} (hu : 0 ≤ u) :
    |riemannPhi1 u| ≤ phi1Const * (exp (-(π / 4)) * exp (-u)) := by
  obtain ⟨l3, r3⟩ := abs_le.mp (abs_thetaSum3_le hu)
  obtain ⟨l1, r1⟩ := abs_le.mp (abs_thetaSum1_le hu)
  have hstep := exp_half_sub_le hu
  have hK3 : (0 : ℝ) ≤ 216 / π ^ 3 + 26784 / π ^ 2 + 51840 / π + 13824 := by positivity
  have hK1 : (0 : ℝ) ≤ 2 / π + 8 := by positivity
  have hm3 := mul_le_mul_of_nonneg_left hstep (mul_nonneg hK3 domConst8_nonneg)
  have hm1 := mul_le_mul_of_nonneg_left hstep (mul_nonneg hK1 domConst_nonneg)
  unfold riemannPhi1 phi1Const
  rw [abs_le]
  constructor <;> nlinarith [hm3, hm1, l3, r3, l1, r1]

/-- **The second derivative of `Φ` decays on the half line.** -/
theorem abs_riemannPhi2_le {u : ℝ} (hu : 0 ≤ u) :
    |riemannPhi2 u| ≤ phi2Const * (exp (-(π / 4)) * exp (-u)) := by
  obtain ⟨l4, r4⟩ := abs_le.mp (abs_thetaSum4_le hu)
  obtain ⟨l2, r2⟩ := abs_le.mp (abs_thetaSum2_le hu)
  have hstep := exp_half_sub_le hu
  have hK4 : (0 : ℝ) ≤ 4096 / π ^ 4 + 2555904 / π ^ 3 + 10878976 / π ^ 2
      + 7340032 / π + 1048576 := by positivity
  have hK2 : (0 : ℝ) ≤ 16 / π ^ 2 + 384 / π + 256 := by positivity
  have hm4 := mul_le_mul_of_nonneg_left hstep (mul_nonneg hK4 domConst8_nonneg)
  have hm2 := mul_le_mul_of_nonneg_left hstep (mul_nonneg hK2 domConst_nonneg)
  unfold riemannPhi2 phi2Const
  rw [abs_le]
  constructor <;> nlinarith [hm4, hm2, l4, r4, l2, r2]

end Cvs.Xi.PhiDerivativesSignedSmall
