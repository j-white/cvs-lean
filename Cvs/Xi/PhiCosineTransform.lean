import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.RiemannPhiKernel
import Cvs.Xi.ThetaDerivativeInheritDecay
import Cvs.Xi.ThetaSecondDerivContinuous
import Cvs.Xi.ThetaSumCosineTransform
import Cvs.Xi.ThetaSumExponentialDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The transform, carried across to `Φ`

Each half of the integrand is dominated by the same exponential, so the transform splits. The
kernel identity rewrites `Φ` as a combination of the theta sum and its second derivative, and the
split then reads the transform of `Φ` off the transform already proved.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Xi.PhiCosineTransform

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable
open Cvs.Xi.ThetaSumExponentialDecay Cvs.Xi.ThetaDerivativeSumsDecay Cvs.Xi.ThetaDerivativeInheritDecay Cvs.Xi.ThetaSecondDerivContinuous
open Cvs.Xi.ThetaSumCosineTransform

/-- **Continuity plus an exponential bound gives integrability on the half line.** -/
theorem integrableOn_of_exp_bound {f : ℝ → ℝ} (hf : Continuous f) {M c : ℝ} (hc : 0 < c)
    (hb : ∀ u : ℝ, 0 ≤ u → |f u| ≤ M * exp (-c * u)) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (g := fun u => M * exp (-c * u))
    ((exp_neg_integrableOn_Ioi 0 hc).const_mul _)
    hf.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs]
  exact hb u (le_of_lt hu)

theorem continuous_cos_mul (t : ℝ) : Continuous fun u : ℝ => cos (t * u) :=
  Real.continuous_cos.comp (continuous_const.mul continuous_id)

/-- The theta sum against the cosine is integrable. -/
theorem integrableOn_thetaSum_cos (t : ℝ) :
    IntegrableOn (fun u => thetaSum u * cos (t * u)) (Ioi (0 : ℝ)) := by
  refine integrableOn_of_exp_bound (M := exp (-(π / 2)) * domConst)
    (continuous_thetaSum.mul (continuous_cos_mul t)) rate_pos (fun u hu => ?_)
  have hK := domConst_nonneg
  have h0 : thetaSum u ≤ exp (-(π / 2)) * domConst * exp (-(π / 2 - 1 / 2) * u) := by
    refine (thetaSum_le hu).trans ?_
    refine (mul_le_mul_of_nonneg_right (exp_prefactor_le u) hK).trans ?_
    have hmono : exp (-((π - 1 / 2) * u)) ≤ exp (-(π / 2 - 1 / 2) * u) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [Real.pi_gt_three]
    calc exp (-(π / 2)) * exp (-((π - 1 / 2) * u)) * domConst
        ≤ exp (-(π / 2)) * exp (-(π / 2 - 1 / 2) * u) * domConst :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le) hK
      _ = exp (-(π / 2)) * domConst * exp (-(π / 2 - 1 / 2) * u) := by ring
  rw [abs_mul, abs_of_nonneg (thetaSum_nonneg u)]
  refine (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (thetaSum_nonneg u)).trans ?_
  rw [mul_one]
  exact h0

/-- The second derivative sum against the cosine is integrable. -/
theorem integrableOn_thetaSum2_cos (t : ℝ) :
    IntegrableOn (fun u => thetaSum2 u * cos (t * u)) (Ioi (0 : ℝ)) := by
  refine integrableOn_of_exp_bound
    (M := (16 / π ^ 2 + 384 / π + 256) * (exp (-(π / 4)) * domConst))
    (continuous_thetaSum2.mul (continuous_cos_mul t)) rate_pos (fun u hu => ?_)
  have hK := domConst_nonneg
  have hc : (0 : ℝ) ≤ 16 / π ^ 2 + 384 / π + 256 := by positivity
  have h2 : |thetaSum2 u|
      ≤ (16 / π ^ 2 + 384 / π + 256) * (exp (-(π / 4)) * domConst)
        * exp (-(π / 2 - 1 / 2) * u) := by
    refine (abs_thetaSum2_le hu).trans ?_
    refine (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_quarter_le u) hc) hK).trans (le_of_eq ?_)
    rw [show -((π / 2 - 1 / 2) * u) = -(π / 2 - 1 / 2) * u by ring]
    ring
  rw [abs_mul]
  refine (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans ?_
  rw [mul_one]
  exact h2

/-- **The transform splits.** -/
theorem integral_split (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), (thetaSum2 u + t ^ 2 * thetaSum u) * cos (t * u)
      = (∫ u in Ioi (0 : ℝ), thetaSum2 u * cos (t * u))
        + t ^ 2 * ∫ u in Ioi (0 : ℝ), thetaSum u * cos (t * u) := by
  have hsplit : ∀ u : ℝ, (thetaSum2 u + t ^ 2 * thetaSum u) * cos (t * u)
      = thetaSum2 u * cos (t * u) + t ^ 2 * (thetaSum u * cos (t * u)) := fun u => by ring
  simp_rw [hsplit]
  rw [integral_add (integrableOn_thetaSum2_cos t)
    ((integrableOn_thetaSum_cos t).const_mul _), integral_const_mul]

/-- **The transform of the theta sum's second derivative.** -/
theorem integral_thetaSum2_cos (t : ℝ) :
    (∫ u in Ioi (0 : ℝ), thetaSum2 u * cos (t * u))
      = -thetaSum1 0 - t ^ 2 * ∫ u in Ioi (0 : ℝ), thetaSum u * cos (t * u) := by
  have h := integral_integrand t
  rw [integral_split t] at h
  linarith

/-- **The transform of `Φ`.** -/
theorem four_mul_integral_riemannPhi (t : ℝ) :
    4 * ∫ u in Ioi (0 : ℝ), riemannPhi u * cos (t * u)
      = -2 * thetaSum1 0
        - 2 * (t ^ 2 + 1 / 4) * ∫ u in Ioi (0 : ℝ), thetaSum u * cos (t * u) := by
  have hpt : ∀ u : ℝ, riemannPhi u * cos (t * u)
      = (1 / 2) * (thetaSum2 u * cos (t * u)) - (1 / 8) * (thetaSum u * cos (t * u)) := by
    intro u
    have h := eight_mul_riemannPhi_eq u
    have hphi : riemannPhi u = (4 * thetaSum2 u - thetaSum u) / 8 := by linarith
    rw [hphi]; ring
  simp_rw [hpt]
  rw [integral_sub ((integrableOn_thetaSum2_cos t).const_mul _)
      ((integrableOn_thetaSum_cos t).const_mul _),
    integral_const_mul, integral_const_mul, integral_thetaSum2_cos t]
  ring

end Cvs.Xi.PhiCosineTransform
