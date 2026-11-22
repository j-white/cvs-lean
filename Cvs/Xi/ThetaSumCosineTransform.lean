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
import Cvs.Xi.ThetaDerivativeInheritDecay
import Cvs.Xi.ThetaSecondDerivContinuous
import Cvs.Xi.ThetaSumExponentialDecay
import Cvs.Xi.ThetaSumsTwiceDifferentiable

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cosine transform of the theta sum, by one integration

The combination `θ'·cos(tu) + t·θ·sin(tu)` has derivative `(θ'' + t²θ)·cos(tu)` exactly, so the
transform needs the fundamental theorem once rather than a double integration by parts. Both sums
vanish at infinity and the derivative is dominated by an exponential, so the integral over the half
line is the boundary value at the origin.
-/

noncomputable section

open Real Set Filter Topology MeasureTheory

namespace Cvs.Xi.ThetaSumCosineTransform

open Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumsTwiceDifferentiable
open Cvs.Xi.ThetaSumExponentialDecay Cvs.Xi.ThetaDerivativeSumsDecay Cvs.Xi.ThetaDerivativeInheritDecay Cvs.Xi.ThetaSecondDerivContinuous

/-- The function the fundamental theorem is applied to. -/
def F (t u : ℝ) : ℝ := thetaSum1 u * cos (t * u) + t * (thetaSum u * sin (t * u))

theorem continuous_F (t : ℝ) : Continuous (F t) := by
  unfold F
  have hlin : Continuous fun u : ℝ => t * u := continuous_const.mul continuous_id
  exact (continuous_thetaSum1.mul (Real.continuous_cos.comp hlin)).add
    (continuous_const.mul (continuous_thetaSum.mul (Real.continuous_sin.comp hlin)))

/-- **The derivative is the integrand**, with the cross terms cancelling. -/
theorem hasDerivAt_F (t u : ℝ) :
    HasDerivAt (F t) ((thetaSum2 u + t ^ 2 * thetaSum u) * cos (t * u)) u := by
  have hlin : HasDerivAt (fun u : ℝ => t * u) t u := by
    simpa using (hasDerivAt_id u).const_mul t
  have hc : HasDerivAt (fun u : ℝ => cos (t * u)) (-sin (t * u) * t) u := hlin.cos
  have hs : HasDerivAt (fun u : ℝ => sin (t * u)) (cos (t * u) * t) u := hlin.sin
  have h1 := (hasDerivAt_thetaSum1 u).mul hc
  have h2 := (hasDerivAt_const u t).mul ((hasDerivAt_thetaSum u).mul hs)
  have h := h1.add h2
  refine h.congr_deriv ?_
  ring

/-- The rate the integrand decays at. -/
theorem rate_pos : (0 : ℝ) < π / 2 - 1 / 2 := by linarith [Real.pi_gt_three]

/-- **The integrand is dominated by an exponential.** -/
theorem abs_integrand_le {t u : ℝ} (hu : 0 ≤ u) :
    |(thetaSum2 u + t ^ 2 * thetaSum u) * cos (t * u)|
      ≤ ((16 / π ^ 2 + 384 / π + 256) * (exp (-(π / 4)) * domConst)
          + t ^ 2 * (exp (-(π / 2)) * domConst)) * exp (-(π / 2 - 1 / 2) * u) := by
  have hcos : |cos (t * u)| ≤ 1 := Real.abs_cos_le_one _
  have hK := domConst_nonneg
  -- the second derivative sum
  have h2 : |thetaSum2 u|
      ≤ (16 / π ^ 2 + 384 / π + 256) * (exp (-(π / 4)) * domConst)
        * exp (-(π / 2 - 1 / 2) * u) := by
    refine (abs_thetaSum2_le hu).trans ?_
    have hc : (0 : ℝ) ≤ 16 / π ^ 2 + 384 / π + 256 := by positivity
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (exp_quarter_le u) hc) hK
    refine this.trans (le_of_eq ?_)
    rw [show -((π / 2 - 1 / 2) * u) = -(π / 2 - 1 / 2) * u by ring]
    ring
  -- the sum itself, at the slower rate
  have h0 : thetaSum u ≤ exp (-(π / 2)) * domConst * exp (-(π / 2 - 1 / 2) * u) := by
    refine (thetaSum_le hu).trans ?_
    have hstep := mul_le_mul_of_nonneg_right (exp_prefactor_le u) hK
    refine hstep.trans ?_
    have hmono : exp (-((π - 1 / 2) * u)) ≤ exp (-(π / 2 - 1 / 2) * u) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [Real.pi_gt_three]
    calc exp (-(π / 2)) * exp (-((π - 1 / 2) * u)) * domConst
        ≤ exp (-(π / 2)) * exp (-(π / 2 - 1 / 2) * u) * domConst := by
          have := mul_le_mul_of_nonneg_left hmono (Real.exp_pos (-(π / 2))).le
          exact mul_le_mul_of_nonneg_right this hK
      _ = exp (-(π / 2)) * domConst * exp (-(π / 2 - 1 / 2) * u) := by ring
  have habs0 : |thetaSum u| = thetaSum u := abs_of_nonneg (thetaSum_nonneg u)
  have hsum : |thetaSum2 u + t ^ 2 * thetaSum u|
      ≤ ((16 / π ^ 2 + 384 / π + 256) * (exp (-(π / 4)) * domConst)
          + t ^ 2 * (exp (-(π / 2)) * domConst)) * exp (-(π / 2 - 1 / 2) * u) := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg (sq_nonneg t), habs0]
    have ht : t ^ 2 * thetaSum u
        ≤ t ^ 2 * (exp (-(π / 2)) * domConst * exp (-(π / 2 - 1 / 2) * u)) :=
      mul_le_mul_of_nonneg_left h0 (sq_nonneg t)
    nlinarith [h2, ht]
  rw [abs_mul]
  have hnn : (0 : ℝ) ≤ ((16 / π ^ 2 + 384 / π + 256) * (exp (-(π / 4)) * domConst)
      + t ^ 2 * (exp (-(π / 2)) * domConst)) * exp (-(π / 2 - 1 / 2) * u) := by
    have : (0 : ℝ) ≤ 16 / π ^ 2 + 384 / π + 256 := by positivity
    positivity
  calc |thetaSum2 u + t ^ 2 * thetaSum u| * |cos (t * u)|
      ≤ |thetaSum2 u + t ^ 2 * thetaSum u| * 1 :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |thetaSum2 u + t ^ 2 * thetaSum u| := mul_one _
    _ ≤ _ := hsum

/-- **The integrand is integrable on the half line.** -/
theorem integrableOn_integrand (t : ℝ) :
    IntegrableOn (fun u => (thetaSum2 u + t ^ 2 * thetaSum u) * cos (t * u)) (Ioi 0) := by
  have hcont : Continuous fun u : ℝ => (thetaSum2 u + t ^ 2 * thetaSum u) * cos (t * u) := by
    have hlin : Continuous fun u : ℝ => t * u := continuous_const.mul continuous_id
    exact (continuous_thetaSum2.add (continuous_const.mul continuous_thetaSum)).mul
      (Real.continuous_cos.comp hlin)
  refine Integrable.mono' (g := fun u => ((16 / π ^ 2 + 384 / π + 256)
      * (exp (-(π / 4)) * domConst) + t ^ 2 * (exp (-(π / 2)) * domConst))
      * exp (-(π / 2 - 1 / 2) * u))
    ((exp_neg_integrableOn_Ioi 0 rate_pos).const_mul _)
    hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs]
  exact abs_integrand_le (le_of_lt hu)

/-- **The boundary term vanishes at infinity.** -/
theorem tendsto_F (t : ℝ) : Tendsto (F t) atTop (𝓝 0) := by
  have hb : Tendsto (fun u : ℝ => |thetaSum1 u| + |t| * |thetaSum u|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => |thetaSum1 u|) atTop (𝓝 0) := by
      simpa using tendsto_thetaSum1.abs
    have h2 : Tendsto (fun u : ℝ => |t| * |thetaSum u|) atTop (𝓝 (|t| * 0)) := by
      exact (by simpa using tendsto_thetaSum.abs : Tendsto (fun u : ℝ => |thetaSum u|)
        atTop (𝓝 0)).const_mul _
    rw [mul_zero] at h2
    simpa using h1.add h2
  refine squeeze_zero_norm' (Eventually.of_forall fun u => ?_) hb
  rw [Real.norm_eq_abs]
  unfold F
  refine (abs_add_le _ _).trans ?_
  have hc : |thetaSum1 u * cos (t * u)| ≤ |thetaSum1 u| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans
      (le_of_eq (mul_one _))
  have hs : |t * (thetaSum u * sin (t * u))| ≤ |t| * |thetaSum u| := by
    rw [abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans
      (le_of_eq (mul_one _))
  linarith

/-- **The cosine transform, by one integration.** -/
theorem integral_integrand (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), (thetaSum2 u + t ^ 2 * thetaSum u) * cos (t * u) = -thetaSum1 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F t) (a := 0) (m := 0)
    (continuous_F t).continuousWithinAt
    (fun x _ => hasDerivAt_F t x)
    (integrableOn_integrand t) (tendsto_F t)
  rw [h]
  unfold F
  simp

end Cvs.Xi.ThetaSumCosineTransform
