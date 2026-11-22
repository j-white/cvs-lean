import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Cvs.Xi.PhiKernelIdentitySums
import Cvs.Xi.PhiThetaDifferentialOperator
import Cvs.Xi.ThetaDerivativeSumsDecay
import Cvs.Xi.ThetaSumExponentialDecay

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The derivative sums inherit the decay

A term whose prefactor is paid by a quarter of the exponential factor is bounded by the same
summable remainder, with the rest of the factor still in hand. Both derivative sums therefore obey
a bound of the shape a constant times `e^{u/2}e^{−(π/4)e^{2u}}`, which is an exponential with
negative rate, and the first of them tends to zero.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.Xi.ThetaDerivativeInheritDecay

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums
open Cvs.Xi.ThetaSumExponentialDecay Cvs.Xi.ThetaDerivativeSumsDecay

/-- The remainder of the dominating series. -/
def dom (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ) ^ 4 + 1) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))

/-- **A prefactor paid by a quarter of the factor leaves the rest in hand.** -/
theorem term_bound {u P C T : ℝ} (hu : 0 ≤ u) (hP : 0 ≤ P)
    (hPC : P * exp (-(π / 4 * exp (2 * u))) ≤ C) (n : ℕ)
    (hT : |T| ≤ exp (u / 2) * P
      * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2)))) :
    |T| ≤ (C * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom n := by
  have hq : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 4 + 1 := by positivity
  have he : (0 : ℝ) < exp (u / 2) := Real.exp_pos _
  have hsplit := exp_split hu n
  have hhalf : exp (-(π / 2 * exp (2 * u)))
      = exp (-(π / 4 * exp (2 * u))) * exp (-(π / 4 * exp (2 * u))) := by
    rw [← Real.exp_add]; congr 1; ring
  -- replace the full exponent by the split one
  have h1 : exp (u / 2) * P
      * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1) * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2)))
      ≤ exp (u / 2) * P
        * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1)
          * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2)))) := by
    have hin : (((n + 1 : ℕ) : ℝ) ^ 4 + 1)
        * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2))
        ≤ (((n + 1 : ℕ) : ℝ) ^ 4 + 1)
          * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left hsplit hq
    exact mul_le_mul_of_nonneg_left hin (by positivity)
  -- pay the prefactor with one quarter of the factor
  have h2 : exp (u / 2) * P
      * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1)
        * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))))
      ≤ (C * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom n := by
    have hrest : (0 : ℝ) ≤ exp (u / 2) * exp (-(π / 4 * exp (2 * u)))
        * ((((n + 1 : ℕ) : ℝ) ^ 4 + 1) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))) := by
      positivity
    have := mul_le_mul_of_nonneg_right hPC hrest
    unfold dom
    rw [hhalf]
    nlinarith [this]
  exact hT.trans (h1.trans h2)

theorem summable_bound (K u : ℝ) :
    Summable (fun n : ℕ => (K * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom n) :=
  (summable_dom).mul_left _

/-- **The first derivative sum's bound.** -/
theorem abs_thetaSum1_le {u : ℝ} (hu : 0 ≤ u) :
    |thetaSum1 u|
      ≤ ((2 / π + 8) * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * domConst := by
  have hbd : ∀ n : ℕ, |thetaTerm1 (n + 1) u|
      ≤ ((2 / π + 8) * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom n := fun n =>
    term_bound hu (by positivity) (prefactor_one_le hu) n (abs_thetaTerm1_le (n + 1) u)
  have hsummable : Summable (fun n : ℕ => |thetaTerm1 (n + 1) u|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbd (summable_bound _ u)
  have hnorm : Summable (fun n : ℕ => ‖thetaTerm1 (n + 1) u‖) := by
    simpa [Real.norm_eq_abs] using hsummable
  have h1 : |thetaSum1 u| ≤ ∑' n : ℕ, |thetaTerm1 (n + 1) u| := by
    unfold thetaSum1
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  refine h1.trans ?_
  have h2 := Summable.tsum_le_tsum hbd hsummable (summable_bound _ u)
  rw [tsum_mul_left] at h2
  exact h2

/-- **The second derivative sum's bound.** -/
theorem abs_thetaSum2_le {u : ℝ} (hu : 0 ≤ u) :
    |thetaSum2 u|
      ≤ ((16 / π ^ 2 + 384 / π + 256) * (exp (u / 2) * exp (-(π / 4 * exp (2 * u)))))
        * domConst := by
  have hbd : ∀ n : ℕ, |thetaTerm2 (n + 1) u|
      ≤ ((16 / π ^ 2 + 384 / π + 256) * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom n :=
    fun n => term_bound hu (by positivity) (prefactor_two_le hu) n (abs_thetaTerm2_le (n + 1) u)
  have hsummable : Summable (fun n : ℕ => |thetaTerm2 (n + 1) u|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hbd (summable_bound _ u)
  have hnorm : Summable (fun n : ℕ => ‖thetaTerm2 (n + 1) u‖) := by
    simpa [Real.norm_eq_abs] using hsummable
  have h1 : |thetaSum2 u| ≤ ∑' n : ℕ, |thetaTerm2 (n + 1) u| := by
    unfold thetaSum2
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
  refine h1.trans ?_
  have h2 := Summable.tsum_le_tsum hbd hsummable (summable_bound _ u)
  rw [tsum_mul_left] at h2
  exact h2

/-- **A quarter of the factor still beats the prefactor.** -/
theorem exp_quarter_le (u : ℝ) :
    exp (u / 2) * exp (-(π / 4 * exp (2 * u)))
      ≤ exp (-(π / 4)) * exp (-((π / 2 - 1 / 2) * u)) := by
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hE : 1 + 2 * u ≤ exp (2 * u) := by
    have := Real.add_one_le_exp (2 * u); linarith
  have hpi := Real.pi_pos
  nlinarith

/-- **The first derivative sum tends to zero.** -/
theorem tendsto_thetaSum1 : Tendsto thetaSum1 atTop (𝓝 0) := by
  have hr : 0 < π / 2 - 1 / 2 := by linarith [Real.pi_gt_three]
  have h1 : Tendsto (fun u : ℝ => -((π / 2 - 1 / 2) * u)) atTop atBot :=
    Filter.tendsto_neg_atBot_iff.mpr (Filter.Tendsto.const_mul_atTop hr Filter.tendsto_id)
  have hexp : Tendsto (fun u : ℝ => exp (-((π / 2 - 1 / 2) * u))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  have hbig := hexp.const_mul ((2 / π + 8) * (exp (-(π / 4)) * domConst))
  rw [mul_zero] at hbig
  refine squeeze_zero_norm' ?_ hbig
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [Real.norm_eq_abs]
  refine (abs_thetaSum1_le hu).trans ?_
  have hc : (0 : ℝ) ≤ 2 / π + 8 := by positivity
  have hstep := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (exp_quarter_le u) hc) domConst_nonneg
  exact hstep.trans (le_of_eq (by ring))

end Cvs.Xi.ThetaDerivativeInheritDecay
