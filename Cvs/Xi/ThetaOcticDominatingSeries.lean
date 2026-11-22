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
import Cvs.Xi.ThetaDerivativeSumsDecay
import Cvs.Xi.ThetaSumExponentialDecay
import Cvs.Xi.ThetaTermFourthDominated

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The octic dominating series and the deeper prefactors

The third and fourth derivative terms reach the sixth and eighth powers of the index, and the
eighth covers both, so one octic series dominates the pair. Their coefficients are a cubic and a
quartic in the inner exponential, and an exponential beats a polynomial: splitting a quarter of
the factor into three parts pays the cubic, and into four parts pays the quartic.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaOcticDominatingSeries

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaSumExponentialDecay Cvs.Xi.ThetaDerivativeSumsDecay Cvs.Xi.ThetaTermFourthDominated

/-- The remainder of the octic dominating series. -/
def dom8 (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ) ^ 8 + 1) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))

theorem dom8_nonneg (n : ℕ) : 0 ≤ dom8 n := by unfold dom8; positivity

theorem summable_dom8 : Summable dom8 :=
  (summable_nat_add_iff 1).mpr (summable_octic_exp (by positivity))

/-- The octic dominating constant. -/
def domConst8 : ℝ := ∑' n : ℕ, dom8 n

theorem domConst8_nonneg : 0 ≤ domConst8 := tsum_nonneg dom8_nonneg

/-- **A prefactor paid by a quarter of the factor leaves the rest in hand.** -/
theorem term_bound8 {u P C T : ℝ} (hu : 0 ≤ u) (hP : 0 ≤ P)
    (hPC : P * exp (-(π / 4 * exp (2 * u))) ≤ C) (n : ℕ)
    (hT : |T| ≤ exp (u / 2) * P
      * ((((n + 1 : ℕ) : ℝ) ^ 8 + 1) * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2)))) :
    |T| ≤ (C * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom8 n := by
  have hq : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 8 + 1 := by positivity
  have he : (0 : ℝ) < exp (u / 2) := Real.exp_pos _
  have hsplit := exp_split hu n
  have hhalf : exp (-(π / 2 * exp (2 * u)))
      = exp (-(π / 4 * exp (2 * u))) * exp (-(π / 4 * exp (2 * u))) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : exp (u / 2) * P
      * ((((n + 1 : ℕ) : ℝ) ^ 8 + 1) * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2)))
      ≤ exp (u / 2) * P
        * ((((n + 1 : ℕ) : ℝ) ^ 8 + 1)
          * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2)))) := by
    have hin : (((n + 1 : ℕ) : ℝ) ^ 8 + 1)
        * exp (-(π * exp (2 * u) * ((n + 1 : ℕ) : ℝ) ^ 2))
        ≤ (((n + 1 : ℕ) : ℝ) ^ 8 + 1)
          * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_left hsplit hq
    exact mul_le_mul_of_nonneg_left hin (by positivity)
  have h2 : exp (u / 2) * P
      * ((((n + 1 : ℕ) : ℝ) ^ 8 + 1)
        * (exp (-(π / 2 * exp (2 * u))) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))))
      ≤ (C * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom8 n := by
    have hrest : (0 : ℝ) ≤ exp (u / 2) * exp (-(π / 4 * exp (2 * u)))
        * ((((n + 1 : ℕ) : ℝ) ^ 8 + 1) * exp (-(π / 2 * ((n + 1 : ℕ) : ℝ) ^ 2))) := by
      positivity
    have := mul_le_mul_of_nonneg_right hPC hrest
    unfold dom8
    rw [hhalf]
    nlinarith [this]
  exact hT.trans (h1.trans h2)

theorem summable_bound8 (K u : ℝ) :
    Summable (fun n : ℕ => (K * (exp (u / 2) * exp (-(π / 4 * exp (2 * u))))) * dom8 n) :=
  summable_dom8.mul_left _

/-- **A third of a quarter of the factor pays the third derivative's prefactor.** -/
theorem prefactor_three_le {u : ℝ} (hu : 0 ≤ u) :
    (1 / 8 + 31 / 2 * π * exp (2 * u) + 30 * π ^ 2 * exp (2 * u) ^ 2
        + 8 * π ^ 3 * exp (2 * u) ^ 3) * exp (-(π / 4 * exp (2 * u)))
      ≤ 216 / π ^ 3 + 26784 / π ^ 2 + 51840 / π + 13824 := by
  have hpi := Real.pi_pos
  have hE1 : (1 : ℝ) ≤ exp (2 * u) := Real.one_le_exp (by linarith)
  have hEpos : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hE2 : (1 : ℝ) ≤ exp (2 * u) ^ 2 := by nlinarith
  have hE3 : (1 : ℝ) ≤ exp (2 * u) ^ 3 := by nlinarith
  have hy : (0 : ℝ) < π / 12 * exp (2 * u) := by positivity
  have h12 : exp (-(π / 12 * exp (2 * u))) ≤ 12 / (π * exp (2 * u)) := by
    refine (exp_neg_le_inv hy).trans (le_of_eq ?_)
    field_simp
  have hcube : exp (-(π / 4 * exp (2 * u))) ≤ (12 / (π * exp (2 * u))) ^ 3 := by
    have htriple : exp (-(π / 4 * exp (2 * u)))
        = exp (-(π / 12 * exp (2 * u))) * exp (-(π / 12 * exp (2 * u)))
          * exp (-(π / 12 * exp (2 * u))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [htriple, pow_succ, pow_succ, pow_one]
    exact mul_le_mul (mul_le_mul h12 h12 (Real.exp_pos _).le (by positivity)) h12
      (Real.exp_pos _).le (by positivity)
  have hfac : (0 : ℝ) ≤ 1 / 8 + 31 / 2 * π * exp (2 * u) + 30 * π ^ 2 * exp (2 * u) ^ 2
      + 8 * π ^ 3 * exp (2 * u) ^ 3 := by positivity
  refine (mul_le_mul_of_nonneg_left hcube hfac).trans ?_
  have heq : (1 / 8 + 31 / 2 * π * exp (2 * u) + 30 * π ^ 2 * exp (2 * u) ^ 2
        + 8 * π ^ 3 * exp (2 * u) ^ 3) * (12 / (π * exp (2 * u))) ^ 3
      = 216 / π ^ 3 * (1 / exp (2 * u) ^ 3) + 26784 / π ^ 2 * (1 / exp (2 * u) ^ 2)
        + 51840 / π * (1 / exp (2 * u)) + 13824 := by
    field_simp
    ring
  rw [heq]
  have hi1 : 1 / exp (2 * u) ≤ 1 := by rw [div_le_one hEpos]; exact hE1
  have hi2 : 1 / exp (2 * u) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hE2
  have hi3 : 1 / exp (2 * u) ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; exact hE3
  nlinarith [mul_le_mul_of_nonneg_left hi3 (show (0 : ℝ) ≤ 216 / π ^ 3 by positivity),
    mul_le_mul_of_nonneg_left hi2 (show (0 : ℝ) ≤ 26784 / π ^ 2 by positivity),
    mul_le_mul_of_nonneg_left hi1 (show (0 : ℝ) ≤ 51840 / π by positivity)]

/-- **A quarter of a quarter of the factor pays the fourth derivative's prefactor.** -/
theorem prefactor_four_le {u : ℝ} (hu : 0 ≤ u) :
    (1 / 16 + 39 * π * exp (2 * u) + 166 * π ^ 2 * exp (2 * u) ^ 2
        + 112 * π ^ 3 * exp (2 * u) ^ 3 + 16 * π ^ 4 * exp (2 * u) ^ 4)
        * exp (-(π / 4 * exp (2 * u)))
      ≤ 4096 / π ^ 4 + 2555904 / π ^ 3 + 10878976 / π ^ 2 + 7340032 / π + 1048576 := by
  have hpi := Real.pi_pos
  have hE1 : (1 : ℝ) ≤ exp (2 * u) := Real.one_le_exp (by linarith)
  have hEpos : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hE2 : (1 : ℝ) ≤ exp (2 * u) ^ 2 := by nlinarith
  have hE3 : (1 : ℝ) ≤ exp (2 * u) ^ 3 := by nlinarith
  have hE4 : (1 : ℝ) ≤ exp (2 * u) ^ 4 := by nlinarith
  have hy : (0 : ℝ) < π / 16 * exp (2 * u) := by positivity
  have h16 : exp (-(π / 16 * exp (2 * u))) ≤ 16 / (π * exp (2 * u)) := by
    refine (exp_neg_le_inv hy).trans (le_of_eq ?_)
    field_simp
  have hquart : exp (-(π / 4 * exp (2 * u))) ≤ (16 / (π * exp (2 * u))) ^ 4 := by
    have hfour : exp (-(π / 4 * exp (2 * u)))
        = exp (-(π / 16 * exp (2 * u))) * exp (-(π / 16 * exp (2 * u)))
          * exp (-(π / 16 * exp (2 * u))) * exp (-(π / 16 * exp (2 * u))) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [hfour, pow_succ, pow_succ, pow_succ, pow_one]
    exact mul_le_mul (mul_le_mul (mul_le_mul h16 h16 (Real.exp_pos _).le (by positivity)) h16
      (Real.exp_pos _).le (by positivity)) h16 (Real.exp_pos _).le (by positivity)
  have hfac : (0 : ℝ) ≤ 1 / 16 + 39 * π * exp (2 * u) + 166 * π ^ 2 * exp (2 * u) ^ 2
      + 112 * π ^ 3 * exp (2 * u) ^ 3 + 16 * π ^ 4 * exp (2 * u) ^ 4 := by positivity
  refine (mul_le_mul_of_nonneg_left hquart hfac).trans ?_
  have heq : (1 / 16 + 39 * π * exp (2 * u) + 166 * π ^ 2 * exp (2 * u) ^ 2
        + 112 * π ^ 3 * exp (2 * u) ^ 3 + 16 * π ^ 4 * exp (2 * u) ^ 4)
        * (16 / (π * exp (2 * u))) ^ 4
      = 4096 / π ^ 4 * (1 / exp (2 * u) ^ 4) + 2555904 / π ^ 3 * (1 / exp (2 * u) ^ 3)
        + 10878976 / π ^ 2 * (1 / exp (2 * u) ^ 2) + 7340032 / π * (1 / exp (2 * u))
        + 1048576 := by
    field_simp
    ring
  rw [heq]
  have hi1 : 1 / exp (2 * u) ≤ 1 := by rw [div_le_one hEpos]; exact hE1
  have hi2 : 1 / exp (2 * u) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hE2
  have hi3 : 1 / exp (2 * u) ^ 3 ≤ 1 := by rw [div_le_one (by positivity)]; exact hE3
  have hi4 : 1 / exp (2 * u) ^ 4 ≤ 1 := by rw [div_le_one (by positivity)]; exact hE4
  nlinarith [mul_le_mul_of_nonneg_left hi4 (show (0 : ℝ) ≤ 4096 / π ^ 4 by positivity),
    mul_le_mul_of_nonneg_left hi3 (show (0 : ℝ) ≤ 2555904 / π ^ 3 by positivity),
    mul_le_mul_of_nonneg_left hi2 (show (0 : ℝ) ≤ 10878976 / π ^ 2 by positivity),
    mul_le_mul_of_nonneg_left hi1 (show (0 : ℝ) ≤ 7340032 / π by positivity)]

end Cvs.Xi.ThetaOcticDominatingSeries
