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

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The derivative sums decay too

The derivative terms carry the same doubly exponential factor with a polynomial in `e^{2u}` in
front, and an exponential beats a polynomial: splitting the factor once more pays for the first
derivative's prefactor and twice more for the second's. Both sums then decay at a plain
exponential rate on the half line.
-/

noncomputable section

open Real Filter Topology

namespace Cvs.Xi.ThetaDerivativeSumsDecay


theorem exp_neg_le_inv {y : ℝ} (hy : 0 < y) : exp (-y) ≤ 1 / y := by
  have h : y ≤ exp y := by linarith [Real.add_one_le_exp y]
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hy h

/-- **A quarter of the factor pays the first derivative's prefactor.** -/
theorem prefactor_one_le {u : ℝ} (hu : 0 ≤ u) :
    (1 / 2 + 2 * π * exp (2 * u)) * exp (-(π / 4 * exp (2 * u))) ≤ 2 / π + 8 := by
  have hpi := Real.pi_pos
  have hE1 : (1 : ℝ) ≤ exp (2 * u) := Real.one_le_exp (by linarith)
  have hEpos : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hy : (0 : ℝ) < π / 4 * exp (2 * u) := by positivity
  have hinv : exp (-(π / 4 * exp (2 * u))) ≤ 4 / (π * exp (2 * u)) := by
    refine (exp_neg_le_inv hy).trans (le_of_eq ?_)
    field_simp
  have hfac : (0 : ℝ) ≤ 1 / 2 + 2 * π * exp (2 * u) := by positivity
  have hstep : (1 / 2 + 2 * π * exp (2 * u)) * exp (-(π / 4 * exp (2 * u)))
      ≤ (1 / 2 + 2 * π * exp (2 * u)) * (4 / (π * exp (2 * u))) :=
    mul_le_mul_of_nonneg_left hinv hfac
  refine hstep.trans ?_
  have heq : (1 / 2 + 2 * π * exp (2 * u)) * (4 / (π * exp (2 * u)))
      = 2 / (π * exp (2 * u)) + 8 := by field_simp; ring
  rw [heq]
  have hle : 2 / (π * exp (2 * u)) ≤ 2 / π := by
    have hpe : π ≤ π * exp (2 * u) := le_mul_of_one_le_right hpi.le hE1
    gcongr
  linarith

/-- **Half of the factor pays the second derivative's prefactor.** -/
theorem prefactor_two_le {u : ℝ} (hu : 0 ≤ u) :
    (1 / 4 + 6 * π * exp (2 * u) + 4 * π ^ 2 * exp (2 * u) ^ 2)
        * exp (-(π / 4 * exp (2 * u)))
      ≤ 16 / π ^ 2 + 384 / π + 256 := by
  have hpi := Real.pi_pos
  have hE1 : (1 : ℝ) ≤ exp (2 * u) := Real.one_le_exp (by linarith)
  have hEpos : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hy : (0 : ℝ) < π / 8 * exp (2 * u) := by positivity
  have hhalf : exp (-(π / 8 * exp (2 * u))) ≤ 8 / (π * exp (2 * u)) := by
    refine (exp_neg_le_inv hy).trans (le_of_eq ?_)
    field_simp
  have hsq : exp (-(π / 4 * exp (2 * u))) ≤ (8 / (π * exp (2 * u))) ^ 2 := by
    have hdouble : exp (-(π / 4 * exp (2 * u)))
        = exp (-(π / 8 * exp (2 * u))) * exp (-(π / 8 * exp (2 * u))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hdouble, sq]
    exact mul_le_mul hhalf hhalf (Real.exp_pos _).le (by positivity)
  have hfac : (0 : ℝ) ≤ 1 / 4 + 6 * π * exp (2 * u) + 4 * π ^ 2 * exp (2 * u) ^ 2 := by
    positivity
  refine (mul_le_mul_of_nonneg_left hsq hfac).trans ?_
  have heq : (1 / 4 + 6 * π * exp (2 * u) + 4 * π ^ 2 * exp (2 * u) ^ 2)
      * (8 / (π * exp (2 * u))) ^ 2
      = 16 / (π ^ 2 * exp (2 * u) ^ 2) + 384 / (π * exp (2 * u)) + 256 := by
    field_simp; ring
  rw [heq]
  have hE2 : (1 : ℝ) ≤ exp (2 * u) ^ 2 := by nlinarith [hE1, hEpos]
  have h1 : 16 / (π ^ 2 * exp (2 * u) ^ 2) ≤ 16 / π ^ 2 := by
    have : π ^ 2 ≤ π ^ 2 * exp (2 * u) ^ 2 := le_mul_of_one_le_right (by positivity) hE2
    gcongr
  have h2 : 384 / (π * exp (2 * u)) ≤ 384 / π := by
    have : π ≤ π * exp (2 * u) := le_mul_of_one_le_right hpi.le hE1
    gcongr
  linarith

end Cvs.Xi.ThetaDerivativeSumsDecay
