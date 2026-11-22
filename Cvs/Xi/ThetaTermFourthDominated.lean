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
import Cvs.Xi.ThetaTermFourthDeriv

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The fourth derivative term is dominated

The quartic factor is a quartic in a single nonnegative argument, so the triangle inequality
bounds it by the same quartic with every sign made positive. Separating the powers of the index
carries it to the eighth, one step beyond the sextic that dominates the level below, so the
dominating series here is the octic one.
-/

noncomputable section

open Real

namespace Cvs.Xi.ThetaTermFourthDominated

open Cvs.Xi.RiemannPhiKernel Cvs.Xi.PhiThetaDifferentialOperator Cvs.Xi.PhiKernelIdentitySums Cvs.Xi.ThetaTermFourthDeriv

/-- The quartic factor, in the single argument the index and the exponential enter through. -/
theorem abs_quartic_factor_le {a : ℝ} (ha : 0 ≤ a) :
    |1 / 16 - 39 / 2 * a + 83 / 2 * a ^ 2 - 14 * a ^ 3 + a ^ 4|
      ≤ 1 / 16 + 39 / 2 * a + 83 / 2 * a ^ 2 + 14 * a ^ 3 + a ^ 4 := by
  have h2 : (0 : ℝ) ≤ a ^ 2 := by positivity
  have h3 : (0 : ℝ) ≤ a ^ 3 := by positivity
  have h4 : (0 : ℝ) ≤ a ^ 4 := by positivity
  rw [abs_le]
  constructor <;> nlinarith

theorem sq_le_octic_add_one (n : ℕ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have key : (0 : ℝ) ≤ (n : ℝ) ^ 2
        * (((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 4 + (n : ℝ) ^ 2 + 1)) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith) (by positivity))
    nlinarith [key]

theorem quartic_le_octic_add_one (n : ℕ) : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 8 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have key : (0 : ℝ) ≤ (n : ℝ) ^ 4 * (((n : ℝ) ^ 2 - 1) * ((n : ℝ) ^ 2 + 1)) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith) (by positivity))
    nlinarith [key]

theorem sextic_le_octic_add_one (n : ℕ) : (n : ℝ) ^ 6 ≤ (n : ℝ) ^ 8 + 1 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    have key : (0 : ℝ) ≤ (n : ℝ) ^ 6 * ((n : ℝ) ^ 2 - 1) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith [key]

/-- The series dominating the fourth derivative family. -/
theorem summable_octic_exp {A : ℝ} (hA : 0 < A) :
    Summable (fun n : ℕ => ((n : ℝ) ^ 8 + 1) * exp (-(A * (n : ℝ) ^ 2))) := by
  have h := (summable_pow_mul_exp_neg_sq 8 hA).add (summable_pow_mul_exp_neg_sq 0 hA)
  refine h.congr (fun n => ?_)
  rw [pow_zero]
  ring

/-- The quartic factor at the index, with the powers of the index separated. -/
theorem abs_factor4_le (n : ℕ) (u : ℝ) :
    |1 / 16 - 39 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u))
        + 83 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
        - 14 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
        + (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 4|
      ≤ 1 / 16 + 39 * π * (n : ℝ) ^ 2 * exp (2 * u)
        + 166 * π ^ 2 * (n : ℝ) ^ 4 * exp (2 * u) ^ 2
        + 112 * π ^ 3 * (n : ℝ) ^ 6 * exp (2 * u) ^ 3
        + 16 * π ^ 4 * (n : ℝ) ^ 8 * exp (2 * u) ^ 4 := by
  have ha : (0 : ℝ) ≤ 2 * π * (n : ℝ) ^ 2 * exp (2 * u) := by positivity
  exact (abs_quartic_factor_le ha).trans (le_of_eq (by ring))

/-- The fourth derivative term is bounded by the dominating series. -/
theorem abs_thetaTerm4_le (n : ℕ) (u : ℝ) :
    |thetaTerm4 n u|
      ≤ exp (u / 2) * (1 / 16 + 39 * π * exp (2 * u) + 166 * π ^ 2 * exp (2 * u) ^ 2
          + 112 * π ^ 3 * exp (2 * u) ^ 3 + 16 * π ^ 4 * exp (2 * u) ^ 4)
        * (((n : ℝ) ^ 8 + 1) * exp (-(π * exp (2 * u) * (n : ℝ) ^ 2))) := by
  have hE : (0 : ℝ) < exp (2 * u) := Real.exp_pos _
  have hpi := Real.pi_pos
  have hs2 := sq_le_octic_add_one n
  have hs4 := quartic_le_octic_add_one n
  have hs6 := sextic_le_octic_add_one n
  have h8 : (0 : ℝ) ≤ (n : ℝ) ^ 8 := by positivity
  have hq : (1 : ℝ) ≤ (n : ℝ) ^ 8 + 1 := by linarith
  have hfac : |1 / 16 - 39 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u))
      + 83 / 2 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 2
      - 14 * (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 3
      + (2 * π * (n : ℝ) ^ 2 * exp (2 * u)) ^ 4|
      ≤ (1 / 16 + 39 * π * exp (2 * u) + 166 * π ^ 2 * exp (2 * u) ^ 2
          + 112 * π ^ 3 * exp (2 * u) ^ 3 + 16 * π ^ 4 * exp (2 * u) ^ 4)
        * ((n : ℝ) ^ 8 + 1) := by
    refine (abs_factor4_le n u).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hs2
        (show (0 : ℝ) ≤ 39 * π * exp (2 * u) by positivity),
      mul_le_mul_of_nonneg_left hs4
        (show (0 : ℝ) ≤ 166 * π ^ 2 * exp (2 * u) ^ 2 by positivity),
      mul_le_mul_of_nonneg_left hs6
        (show (0 : ℝ) ≤ 112 * π ^ 3 * exp (2 * u) ^ 3 by positivity),
      mul_le_mul_of_nonneg_left (show (n : ℝ) ^ 8 ≤ (n : ℝ) ^ 8 + 1 by linarith)
        (show (0 : ℝ) ≤ 16 * π ^ 4 * exp (2 * u) ^ 4 by positivity),
      mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ (1 : ℝ) / 16 by norm_num)]
  have h1 : (0 : ℝ) < exp (u / 2) := Real.exp_pos _
  have h2 : (0 : ℝ) < exp (-(π * exp (2 * u) * (n : ℝ) ^ 2)) := Real.exp_pos _
  rw [thetaTerm4_eq_prod, abs_mul, abs_mul, abs_of_pos h1, abs_of_pos h2]
  nlinarith [mul_le_mul_of_nonneg_left hfac (mul_pos h1 h2).le]

/-- The sum of the fourth derivatives of the theta terms. -/
noncomputable def thetaSum4 (u : ℝ) : ℝ := ∑' n : ℕ, thetaTerm4 (n + 1) u

end Cvs.Xi.ThetaTermFourthDominated
